//! SDDISPATCH encoding plans over one exclusively borrowed APDU payload.
//! Plans retain offsets and small header fields, never references to bytes that
//! the encoder will mutate. Each input segment moves directly to its final slot.
#![forbid(unsafe_code)]

#[derive(Clone, Copy, Default)]
struct Segment {
    source: u16,
    destination: u16,
    len: u16,
}

pub(crate) struct InPlaceRequest {
    prefix: [u8; 11],
    prefix_len: u8,
    segments: [Segment; 3],
    count: u8,
    length_values: bool,
    len: u16,
}

impl InPlaceRequest {
    pub(crate) fn new(
        input: &[u8],
        prefix: &[u8],
        parts: &[&[u8]],
        length_values: bool,
    ) -> Option<Self> {
        if prefix.len() > 11 || parts.len() > 3 {
            return None;
        }
        let mut plan = Self {
            prefix: [0; 11],
            prefix_len: prefix.len() as u8,
            segments: [Segment::default(); 3],
            count: parts.len() as u8,
            length_values,
            len: 0,
        };
        plan.prefix[..prefix.len()].copy_from_slice(prefix);
        let mut end = prefix.len();
        for (segment, part) in plan.segments.iter_mut().zip(parts) {
            let source = if part.is_empty() {
                0
            } else {
                (part.as_ptr() as usize).checked_sub(input.as_ptr() as usize)?
            };
            if source.checked_add(part.len())? > input.len() || (length_values && part.len() > 255)
            {
                return None;
            }
            end += usize::from(length_values);
            *segment = Segment {
                source: u16::try_from(source).ok()?,
                destination: u16::try_from(end).ok()?,
                len: u16::try_from(part.len()).ok()?,
            };
            end = end.checked_add(part.len())?;
        }
        if end > rustlet_runtime::APDU_PAYLOAD_LENGTH_MAX {
            return None;
        }
        plan.len = end as u16;
        Some(plan)
    }

    pub(crate) fn encode(self, out: &mut [u8]) -> Option<usize> {
        let parts = &self.segments[..self.count as usize];
        if self.len as usize > out.len()
            || parts
                .iter()
                .any(|s| s.source as usize + s.len as usize > out.len())
        {
            return None;
        }
        // Determine a dependency order before modifying anything: a move must
        // not overwrite another segment's still-live source. No scratch copy.
        let mut pending = (1u8 << self.count) - 1;
        let mut order = [0u8; 3];
        for next in order.iter_mut().take(parts.len()) {
            let index = (0..parts.len()).find(|&i| {
                pending & (1 << i) != 0
                    && (0..parts.len()).all(|j| {
                        i == j
                            || pending & (1 << j) == 0
                            || !overlap(
                                parts[i].destination,
                                parts[i].len,
                                parts[j].source,
                                parts[j].len,
                            )
                    })
            });
            let Some(index) = index else {
                self.encode_cycles(out);
                return Some(self.len as usize);
            };
            *next = index as u8;
            pending &= !(1 << index);
        }
        for &index in order.iter().take(parts.len()) {
            let s = parts[index as usize];
            let source = s.source as usize;
            let destination = s.destination as usize;
            if source != destination && s.len != 0 {
                out.copy_within(source..source + s.len as usize, destination);
            }
        }
        self.write_prefixes(out);
        Some(self.len as usize)
    }

    fn write_prefixes(&self, out: &mut [u8]) {
        out[..self.prefix_len as usize].copy_from_slice(&self.prefix[..self.prefix_len as usize]);
        if self.length_values {
            for s in &self.segments[..self.count as usize] {
                out[s.destination as usize - 1] = s.len as u8;
            }
        }
    }

    /// A certificate may reorder fields cyclically (public key before subject).
    /// Track only pending destinations, not their contents. Drain destinations
    /// whose old byte is no longer needed, then rotate each remaining cycle
    /// using one byte. Every final payload byte is written once.
    #[inline(never)]
    fn encode_cycles(&self, out: &mut [u8]) {
        let parts = &self.segments[..self.count as usize];
        let mut pending = [0u32; 8];
        for s in parts {
            for index in s.destination..s.destination + s.len {
                set_pending(&mut pending, index as usize, true);
            }
        }
        while let Some(first) = (0..self.len as usize).find(|&i| is_pending(&pending, i)) {
            let ready = (first..self.len as usize).find(|&i| {
                is_pending(&pending, i)
                    && !parts.iter().any(|s| {
                        i >= s.source as usize
                            && i < s.source as usize + s.len as usize
                            && is_pending(&pending, s.destination as usize + i - s.source as usize)
                    })
            });
            if let Some(destination) = ready {
                let source = self.source_for(destination);
                out[destination] = out[source];
                set_pending(&mut pending, destination, false);
            } else {
                // With no drainable node, remaining dependencies are cycles:
                // each pending destination has exactly one pending consumer.
                let saved = out[first];
                let mut destination = first;
                loop {
                    let source = self.source_for(destination);
                    out[destination] = if source == first { saved } else { out[source] };
                    set_pending(&mut pending, destination, false);
                    if source == first {
                        break;
                    }
                    destination = source;
                }
            }
        }
        self.write_prefixes(out);
    }

    fn source_for(&self, destination: usize) -> usize {
        let s = self.segments[..self.count as usize]
            .iter()
            .find(|s| {
                destination >= s.destination as usize
                    && destination < s.destination as usize + s.len as usize
            })
            .expect("pending destination belongs to an encoded segment");
        s.source as usize + destination - s.destination as usize
    }
}

fn is_pending(bits: &[u32; 8], index: usize) -> bool {
    bits[index / 32] & (1 << (index % 32)) != 0
}
fn set_pending(bits: &mut [u32; 8], index: usize, pending: bool) {
    let mask = 1 << (index % 32);
    if pending {
        bits[index / 32] |= mask;
    } else {
        bits[index / 32] &= !mask;
    }
}

fn overlap(a: u16, a_len: u16, b: u16, b_len: u16) -> bool {
    a_len != 0
        && b_len != 0
        && (a as usize) < b as usize + b_len as usize
        && (b as usize) < a as usize + a_len as usize
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expands_a_resident_command_without_overwriting_its_input() {
        let mut buffer = [0u8; 256];
        buffer[..8].copy_from_slice(b"payload!");
        let plan = InPlaceRequest::new(&buffer, &[1, 2, 3, 4, 5], &[&buffer[..8]], false).unwrap();
        assert_eq!(plan.encode(&mut buffer), Some(13));
        assert_eq!(&buffer[..13], b"\x01\x02\x03\x04\x05payload!");
    }

    #[test]
    fn compacts_tlv_fields_and_duplicates_authenticated_data_safely() {
        let mut buffer = [0u8; 256];
        buffer[8..12].copy_from_slice(b"host");
        buffer[18..24].copy_from_slice(b"public");
        let plan = InPlaceRequest::new(&buffer, &[1, 2], &[&buffer[8..12], &buffer[18..24]], true)
            .unwrap();
        assert_eq!(plan.encode(&mut buffer), Some(14));
        assert_eq!(&buffer[..14], b"\x01\x02\x04host\x06public");
        buffer[..8].copy_from_slice(b"dataMAC!");
        let plan = InPlaceRequest::new(
            &buffer,
            &[0; 11],
            &[&buffer[..4], &buffer[..4], &buffer[4..8]],
            false,
        )
        .unwrap();
        assert_eq!(plan.encode(&mut buffer), Some(23));
        assert_eq!(&buffer[11..23], b"datadataMAC!");
    }

    #[test]
    fn invalid_plans_leave_the_payload_untouched() {
        let mut buffer = *b"abcdefgh";
        let external = [0xA5; 4];
        assert!(InPlaceRequest::new(&buffer, &[], &[&external], false).is_none());
        let plan = InPlaceRequest::new(&buffer, &[0; 6], &[&buffer], false).unwrap();
        assert_eq!(plan.encode(&mut buffer), None);
        assert_eq!(&buffer, b"abcdefgh");
        // Cyclic field reordering needs only a one-byte temporary.
        let plan =
            InPlaceRequest::new(&buffer, &[], &[&buffer[4..8], &buffer[..4]], false).unwrap();
        assert_eq!(plan.encode(&mut buffer), Some(8));
        assert_eq!(&buffer, b"efghabcd");
    }

    #[test]
    fn overlapping_and_reordered_fields_match_external_encoding() {
        for first in 0..8 {
            for second in 0..8 {
                for third in 0..8 {
                    for length in 0..=4 {
                        let mut buffer = core::array::from_fn::<_, 32, _>(|i| i as u8);
                        let source = buffer;
                        let parts = [
                            &buffer[first..first + length],
                            &buffer[second..second + length],
                            &buffer[third..third + length],
                        ];
                        let plan =
                            InPlaceRequest::new(&buffer, &[0xA5, 0x5A], &parts, true).unwrap();
                        let mut expected = std::vec![0xA5, 0x5A];
                        for start in [first, second, third] {
                            expected.push(length as u8);
                            expected.extend_from_slice(&source[start..start + length]);
                        }
                        let end = plan.encode(&mut buffer).unwrap();
                        assert_eq!(
                            &buffer[..end],
                            expected,
                            "sources {first}, {second}, {third}; length {length}"
                        );
                    }
                }
            }
        }
    }
}
