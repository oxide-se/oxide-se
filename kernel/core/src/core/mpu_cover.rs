#![forbid(unsafe_code)]
//! Exact executable-window coverage for PMSAv6/v7 subregions and PMSAv8 limits.
//! Overlapping nominal regions have identical permissions. Every enabled
//! subregion belongs to the requested window; disabled portions grant nothing.
use super::target::MpuAlignmentModel;

/// Minimum package placement and accessible-window granule, in bytes.
pub const GRANULE: usize = 256;
/// Application code slots; the shared gate and application RAM have other slots.
pub const CODE_REGIONS: usize = 5;

/// Additional reserved flash, beyond the page-rounded package block.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MpuPadding {
    /// Erased bytes before the package, excluded from its MPU window.
    pub before: usize,
    /// Erased bytes appended inside the package's MPU window.
    pub after: usize,
}

/// Invalid geometry, unsupported hardware, or exhausted code-region budget.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MpuCoverError {
    InvalidWindow,
    Unsupported,
    RegionBudgetExceeded,
}

/// One nominal region and its disabled-subregion mask.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CoverRegion {
    pub base: usize,
    pub size: usize,
    /// RASR SRD bits; zero for a PMSAv8 base/limit region.
    pub disabled_subregions: u8,
}

/// Allocation-free iterator over a minimum-cardinality exact cover.
pub struct Cover {
    start: usize,
    end: usize,
    cursor: usize,
    model: MpuAlignmentModel,
}

impl Cover {
    /// Validates a nonempty, page-aligned window without rounding its bounds.
    pub fn new(
        address: usize,
        size: usize,
        model: MpuAlignmentModel,
    ) -> Result<Self, MpuCoverError> {
        if model == MpuAlignmentModel::Unsupported {
            return Err(MpuCoverError::Unsupported);
        }
        let end = address
            .checked_add(size)
            .ok_or(MpuCoverError::InvalidWindow)?;
        if size == 0 || !address.is_multiple_of(GRANULE) || !size.is_multiple_of(GRANULE) {
            return Err(MpuCoverError::InvalidWindow);
        }
        Ok(Self {
            start: address,
            end,
            cursor: address,
            model,
        })
    }
}

impl Iterator for Cover {
    type Item = CoverRegion;
    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor == self.end {
            return None;
        }
        if self.model == MpuAlignmentModel::Relaxed32Byte {
            self.cursor = self.end;
            return Some(CoverRegion {
                base: self.start,
                size: self.end - self.start,
                disabled_subregions: 0,
            });
        }
        let mut size = 8 * GRANULE;
        let mut best_end = self.cursor;
        let mut best = None;
        // Each usable region has at least one subregion inside the window.
        while size / 8 <= self.end - self.start {
            let granule = size / 8;
            let base = self.cursor & !(size - 1);
            let lo = self.start.max(base);
            let first = (lo - base).div_ceil(granule);
            let last = ((self.end - base) / granule).min(8);
            let enabled_start = base + first * granule;
            let enabled_end = base + last * granule;
            if enabled_start <= self.cursor && enabled_end > best_end {
                let enabled = ((1u16 << last) - 1) & !((1u16 << first) - 1);
                best = Some(CoverRegion {
                    base,
                    size,
                    disabled_subregions: !(enabled as u8),
                });
                best_end = enabled_end;
            }
            let Some(next) = size.checked_mul(2) else {
                break;
            };
            size = next;
        }
        // A 2-KiB region always covers at least the next 256-byte page.
        self.cursor = best_end;
        best
    }
}

/// Chooses the least additional storage that fits the target's five code slots.
/// Both inputs describe the complete page-rounded owning block, including its
/// header and trailer. The prefix shifts that block; the suffix extends it.
/// Ties prefer a suffix. No flash is read, written or allocated by this query.
pub fn mpu_cover_require_padding_for(
    address: usize,
    size: usize,
) -> Result<MpuPadding, MpuCoverError> {
    padding_for(address, size, super::target::mpu_region_policy().model)
}

fn padding_for(
    address: usize,
    size: usize,
    model: MpuAlignmentModel,
) -> Result<MpuPadding, MpuCoverError> {
    Cover::new(address, size, model)?;
    for (before, after) in [(0, 0), (0, GRANULE), (GRANULE, 0), (GRANULE, GRANULE)] {
        let Some(start) = address.checked_add(before) else {
            continue;
        };
        let Some(len) = size.checked_add(after) else {
            continue;
        };
        if let Ok(cover) = Cover::new(start, len, model) {
            if cover.take(CODE_REGIONS + 1).count() <= CODE_REGIONS {
                return Ok(MpuPadding { before, after });
            }
        }
    }
    Err(MpuCoverError::RegionBudgetExceeded)
}

#[cfg(test)]
mod tests {
    use super::*;
    const STRICT: MpuAlignmentModel = MpuAlignmentModel::StrictPowerOfTwo;

    fn verify_union(start: usize, len: usize, cover: &[CoverRegion]) {
        for region in cover {
            assert_eq!(region.base % region.size, 0);
            for sub in 0..8 {
                if region.disabled_subregions & (1 << sub) == 0 {
                    let lo = region.base + sub * (region.size / 8);
                    assert!(lo >= start && lo + region.size / 8 <= start + len);
                }
            }
        }
        for page in (start..start + len).step_by(GRANULE) {
            assert!(cover.iter().any(|r| page >= r.base
                && page < r.base + r.size
                && r.disabled_subregions & (1 << ((page - r.base) / (r.size / 8))) == 0));
        }
    }

    #[test]
    fn overlapping_middle_regions_cover_only_owned_pages() {
        for (start, len) in [
            (0x1001_0700, 50 * 256),
            (0x1000_1900, 2560),
            (0x1003_6e00, 290 * 256),
        ] {
            let regions: std::vec::Vec<_> = Cover::new(start, len, STRICT).unwrap().collect();
            verify_union(start, len, &regions);
            assert!(regions.len() <= 5);
        }
    }

    #[test]
    fn padding_is_minimal_and_guarantees_every_length_through_74240_bytes() {
        for pages in 1usize..=290 {
            let period = 1usize << ((8 * (pages + 1)).ilog2());
            for page in 0..period {
                let start = page * GRANULE;
                let len = pages * GRANULE;
                let padding = padding_for(start, len, STRICT).unwrap();
                assert!(
                    Cover::new(start + padding.before, len + padding.after, STRICT)
                        .unwrap()
                        .count()
                        <= CODE_REGIONS
                );
                for (before, after) in [(0, 0), (0, 256), (256, 0), (256, 256)] {
                    if before + after < padding.before + padding.after {
                        assert!(
                            Cover::new(start + before, len + after, STRICT)
                                .unwrap()
                                .count()
                                > CODE_REGIONS
                        );
                    }
                }
            }
        }
        assert_eq!(
            padding_for(0x36e00, 291 * 256, STRICT),
            Err(MpuCoverError::RegionBudgetExceeded)
        );
    }

    #[test]
    fn suffix_prefix_and_combined_padding_are_selected_only_when_needed() {
        for (start, len, before, after) in [(439, 146, 0, 1), (439, 218, 1, 0), (878, 292, 1, 1)] {
            let padding = padding_for(start * GRANULE, len * GRANULE, STRICT).unwrap();
            assert_eq!(
                padding,
                MpuPadding {
                    before: before * GRANULE,
                    after: after * GRANULE
                }
            );
            let regions: std::vec::Vec<_> =
                Cover::new((start + before) * GRANULE, (len + after) * GRANULE, STRICT)
                    .unwrap()
                    .collect();
            verify_union(
                (start + before) * GRANULE,
                (len + after) * GRANULE,
                &regions,
            );
        }
    }

    #[test]
    fn relaxed_profile_needs_one_region_without_padding() {
        let model = MpuAlignmentModel::Relaxed32Byte;
        assert_eq!(
            padding_for(0x1003_6e00, 291 * 256, model),
            Ok(MpuPadding::default())
        );
        let regions: std::vec::Vec<_> =
            Cover::new(0x1003_6e00, 291 * 256, model).unwrap().collect();
        assert_eq!(
            regions,
            [CoverRegion {
                base: 0x1003_6e00,
                size: 291 * 256,
                disabled_subregions: 0
            }]
        );
    }

    #[test]
    fn malformed_and_unsupported_windows_fail_closed() {
        for (start, len) in [(0, 0), (1, 256), (256, 257), (usize::MAX - 255, 256)] {
            assert!(matches!(
                Cover::new(start, len, STRICT),
                Err(MpuCoverError::InvalidWindow)
            ));
        }
        assert_eq!(
            padding_for(256, 256, MpuAlignmentModel::Unsupported),
            Err(MpuCoverError::Unsupported)
        );
    }
}
