#!/usr/bin/env python3
"""Package a devkit ELF as UF2, resetting the board's entire persistent flash.

Uses Raspberry Pi picotool 2.2.0 (or a compatible version). The generated UF2
contains every page of flash, including erased bytes outside ELF load segments.
This is an installation image, not an update preserving application data.
"""
import argparse
import pathlib
import struct
import subprocess
import tempfile


def flash_image(elf, size):
    data = elf.read_bytes()
    if data[:7] != b'\x7fELF\x01\x01\x01':
        raise ValueError('Expected a little-endian ELF32 image')
    header = struct.unpack_from('<16sHHIIIIIHHHHHH', data)
    if header[2] != 40:
        raise ValueError('Expected an ARM ELF')
    image = bytearray(b'\xff' * size)
    occupied = bytearray(size)
    for index in range(header[10]):
        kind, offset, _, address, length, _, _, _ = struct.unpack_from(
            '<8I', data, header[5] + index * header[9])
        if kind != 1 or length == 0:
            continue
        start = address - 0x10000000
        if start < 0 or start + length > size or offset + length > len(data):
            raise ValueError('ELF load segment outside declared flash or file')
        if any(occupied[start:start + length]):
            raise ValueError('Overlapping ELF load segments')
        image[start:start + length] = data[offset:offset + length]
        occupied[start:start + length] = b'\x01' * length
    if not occupied[0]:
        raise ValueError('Missing flash boot image')
    return image


def verify_uf2(path, expected, family):
    raw = path.read_bytes()
    # picotool's leading RP2350-E10 workaround block is tagged IGNORE_BLOCK.
    if family == 0xE48BFF59:
        workaround = bytearray(512)
        struct.pack_into('<8I', workaround, 0, 0x0A324655, 0x9E5D5157,
                         0xA000, 0x103FFF00, 256, 0, 2, 0xE48BFF57)
        workaround[32:288] = b'\xef' * 256
        struct.pack_into('<I', workaround, 288, 0x9957E304)
        struct.pack_into('<I', workaround, 508, 0x0AB16F30)
        if raw[:512] != workaround:
            raise ValueError('Invalid RP2350-E10 workaround block')
        raw = raw[512:]
    count = len(expected) // 256
    if len(raw) != count * 512:
        raise ValueError('Unexpected UF2 size')
    for index in range(count):
        block = raw[index * 512:(index + 1) * 512]
        a, b, flags, address, length, number, total, device = struct.unpack_from('<8I', block)
        if (a, b, flags, address, length, number, total, device) != (
            0x0A324655, 0x9E5D5157, 0x2000, 0x10000000 + index * 256,
            256, index, count, family):
            raise ValueError(f'Invalid UF2 block {index}')
        if struct.unpack_from('<I', block, 508)[0] != 0x0AB16F30:
            raise ValueError('Invalid UF2 end marker')
        if block[32:288] != expected[index * 256:(index + 1) * 256]:
            raise ValueError(f'UF2 payload differs from flash image at block {index}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('board', choices=['pico1', 'pico2'])
    parser.add_argument('elf', type=pathlib.Path)
    parser.add_argument('output', type=pathlib.Path)
    parser.add_argument('--picotool', default='picotool')
    args = parser.parse_args()
    size, family = {'pico1': (0x200000, 0xE48BFF56),
                    'pico2': (0x400000, 0xE48BFF59)}[args.board]
    image = flash_image(args.elf, size)
    with tempfile.TemporaryDirectory(prefix='oxide-devkit-uf2-') as directory:
        binary = pathlib.Path(directory) / 'flash.bin'
        binary.write_bytes(image)
        workaround = ['--abs-block', '0x103fff00'] if args.board == 'pico2' else []
        subprocess.run([args.picotool, 'uf2', 'convert', str(binary), str(args.output),
                        '--family', hex(family), '--offset', '0x10000000'] + workaround, check=True)
    verify_uf2(args.output, image, family)
    print(f'Verified {args.output}: {size} flash bytes, family {family:#x}')


if __name__ == '__main__':
    main()
