#!/usr/bin/env python3
"""Check the registry's global-state and physical-backend dependency boundary.

The canonical registry owns the only resident object-reference table.
Other flash diagnostics reserve separate tails before registry initialization;
this check deliberately covers registry code and its selected_app adapter.
"""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
src = root / "kernel/firmware/src"
registry = src / "registry"
errors = []
for path in src.rglob("*.rs"):
    text = path.read_text()
    inside = path.is_relative_to(registry)
    if not inside and re.search(r"\bOBJECT_REGISTRY\b", text):
        errors.append(f"{path.relative_to(root)}: direct global registry access")
    if inside and path.name != "physical.rs" and re.search(r"core::(?:ptr::read_volatile|slice::from_raw_parts)", text):
        errors.append(f"{path.relative_to(root)}: direct mapped flash read")
    if (inside and path.name != "physical.rs") or path.name == "selected_app.rs":
        if re.search(r"(?:core|target)::(?:flash\b|flash_persistence_area\b)", text):
            errors.append(f"{path.relative_to(root)}: bypasses registry physical boundary")

for error in errors:
    print(error, file=sys.stderr)
if errors:
    sys.exit(1)
print("Registry boundary: global state confined; physical backend access centralized.")
