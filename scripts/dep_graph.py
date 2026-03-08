#!/usr/bin/env python3
"""
Build a dependency graph of theorems/defs in the SIA project.
Reports: (1) unused theorems, (2) full dependency tree.

This is a text-based analysis — it finds declarations and checks if their
names appear elsewhere. Not perfect (no semantic analysis), but catches
obvious dead weight.
"""

import re
import os
import sys
from collections import defaultdict
from pathlib import Path

SIA_DIR = Path(__file__).parent.parent / "SIA"
EXTRAS_DIR = Path(__file__).parent.parent / "extras"

# Files to analyze (in dependency order)
FILES = [
    SIA_DIR / "Algebra.lean",
    SIA_DIR / "Order.lean",
    SIA_DIR / "Field.lean",
    SIA_DIR / "Axioms.lean",
    SIA_DIR / "Delta.lean",
    SIA_DIR / "Continuity.lean",
    SIA_DIR / "Derivative.lean",
    SIA_DIR / "HigherOrder.lean",
    SIA_DIR / "Integration.lean",
    SIA_DIR / "FTC.lean",
]

# Declarations that are "terminal" — end results, not expected to be used elsewhere
TERMINAL = {
    # CheckAxioms just prints axioms
    # FTC theorems are end results
    "ftc1", "ftc2", "integral_well_defined",
    "same_deriv_differ_by_const", "eq_of_same_deriv_and_initial",
    "integration_by_parts", "product_has_slope",
    # Continuity results
    "all_continuous", "neighbors_not_transitive",
    # Delta results about LEM
    "not_lem_on_delta",
    # Higher-order results
    "delta_k_zero_mem", "delta_k_one_eq_delta", "delta_k_neg",
    "taylor_degree2", "delta_2_cube_zero",
    # Simp-tagged lemmas (used by the simplifier, not directly)
    # CheckAxioms declarations
}

# Pattern matching declarations
DECL_RE = re.compile(
    r'^(?:theorem|def|instance|class|noncomputable\s+def)\s+(\w+)',
    re.MULTILINE,
)

# Also match class field declarations (inside class bodies)
CLASS_FIELD_RE = re.compile(
    r'^\s+(\w+)\s*:\s',
    re.MULTILINE,
)


def extract_declarations(filepath):
    """Extract all theorem/def names from a file."""
    text = filepath.read_text()
    decls = []

    for m in DECL_RE.finditer(text):
        name = m.group(1)
        decls.append(name)

    return decls


def find_references(name, files, declaring_file):
    """Find files that reference a name (excluding its own declaration)."""
    refs = []
    for f in files:
        text = f.read_text()
        # Look for the name as a word boundary match
        # Exclude the declaration line itself
        lines = text.split('\n')
        for i, line in enumerate(lines):
            # Skip the declaration line
            if f == declaring_file and re.match(
                rf'^(?:theorem|def|instance|class|noncomputable\s+def)\s+{re.escape(name)}\b',
                line,
            ):
                continue
            # Skip comments
            stripped = line.split('--')[0]
            if re.search(rf'\b{re.escape(name)}\b', stripped):
                refs.append((f.name, i + 1, line.strip()))
    return refs


def build_graph(files):
    """Build declaration list and find unused ones."""
    all_decls = {}  # name -> declaring file

    for f in files:
        for name in extract_declarations(f):
            all_decls[name] = f

    # Also scan extras
    extras = list(EXTRAS_DIR.glob("*.lean")) if EXTRAS_DIR.exists() else []
    all_files = files + extras

    # For each declaration, find if it's referenced
    unused = []
    used_by = defaultdict(list)

    for name, declaring_file in sorted(all_decls.items()):
        refs = find_references(name, all_files, declaring_file)
        if not refs:
            unused.append((name, declaring_file))
        else:
            for ref_file, line, text in refs:
                used_by[name].append(ref_file)

    return all_decls, unused, used_by


def main():
    all_decls, unused, used_by = build_graph(FILES)

    print("=" * 70)
    print("DEPENDENCY ANALYSIS — SIA Project")
    print("=" * 70)

    # Report unused
    truly_unused = [(n, f) for n, f in unused if n not in TERMINAL]
    terminal_unused = [(n, f) for n, f in unused if n in TERMINAL]

    print(f"\nTotal declarations found: {len(all_decls)}")
    print(f"Used by other declarations: {len(all_decls) - len(unused)}")
    print(f"Terminal (end results): {len(terminal_unused)}")
    print(f"Potentially unused: {len(truly_unused)}")

    if truly_unused:
        print("\n" + "-" * 70)
        print("POTENTIALLY UNUSED (not referenced anywhere, not marked terminal):")
        print("-" * 70)
        for name, f in truly_unused:
            print(f"  {f.name}: {name}")

    if terminal_unused:
        print("\n" + "-" * 70)
        print("TERMINAL RESULTS (end goals, not expected to be used):")
        print("-" * 70)
        for name, f in terminal_unused:
            print(f"  {f.name}: {name}")

    # Print dependency info for each file
    print("\n" + "=" * 70)
    print("DECLARATIONS BY FILE")
    print("=" * 70)
    for f in FILES:
        decls = extract_declarations(f)
        if not decls:
            continue
        print(f"\n--- {f.name} ---")
        for name in decls:
            refs = used_by.get(name, [])
            status = ""
            if name in TERMINAL:
                status = " [TERMINAL]"
            elif not refs:
                status = " [UNUSED?]"
            else:
                # Deduplicate
                unique_refs = sorted(set(refs))
                status = f" -> {', '.join(unique_refs)}"
            print(f"  {name}{status}")


if __name__ == "__main__":
    main()
