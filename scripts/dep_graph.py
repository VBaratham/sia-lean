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
    # FTC theorems are end results
    "ftc1", "ftc2", "integral_well_defined",
    "same_deriv_differ_by_const", "eq_of_same_deriv_and_initial",
    "integration_by_parts", "product_has_slope",
    # Continuity results
    "all_continuous", "neighbors_not_transitive",
    "neighbors_refl", "neighbors_symm",
    # Delta results about LEM
    "not_lem_on_delta",
    # Higher-order results
    "delta_k_zero_mem", "delta_k_one_eq_delta", "delta_k_neg",
    "taylor_degree2", "delta_2_cube_zero",
    # Order results (mathematically important even if not used downstream)
    "le_le_eq_nn",
    # Derivative end results (slope rules and uniqueness)
    "deriv_const_slope", "deriv_id_slope", "deriv_neg_slope",
    "deriv_const_mul_slope",
    "deriv_add_eq", "deriv_mul_eq", "deriv_comp_eq",
    # Integration end results (linearity, etc.)
    "antideriv_add_eq", "antideriv_const_mul", "antideriv_neg",
    "antideriv_sub", "integral_additive",
    "const_antideriv_slope", "antideriv_microaffine", "antideriv_slope_eq",
}

# Symmetric counterparts — one side is used, the other is a library lemma
SYMMETRIC = {
    "add_neg_cancel_left": "neg_add_cancel_left is used",
    "add_right_cancel": "add_left_cancel is used",
    "add_sub_cancel": "sub_add_cancel is used",
    "le_add_right_of": "le_add_left_of is used",
    "le_neg_flip": "lt_neg_flip is used",
    "div_mul_cancel": "mul_div_cancel counterpart",
    "le_of_lt": "standard library lemma",
    "le_of_eq": "standard library lemma",
}

# Pattern matching declarations
DECL_RE = re.compile(
    r'^(?:theorem|def|instance|class|noncomputable\s+def)\s+(\w+)',
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
        lines = text.split('\n')
        for i, line in enumerate(lines):
            if f == declaring_file and re.match(
                rf'^(?:theorem|def|instance|class|noncomputable\s+def)\s+{re.escape(name)}\b',
                line,
            ):
                continue
            stripped = line.split('--')[0]
            if re.search(rf'\b{re.escape(name)}\b', stripped):
                refs.append((f.name, i + 1, line.strip()))
    return refs


def build_graph(files):
    """Build declaration list and find unused ones."""
    all_decls = {}
    for f in files:
        for name in extract_declarations(f):
            all_decls[name] = f

    extras = list(EXTRAS_DIR.glob("*.lean")) if EXTRAS_DIR.exists() else []
    all_files = files + extras

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

    truly_unused = []
    terminal = []
    symmetric = []

    for name, f in unused:
        if name in TERMINAL:
            terminal.append((name, f))
        elif name in SYMMETRIC:
            symmetric.append((name, f, SYMMETRIC[name]))
        else:
            truly_unused.append((name, f))

    print(f"\nTotal declarations: {len(all_decls)}")
    print(f"Used downstream: {len(all_decls) - len(unused)}")
    print(f"Terminal results: {len(terminal)}")
    print(f"Symmetric counterparts: {len(symmetric)}")
    print(f"Potentially dead: {len(truly_unused)}")

    if truly_unused:
        print("\n" + "=" * 70)
        print("POTENTIALLY DEAD (not used, not terminal, not symmetric)")
        print("=" * 70)
        for name, f in truly_unused:
            print(f"  {f.name}: {name}")

    if symmetric:
        print("\n" + "=" * 70)
        print("SYMMETRIC / LIBRARY LEMMAS (one side used, other not)")
        print("=" * 70)
        for name, f, note in symmetric:
            print(f"  {f.name}: {name}  ({note})")

    if terminal:
        print("\n" + "=" * 70)
        print("TERMINAL RESULTS (end goals)")
        print("=" * 70)
        for name, f in terminal:
            print(f"  {f.name}: {name}")

    # Print full dependency tree
    print("\n" + "=" * 70)
    print("FULL DEPENDENCY MAP")
    print("=" * 70)
    for f in FILES:
        decls = extract_declarations(f)
        if not decls:
            continue
        print(f"\n--- {f.name} ---")
        for name in decls:
            refs = used_by.get(name, [])
            if name in TERMINAL:
                status = " [TERMINAL]"
            elif name in SYMMETRIC:
                status = " [SYMMETRIC]"
            elif not refs:
                status = " [DEAD?]"
            else:
                unique_refs = sorted(set(refs))
                status = f" -> {', '.join(unique_refs)}"
            print(f"  {name}{status}")


if __name__ == "__main__":
    main()
