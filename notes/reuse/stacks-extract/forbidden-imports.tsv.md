# `forbidden-imports.tsv`

This page holds the table `forbidden-imports.tsv` as it is, in the code block below. To use it, save the content of the block under that name.

```text
# Mathlib modules that no module of the extract may have in its import closure: module<TAB>why.
# Each declares a name that weil-conjectures also declares (operator note 1, 22 November 2026);
# no module of Mathlib imports them, so they enter only through `import Mathlib` or by name.
Mathlib.CategoryTheory.GuitartExact.Prod	declares CategoryTheory.TwoSquare.GuitartExact.prod, also declared by WeilConjectures.FromJoel.CategoryTheory.GuitartExact.Basic
Mathlib.RingTheory.Depth.Basic	declares Ideal.depth and IsLocalRing.depth, also declared by WeilConjectures.RingTheory.Depth
Mathlib.RepresentationTheory.Stabilizer	declares Representation.stabilizer, also declared by WeilConjectures.RepresentationTheory.GeometricConstituents
```
