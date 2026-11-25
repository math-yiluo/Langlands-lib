# `STX-RENAMES.tsv`

This page holds the table `STX-RENAMES.tsv` as it is, in the code block below. To use it, save the content of the block under that name.

```text
# Renames of the extract, applied by tools/stx-extract.py. Rule: a declaration of the extract whose full
# name is also declared by weil-conjectures, Mathlib or the Library keeps its namespace, and its last name
# component `c` gets the prefix `stacks` in Lean's case convention: `Stacks` + c when c is UpperCamelCase
# (types, classes, predicates), `stacks_` + c for theorems, `stacks` + c with its first letter capitalised for
# other definitions. A row renames the declaration and every declaration of the extract in its namespace
# (fields, constructors, equation lemmas, theorems `X.foo`), which keep their own last components.
old full name	new full name	module	clashed with
AdicCompletion.factorPow_evalₐ	AdicCompletion.stacks_factorPow_evalₐ	StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow	weil-conjectures
AdicCompletion.isNoetherianRing	AdicCompletion.stacks_isNoetherianRing	StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.PowerSeriesSurjection	weil-conjectures
Algebra.IsSeparableExtension	Algebra.StacksIsSeparableExtension	StacksFrontier.FieldTheory.Separable.Defs	weil-conjectures
Algebra.isSeparableExtension_of_perfectField	Algebra.stacks_isSeparableExtension_of_perfectField	StacksFrontier.FieldTheory.Separable.PerfectField	weil-conjectures
AlgebraicGeometry.Scheme.Hom.apply_fiberι	AlgebraicGeometry.Scheme.Hom.stacks_apply_fiberι	StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic	weil-conjectures
AlgebraicGeometry.Scheme.Hom.fiberMap	AlgebraicGeometry.Scheme.Hom.stacksFiberMap	StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMap	weil-conjectures
AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal	AlgebraicGeometry.Scheme.IdealSheafData.stacks_isReduced_subscheme_vanishingIdeal	StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme	weil-conjectures
AlgebraicGeometry.Scheme.normalization	AlgebraicGeometry.Scheme.stacksNormalization	StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme	weil-conjectures
IsAnalyticallyUnramified	StacksIsAnalyticallyUnramified	StacksFrontier.RingTheory.AnalyticallyUnramified.Defs	weil-conjectures
IsCohenRing	StacksIsCohenRing	StacksFrontier.RingTheory.CohenRing	weil-conjectures
IsN1	StacksIsN1	StacksFrontier.RingTheory.Nagata.Defs	weil-conjectures
IsNagataRing	StacksIsNagataRing	StacksFrontier.RingTheory.Nagata.Defs	weil-conjectures; IsNagataRing.isNoetherianRing: weil-conjectures
IsRegularLocalRing.isDomain	IsRegularLocalRing.stacks_isDomain	StacksFrontier.RingTheory.RegularLocalRing.Basic	weil-conjectures; Library (theorem in Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain)
Module.Flat.tensorProduct_of_flat	Module.Flat.stacks_tensorProduct_of_flat	StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra	weil-conjectures
Module.depth	Module.stacksDepth	StacksFrontier.RingTheory.Depth.Defs.Defs	Library scan (Langlands/AnthropicFLT/Definitions/Def_Patching_SystemTypes.lean)
Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes	Module.stacks_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes	StacksFrontier.RingTheory.Depth.Criteria	Library scan (Langlands/AnthropicFLT/Theorems/Thm_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes.lean)
ringKrullDim_ne_top_of_finiteType	stacks_ringKrullDim_ne_top_of_finiteType	StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop	weil-conjectures
topologicalKrullDimAt	stacksTopologicalKrullDimAt	StacksFrontier.Topology.Dimension.Krull	weil-conjectures; topologicalKrullDimAt.eq_1: weil-conjectures
```
