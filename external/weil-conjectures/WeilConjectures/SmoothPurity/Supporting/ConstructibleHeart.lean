/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.ConstructibleStandardTStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
/-! # Constructible hearts and their standard truncations

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-admissible`,
`def-weil-constructible-heart`, order 1506 (blueprint: def-weil-constructible-heart).

The hearts are the full subcategories on the intersection of the specified standard
classes. On a finite-type geometric scheme the standard pair determines a unique
bounded t-structure; its canonical truncations give the displayed vanishing tests.
-/

@[expose] public section

set_option autoImplicit false

universe d u v

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

section Hearts

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

end Hearts

section FiniteType

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})
  [base : Y.Over (AlgebraicGeometry.Spec (CommRingCat.of D.k))]
  [finiteTypeLocal :
    AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of D.k))]
  [finiteTypeCompact :
    AlgebraicGeometry.QuasiCompact (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of D.k))]

include base finiteTypeLocal finiteTypeCompact

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

end FiniteType

section PaperCoefficients

end PaperCoefficients

end WeilConjectures
