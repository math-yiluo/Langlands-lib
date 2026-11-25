/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarStandardCohomology
public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory

/-! # Standard cohomology on the intrinsic common-stage Weil category

Source: Bhatt--Scholze 6.8.11(3), 6.8.14(2), 6.8.15; BBD 1.3
(blueprint: def-weil-derived-cohomology-sheaves).
The recorded ambient and coefficient-pair cohomology remain reexported. Here the same
standard truncation construction is applied to the general intrinsic pair category.
The Weil map is induced by the canonical Frobenius truncation comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

end WeilConjectures
