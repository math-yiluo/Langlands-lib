/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ContractingIdeals
public import WeilConjectures.TraceFormula.LocalTermLocality
public import WeilConjectures.TraceFormula.Specialization.DeformationModelNormalCone
public import WeilConjectures.TraceFormula.Specialization.DeformationModelProduct

/-!

# The special fibre of the deformation of a contracting correspondence

Let `c = (c₁, c₂) : C ⟶ X × X` be contracting at the `k`-point `y` of its support, with
`x = c₁(y) = c₂(y)`. Deforming `X` to the normal cone of `x` and `C` to the normal cone of `y`,
the legs lift to the deformations (`IsContractingAt.ker_map_le_c₁`, `IsContractingAt.ker_map_le_c₂`)
and their special fibres are the legs `γᵢ : N_y C ⊗ k' ⟶ N_x X ⊗ k'` of the *specialized
correspondence* (`ProEtale.CondensedRing.Correspondence.IsContractingAt.specialLeg₁`,
`ProEtale.CondensedRing.Correspondence.IsContractingAt.specialLeg₂`). The contraction condition
forces `γ₂` to land set-theoretically in the zero section `x ⊗ k'` of `N_x X ⊗ k'`
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.range_specialLeg₂_subset`, blueprint
`lemma-normal-cones-contracting-ideals` (2)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable {c : Correspondence ℓ K} {y : RationalPoint c.C} (hc : c.IsContractingAt y)
  (k' : Type u) [Field k'] [Algebra k k']

namespace IsContractingAt

/-- The first special leg `γ₁ : N_y C ⊗ k' ⟶ N_x X ⊗ k'`, the special fibre of the lift of `c₁`
to the deformations to the normal cones. -/
noncomputable abbrev specialLeg₁ :
    deformationSpecialFibre c.C y.left.ker k' ⟶ deformationSpecialFibre X (y ≫ c.c₁).left.ker k' :=
  deformationSpecialFibreMap c.c₁ hc.ker_map_le_c₁ k'

/-- The second special leg `γ₂ : N_y C ⊗ k' ⟶ N_x X ⊗ k'`, the special fibre of the lift of `c₂`
to the deformations to the normal cones. -/
noncomputable abbrev specialLeg₂ :
    deformationSpecialFibre c.C y.left.ker k' ⟶ deformationSpecialFibre X (y ≫ c.c₁).left.ker k' :=
  deformationSpecialFibreMap c.c₂ hc.ker_map_le_c₂ k'

/-- **The contracting leg lands in the zero section** (blueprint
`lemma-normal-cones-contracting-ideals` (2)): the special leg `γ₂` maps the special fibre of the
deformation of `C` set-theoretically into the zero section of the special fibre `N_x X ⊗ k'` of the
deformation of `X`. -/
theorem range_specialLeg₂_subset :
    Set.range (hc.specialLeg₂ k').left ⊆
      Set.range (deformationSpecialFibreZeroSection X (y ≫ c.c₁).left.ker k').left := by
  obtain ⟨n, hn, hle⟩ := hc.ker_map_pow_le
  exact range_deformationSpecialFibreMap_subset k' c.c₂ hc.ker_map_le_c₂
    (IdealSheafData.range_normalConeMap_subset_range_normalConeZeroSection _ _ _ _ hn hle)

end IsContractingAt

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
