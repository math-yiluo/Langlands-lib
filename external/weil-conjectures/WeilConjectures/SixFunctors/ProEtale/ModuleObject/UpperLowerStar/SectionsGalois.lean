/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.StalkFrobeniusOfId

/-!
# The Galois action on sections of module objects

The Galois action `x^* M ⟶ σ^* x^* M ≅ (σ ≫ x)^* M = x^* M`, for a trivialization `σ^*
≅ 𝟭` which is the unit comparison at the unit, pulls back global sections.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {S T : Scheme.{u}}

/-- The Galois action `x̄^* M ⟶ σ^* x̄^* M ≅ (σ ≫ x̄)^* M = x̄^* M`,
for a trivialization
`τ : σ^* ≅ 𝟭` which is the unit comparison at the unit,
sends a global section to its pullback
along `σ`. -/
lemma comp_inv_app_comp_upperStarComp_inv_app_eq_upperStarSectionMap
    (σ : S ⟶ S) (x : S ⟶ T) (h : σ ≫ x = x)
    (τ : (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _)
    (hτ : τ.inv.app 𝟙ₘ = (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj
        ℓ⟧).hom)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))
    (v : 𝟙ₘ ⟶ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) :
    v ≫ τ.inv.app ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).inv.app M ≫
        (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) h).hom.app M =
      upperStarSectionMap (Profinite.padicAlgClRingObj ℓ) σ h M v := by
  have hn := τ.inv.naturality v
  rw [Functor.id_map] at hn
  rw [reassoc_of% hn, hτ, upperStarEqToIso_hom_app, upperStarSectionMap]

end AlgebraicGeometry.ProEtale.CondensedRing
