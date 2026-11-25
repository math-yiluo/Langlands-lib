/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.MapIsoUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
public import WeilConjectures.TateTwist.ProEtale

/-!
# Tate twists are locally free once `ℚ̄_ℓ(1)` is locally trivial

Let `X` be a scheme and `{gᵢ : Uᵢ ⟶ X}` a pro-étale cover over which the Tate twist `ℚ̄_ℓ,X(1)`
becomes trivial: `gᵢ^* ℚ̄_ℓ,X(1) ≅ gᵢ^* ℚ̄_ℓ,X` as modules over `gᵢ^* ℚ̄_ℓ,X`. Then every Tate twist
`ℚ̄_ℓ,X(d)`, `d ∈ ℤ`, becomes trivial over the same cover
(`AlgebraicGeometry.ProEtale.upperStarMapModTateTwistIsoUnit`), hence is locally free of rank one
(`AlgebraicGeometry.ProEtale.isLocallyFree_tateTwist_of_iso`): the pullbacks `gᵢ^*` are strong
monoidal for the relative tensor products and commute with the internal homs, and `ℚ̄_ℓ,X(d)` is a
tensor power of `ℚ̄_ℓ,X(1)` for `d ≥ 0` and the dual of one for `d < 0`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X U : Scheme.{u}} (g : U ⟶ X) [WeaklyEtale g] (ℓ : ℕ) [Fact ℓ.Prime]

/-- If the pullback of `ℚ̄_ℓ,X(1)` along `g` is trivial, so is the pullback of every non-negative
Tate twist `ℚ̄_ℓ,X(d) = ℚ̄_ℓ,X(1)^{⊗ d}`. -/
noncomputable def upperStarMapModTateTwistNatIsoUnit
    (e : ((g)^*[Ab.{u + 1}].mapMod (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj
      (tateTwistOne X ℓ) ≅ 𝟙_ _) :
    (d : ℕ) → ((g)^*[Ab.{u + 1}].mapMod
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj (tateTwistNat X ℓ d) ≅ 𝟙_ _
  | 0 => Functor.mapUnitIsoUnit _
  | d + 1 => Functor.mapTensorObjIsoUnit _ (upperStarMapModTateTwistNatIsoUnit e d) e

/-- If the pullback of `ℚ̄_ℓ,X(1)` along a weakly étale `g` is trivial, so is the pullback of
every Tate twist `ℚ̄_ℓ,X(d)`, `d ∈ ℤ`: for `d < 0` it is the dual of `ℚ̄_ℓ,X(-d)`, and `g^*`
commutes with internal homs. -/
noncomputable def upperStarMapModTateTwistIsoUnit
    (e : ((g)^*[Ab.{u + 1}].mapMod (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj
      (tateTwistOne X ℓ) ≅ 𝟙_ _) :
    (d : ℤ) → ((g)^*[Ab.{u + 1}].mapMod
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj (tateTwist X ℓ d) ≅ 𝟙_ _
  | (d : ℕ) => upperStarMapModTateTwistNatIsoUnit g ℓ e d
  | .negSucc d =>
    have := isIso_ihomComparison_upperStar Ab.{u + 1} g
    Functor.mapIhomObjIsoUnit _ (upperStarMapModTateTwistNatIsoUnit g ℓ e (d + 1))
      (Functor.mapUnitIsoUnit _)

/-- **The Tate twists are locally free of rank one** over any pro-étale cover over which
`ℚ̄_ℓ,X(1)` is trivial. -/
theorem isLocallyFree_tateTwist_of_iso (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, Nonempty (((𝒰.f i)^*[Ab.{u + 1}].mapMod
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj (tateTwistOne X ℓ) ≅ 𝟙_ _))
    (d : ℤ) :
    IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) (tateTwist X ℓ d) := by
  refine ⟨𝒰, fun i ↦ ⟨1, ⟨?_⟩⟩⟩
  have : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  exact upperStarMapModTateTwistIsoUnit (𝒰.f i) ℓ (h i).some d ≪≫
    (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular _)).symm

end AlgebraicGeometry.ProEtale
