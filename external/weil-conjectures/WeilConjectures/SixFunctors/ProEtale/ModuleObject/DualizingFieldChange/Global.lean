/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Finite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Tensor
import WeilConjectures.Tactic.ExactModProofs

/-!

# Base change of dualizing complexes: global sections and finite schemes

Let `X` be a proper `k₁`-scheme, `X'` a proper `k₂`-scheme with a cartesian square
`π ≫ a = a' ≫ πₛ` over `πₛ : Spec k₂ ⟶ Spec k₁`, and `φ : π^* ω_X ⟶ ω_{X'}` the comparison of
the dualizing complexes (`ProEtale.CondensedRing.dualizingComplexBaseChange`), for an
isomorphism `e : πₛ^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`.

* **Global sections** (`ProEtale.CondensedRing.isIso_lowerStar_map_dualizingComplexBaseChange`):
  `Ra'_* φ` is an isomorphism; more generally the global sections of the duality map
  `δ_{π,M} : π^* D_X M ⟶ D_{X'} π^* M` are isomorphisms
  (`ProEtale.CondensedRing.isIso_lowerStar_map_nearbyDualityMap_dualizingComplexBaseChange`).
  This is the abstract proper identity
  `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans` with `G = Ra_*`,
  `G' = Ra'_*`, `Ψ_X = π^*`, `Ψ_Y = πₛ^*` and `χ` the proper base change isomorphism; its inputs
  are the trace compatibility of `φ`, the compatibility of base change with the lax tensor maps
  (`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap_tensor`), global Verdier duality on
  `X` and `X'` and the commutation of `πₛ^*` with duals.
* **Finite schemes** (`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_isFinite`): if
  `X` is finite over `k₁`, `φ` is an isomorphism, the finite pushforward `Ra'_*` being
  conservative.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

section Global

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [IsProper (toPoint X).left]
  {X' : Over (Spec (.of k₂))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [IsProper (toPoint X').left]
  {π : X'.left ⟶ X.left} {πₛ : Spec (.of k₂) ⟶ Spec (.of k₁)}
  (e : (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).obj (𝟙_ _) ⟶
    𝟙_ _)

/-- `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans` for the pullbacks
`π^*`, `πₛ^*` and the pushforwards to the points, for an arbitrary invertible exchange `χ` and an
arbitrary dualizing map `φ`; they are kept abstract so that the kernel never unfolds them. -/
private lemma isIso_lowerStar_map_nearbyDualityMap_aux [IsIso e]
    (χ : boundedConstructibleLowerStar ℓ (toPoint X) ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π ⋙
        boundedConstructibleLowerStar ℓ (toPoint X')) [IsIso χ]
    (φ : (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π).obj (dualizingComplex ℓ X) ⟶
      dualizingComplex ℓ X')
    (hμ : ∀ A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      (χ.app A ⊗ₘ χ.app B) ≫
        (letI := boundedConstructibleLowerStarLaxMonoidal ℓ (toPoint X');
          Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ (toPoint X')) _ _) ≫
        (boundedConstructibleLowerStar ℓ (toPoint X')).map
          (Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π) A B) =
      Functor.LaxMonoidal.μ
          (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ) _ _ ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).map
          (letI := boundedConstructibleLowerStarLaxMonoidal ℓ (toPoint X);
            Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ (toPoint X)) A B) ≫
        χ.app (A ⊗ B))
    (hθ : (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).map
          (NearbyCyclesModel.trace ℓ X) ≫ e =
      χ.app (dualizingComplex ℓ X) ≫ (boundedConstructibleLowerStar ℓ (toPoint X')).map φ ≫
        NearbyCyclesModel.trace ℓ X')
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleLowerStar ℓ (toPoint X')).map
      (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
        (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π) A B) φ M)) :=
  Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans hμ hθ
    (fun A _ _ y ↦ letI := boundedConstructibleLowerStarLaxMonoidal ℓ (toPoint X')
      Functor.LaxMonoidal.μ_natural_right _ A y)
    (fun x y ↦ Functor.LaxMonoidal.μ_natural _ x y) M inferInstance inferInstance
    (isIso_nearbyDualityMap_lowerStar_trace ℓ X M)
    (isIso_nearbyDualityMap_lowerStar_trace ℓ X' _)
    (isIso_nearbyDualityMap_upperStarOfMap_point ℓ πₛ e _)

/-- **Global sections of the duality map of the base change**: for the pullback `π^*` with
dualizing map the comparison `φ : π^* ω_X ⟶ ω_{X'}`, the global sections
`Ra'_* δ_{π,M} : Ra'_* π^* D_X M ⟶ Ra'_* D_{X'} π^* M` of the duality map are invertible. This is
`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans` for `G = Ra_*`,
`G' = Ra'_*`, `Ψ_X = π^*`, `Ψ_Y = πₛ^*` and `χ` the proper base change isomorphism, with the
compatibility of base change with the lax tensor maps
(`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap_tensor`), the trace compatibility of
`φ`, global Verdier duality on `X` and `X'`
(`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_trace`) and the commutation of `πₛ^*`
with duals (`ProEtale.CondensedRing.isIso_nearbyDualityMap_upperStarOfMap_point`). -/
theorem isIso_lowerStar_map_nearbyDualityMap_dualizingComplexBaseChange [IsIso e]
    (sq : IsPullback π (toPoint X').left (toPoint X).left πₛ)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleLowerStar ℓ (toPoint X')).map
      (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
        (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π) A B)
        (dualizingComplexBaseChange ℓ e sq) M)) := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq
  have h := isIso_lowerStar_map_nearbyDualityMap_aux ℓ e
    (boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq) (dualizingComplexBaseChange ℓ e sq)
    (boundedConstructibleBaseChangeOfMap_tensor ℓ sq.toCommSq)
    (baseChange_comp_map_dualizingComplexBaseChange_comp_trace ℓ e sq).symm M
  cast_proofs h

/-- **Global sections of the comparison of dualizing complexes**:
`Ra'_* φ : Ra'_* π^* ω_X ⟶ Ra'_* ω_{X'}` is invertible. -/
theorem isIso_lowerStar_map_dualizingComplexBaseChange [IsIso e]
    (sq : IsPullback π (toPoint X').left (toPoint X).left πₛ) :
    IsIso ((boundedConstructibleLowerStar ℓ (toPoint X')).map
      (dualizingComplexBaseChange ℓ e sq)) :=
  Verdier.isIso_map_of_isIso_map_nearbyDualityMap_unit _ _ _
    (isIso_lowerStar_map_nearbyDualityMap_dualizingComplexBaseChange ℓ e sq (𝟙_ _))

/-- **Base change of dualizing complexes, finite case**: for `X` finite over `k₁`, the comparison
`π^* ω_X ⟶ ω_{X'}` is an isomorphism: `X'` is finite over `k₂`, and the finite pushforward
`Ra'_*` is conservative
(`ProEtale.CondensedRing.isIso_of_isIso_map_boundedConstructibleLowerStar_of_isFinite`). -/
theorem isIso_dualizingComplexBaseChange_of_isFinite [IsIso e]
    (sq : IsPullback π (toPoint X').left (toPoint X).left πₛ) [IsFinite (toPoint X).left] :
    IsIso (dualizingComplexBaseChange ℓ e sq) := by
  have : IsFinite (toPoint X').left :=
    MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›
  exact isIso_of_isIso_map_boundedConstructibleLowerStar_of_isFinite ℓ (toPoint X') _
    (isIso_lowerStar_map_dualizingComplexBaseChange ℓ e sq)

end Global

end AlgebraicGeometry.ProEtale.CondensedRing
