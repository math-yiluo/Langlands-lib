/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityLaxMonoidal

/-!

# Nearby duality and global sections: the pushforward exchange

Concrete inputs for `TraceFormula.Specialization.NearbyDualityGlobal`:

* the compatibility of the pushforward exchange `χ_f` with the lax tensor maps
  (`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_tensor`);
* **global Verdier duality** (`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_trace`).

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

/-! ### The pushforward exchange and the lax tensor maps -/

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f.left f'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) (hN :
      N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-- `CategoryTheory.mateEquiv_counit` for the restricted pullback and pushforward, for an
arbitrary transformation `β`; it is kept abstract so that the kernel never unfolds the pullback
exchange. -/
private lemma map_mateEquiv_app_comp_counit_aux
    (β : boundedConstructibleNearbyCycles hN ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleNearbyCycles hM)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        ((mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ f') β).app A) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ f').counit.app
          ((boundedConstructibleNearbyCycles hM).obj A) =
      β.app ((boundedConstructibleLowerStar ℓ f).obj A) ≫
        (boundedConstructibleNearbyCycles hM).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app A) :=
  mateEquiv_counit _ _ β A

/-- The restricted pushforward exchange is the mate of the restricted pullback exchange:
compatibility with the counits of `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. -/
lemma Hom.map_boundedConstructiblePushforwardExchange_app_comp_counit_app
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        ((φ.boundedConstructiblePushforwardExchange ℓ hM hN).app A) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ f').counit.app
          ((boundedConstructibleNearbyCycles hM).obj A) =
      (φ.boundedConstructiblePullbackExchange ℓ hM hN).app
          ((boundedConstructibleLowerStar ℓ f).obj A) ≫
        (boundedConstructibleNearbyCycles hM).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app A) := by
  rw [Hom.boundedConstructiblePushforwardExchange_eq_mateEquiv]
  exact map_mateEquiv_app_comp_counit_aux hM hN _ A

/-- The oplax monoidality of `NearbyCyclesModel.liftExchange` of an arbitrary transformation
`α : Ψ_N ⋙ Lf'^* ⟶ Lf^* ⋙ Ψ_M`, deduced from that of `α`; the transformation is kept abstract so
that the kernel never unfolds the pullback exchange. -/
private lemma liftExchange_tensor_oplax_aux
    (α : N.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
        L((f'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ M.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (hα : ∀ A B, L((f'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        (N.tensorMap (Profinite.padicAlgClRingObj ℓ) A B) ≫ α.app (A ⊗ B) ≫
          (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
            (Functor.OplaxMonoidal.δ L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) A B) =
      Functor.OplaxMonoidal.δ L((f'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) _ _ ≫
        (α.app A ⊗ₘ α.app B) ≫ M.tensorMap (Profinite.padicAlgClRingObj ℓ) _ _)
    (β : boundedConstructibleNearbyCycles hN ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' ⟶
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
          boundedConstructibleNearbyCycles hM)
    (hβ : β = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _) α
        (fun K ↦ hN K.obj K.property) (fun K ↦ hM K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f' K)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f K))
    (A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        (boundedConstructibleTensorMap hN A B) ≫
        β.app (A ⊗ B) ≫ (boundedConstructibleNearbyCycles hM).map
          (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            f) A B) =
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f')
          _ _ ≫ (β.app A ⊗ₘ β.app B) ≫ boundedConstructibleTensorMap hM _ _ := by
  subst hβ
  apply ObjectProperty.hom_ext
  -- Normalize the restricted maps explicitly so matching `hα` does not unfold the
  -- concrete nearby-cycles functors to compare their morphisms.
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    boundedConstructibleUpperStar_δ_hom, ObjectProperty.tensorHom_hom', liftExchange_app_hom,
    boundedConstructibleNearbyCycles, ObjectProperty.lift_map, ObjectProperty.homMk_hom,
    Functor.comp_map, ObjectProperty.ι_map, boundedConstructibleTensorMap]
  exact hα A.obj B.obj

/-- **The restricted pullback exchange is monoidal**, in the oplax form: the restriction of
`NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`. -/
lemma Hom.boundedConstructiblePullbackExchange_tensor_oplax (A B :
    Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        (boundedConstructibleTensorMap hN A B) ≫
        (φ.boundedConstructiblePullbackExchange ℓ hM hN).app (A ⊗ B) ≫
        (boundedConstructibleNearbyCycles hM).map
          (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              f) A B) =
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f') _
          _ ≫
        ((φ.boundedConstructiblePullbackExchange ℓ hM hN).app A ⊗ₘ
          (φ.boundedConstructiblePullbackExchange ℓ hM hN).app B) ≫
        boundedConstructibleTensorMap hM _ _ :=
  liftExchange_tensor_oplax_aux hM hN (φ.pullbackExchange _)
    (φ.map_tensorMap_comp_pullbackExchange_app _) _
    (φ.boundedConstructiblePullbackExchange_eq_liftExchange' hM hN) A B

/-- `CategoryTheory.Verdier.pushforwardExchange_tensor_aux` for the restricted functors, for
arbitrary transformations `β` (pullback exchange) and `χ` (its mate); they are kept abstract so
that the kernel never unfolds the exchanges. -/
private lemma pushforwardExchange_tensor_restricted_aux
    (β : boundedConstructibleNearbyCycles hN ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleNearbyCycles hM)
    (χ : boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleNearbyCycles hN ⟶
      boundedConstructibleNearbyCycles hM ⋙ boundedConstructibleLowerStar ℓ f')
    (hχ : ∀ A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map (χ.app A) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ f').counit.app
          ((boundedConstructibleNearbyCycles hM).obj A) =
      β.app ((boundedConstructibleLowerStar ℓ f).obj A) ≫
        (boundedConstructibleNearbyCycles hM).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app A))
    (hβ : ∀ A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          (boundedConstructibleTensorMap hN A B) ≫
          β.app (A ⊗ B) ≫
          (boundedConstructibleNearbyCycles hM).map
            (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
              ℓ f) A B) =
        Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            f') _ _ ≫
          (β.app A ⊗ₘ β.app B) ≫ boundedConstructibleTensorMap hM _ _)
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (χ.app A ⊗ₘ χ.app B) ≫
        (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f';
          Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f') _ _) ≫
        (boundedConstructibleLowerStar ℓ f').map (boundedConstructibleTensorMap hM A B) =
      boundedConstructibleTensorMap hN _ _ ≫ (boundedConstructibleNearbyCycles hN).map
          (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f;
            Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f) A B) ≫
        χ.app (A ⊗ B) :=
  Verdier.pushforwardExchange_tensor_aux (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f')
    (boundedConstructibleTensorMap hM) (boundedConstructibleTensorMap hN)
    (fun x y ↦ boundedConstructibleTensorMap_natural hM x y) β χ hχ hβ A B

/-- **The pushforward exchange is compatible with the lax tensor maps** (blueprint
`lemma-nearby-duality-proper-direct-image` (1), "the lax products commute through proper exchange"):
with the lax monoidal structures of `Rf_*` and `Rf'_*` (`boundedConstructibleLowerStarLaxMonoidal`),
`Rf'_*(μ_M) ∘ μ_{Rf'_*} ∘ (χ ⊗ χ) = χ ∘ Ψ_N(μ_{Rf_*}) ∘ μ_N`. Both sides have the same adjoint,
the tensor product of the generic-open counits, by the monoidality of the pullback exchange
(`CategoryTheory.Verdier.pushforwardExchange_tensor_aux`). -/
lemma Hom.boundedConstructiblePushforwardExchange_tensor (A B :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((φ.boundedConstructiblePushforwardExchange ℓ hM hN).app A ⊗ₘ
        (φ.boundedConstructiblePushforwardExchange ℓ hM hN).app B) ≫
        (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f';
          Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f') _ _) ≫
        (boundedConstructibleLowerStar ℓ f').map (boundedConstructibleTensorMap hM A B) =
      boundedConstructibleTensorMap hN _ _ ≫ (boundedConstructibleNearbyCycles hN).map
          (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f;
            Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f) A B) ≫
        (φ.boundedConstructiblePushforwardExchange ℓ hM hN).app (A ⊗ B) :=
  pushforwardExchange_tensor_restricted_aux hM hN (φ.boundedConstructiblePullbackExchange ℓ hM hN)
    (φ.boundedConstructiblePushforwardExchange ℓ hM hN)
    (φ.map_boundedConstructiblePushforwardExchange_app_comp_counit_app hM hN)
    (φ.boundedConstructiblePullbackExchange_tensor_oplax hM hN) A B

end NearbyCyclesModel

/-! ### Global Verdier duality -/

section Global

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsProper (toPoint Z).left]

/-- **Global Verdier duality** (blueprint `lemma-nearby-duality-proper-direct-image` (3), "global
Verdier duality"): for a proper `k`-scheme `Z` with structure morphism `a`, the duality map
`Ra_* D_Z K ⟶ RHom(Ra_* K, ℚ̄_ℓ)` of `(Ra_*, μ, tr_Z)` (`μ` the lax structure
`boundedConstructibleLowerStarLaxMonoidal`, `tr_Z` the trace `NearbyCyclesModel.trace`) is an
isomorphism: read through `Ra_! ≅ Ra_*` it is the Verdier exchange morphism
(`CategoryTheory.Verdier.nearbyDualityMap_comp_pre_eq_exchange`), an isomorphism by
`ProEtale.CondensedRing.isIso_verdierExchange`. -/
theorem isIso_nearbyDualityMap_lowerStar_trace (K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap
      (letI := boundedConstructibleLowerStarLaxMonoidal ℓ
        (toPoint Z);
        Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ (toPoint Z)))
      (NearbyCyclesModel.trace ℓ Z) K) := by
  have e := Verdier.nearbyDualityMap_comp_pre_eq_exchange
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (toPoint Z))
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z))
    (boundedConstructibleExceptionalProjection ℓ (toPoint Z))
    (fun T B ↦ upperStar_map_exceptionalProjection_comp_counit ℓ (toPoint Z) T B) K (𝟙_ _)
  have h₁ : IsIso (Verdier.exchange
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (toPoint Z))
      (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z))
      (boundedConstructibleExceptionalProjection ℓ (toPoint Z)) K (𝟙_ _)) :=
    isIso_verdierExchange ℓ (toPoint Z) K (𝟙_ _)
  have h₂ := isIso_pre_app
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z)).hom.app K) (𝟙_ _)
  rw [← e] at h₁
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h₂ h₁

end Global

end AlgebraicGeometry.ProEtale.CondensedRing
