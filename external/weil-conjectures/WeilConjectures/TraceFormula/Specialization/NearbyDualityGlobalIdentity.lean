/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGlobal
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange

/-!

# Global sections of the duality map of a proper model: the identity

For a trait model `M` over the base with proper `X`, `X'` and proper total space,
`NearbyCyclesModel.isIso_lowerStar_nearbyDualityMap_of_isIso` shows that `RΓ(X', δ_{M,K})` is an
isomorphism. This file keeps the underlying identity (blueprint
`lemma-nearby-duality-proper-direct-image`, (E.14)): under the proper exchange
`χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M`, global Verdier duality on both fibres (the duality maps of
`(Ra_*, μ, tr_X)` and `(Ra'_*, μ, tr_{X'})`) and the duality map of the trait itself,
`RΓ(X', δ_{M,K})` is the composite of these canonical isomorphisms.

## Main results

* `CategoryTheory.Verdier.nearbyDualityMap_proper_natTrans`: the abstract proper identity
  `CategoryTheory.Verdier.nearbyDualityMap_proper'` for an exchange given as a natural
  transformation, with implicit categories.
* `NearbyCyclesModel.pushforwardExchange_comp_lowerStar_map_nearbyDualityMap`: the square
  `χ ∘ RΓ(δ_{M,K}) ∘ δ_{a'} ∘ D(χ) = Ψ_S(δ_a) ∘ δ_S` (blueprint
  `lemma-nearby-duality-proper-direct-image`, (E.14)).
* `NearbyCyclesModel.lowerStar_map_nearbyDualityMap_eq`: `RΓ(X', δ_{M,K})` as the composite of
  the inverse of `χ_a`, Verdier duality on `X`, the duality map of the trait, `D(χ_a)⁻¹` and
  the inverse of Verdier duality on `X'`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Verdier

/-- `CategoryTheory.Verdier.nearbyDualityMap_proper'` for an exchange given as a natural
transformation `χ : G ⋙ Ψ_Y ⟶ Ψ_X ⋙ G'`, its compatibility with the lax tensor maps given first.
The categories and their monoidal structures are implicit, found by unification from that
compatibility (as in `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans`). -/
theorem nearbyDualityMap_proper_natTrans {C : Type*} {_ : Category C}
    {_ : MonoidalCategory C} {_ : MonoidalClosed C} {C' : Type*} {_ : Category C'}
    {_ : MonoidalCategory C'} {_ : MonoidalClosed C'} {D : Type*} {_ : Category D}
    {_ : MonoidalCategory D} {_ : MonoidalClosed D} {D' : Type*} {_ : Category D'}
    {_ : MonoidalCategory D'} {_ : MonoidalClosed D'} {ΨX : C ⥤ C'} {ΨY : D ⥤ D'}
    {μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B)}
    {μY : ∀ A B : D, ΨY.obj A ⊗ ΨY.obj B ⟶ ΨY.obj (A ⊗ B)} {ωX : C} {ωX' : C'} {ωY : D}
    {ωY' : D'} {θX : ΨX.obj ωX ⟶ ωX'} {θY : ΨY.obj ωY ⟶ ωY'} {G : C ⥤ D} {G' : C' ⥤ D'}
    {μG : ∀ A B : C, G.obj A ⊗ G.obj B ⟶ G.obj (A ⊗ B)}
    {μG' : ∀ A B : C', G'.obj A ⊗ G'.obj B ⟶ G'.obj (A ⊗ B)} {tr : G.obj ωX ⟶ ωY}
    {tr' : G'.obj ωX' ⟶ ωY'} {χ : G ⋙ ΨY ⟶ ΨX ⋙ G'}
    (hμ : ∀ A B : C, (χ.app A ⊗ₘ χ.app B) ≫ μG' _ _ ≫ G'.map (μX A B) =
      μY _ _ ≫ ΨY.map (μG A B) ≫ χ.app (A ⊗ B))
    (hθ : ΨY.map tr ≫ θY = χ.app ωX ≫ G'.map θX ≫ tr')
    (hμG' : ∀ (A : C') {B B' : C'} (y : B ⟶ B'),
      G'.obj A ◁ G'.map y ≫ μG' A B' = μG' A B ≫ G'.map (A ◁ y))
    (hμY : ∀ {A A' B B' : D} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨY.map x ⊗ₘ ΨY.map y) ≫ μY A' B' = μY A B ≫ ΨY.map (x ⊗ₘ y)) (M : C) :
    ΨY.map (nearbyDualityMap μG tr M) ≫ nearbyDualityMap μY θY (G.obj M) =
      χ.app _ ≫ G'.map (nearbyDualityMap μX θX M) ≫
        nearbyDualityMap μG' tr' (ΨX.obj M) ≫ (pre (χ.app M)).app ωY' :=
  nearbyDualityMap_proper' μX μY θX θY μG μG' tr tr' (fun A ↦ χ.app A) hμG' hμY
    (fun g ↦ χ.naturality g) hμ hθ M

/-- The transposes `D(f)` and `D(f⁻¹)` of an isomorphism `f` are inverse. The categories and their
monoidal structures are implicit, found by unification. -/
@[reassoc]
lemma pre_app_comp_pre_inv_app {C : Type*} {_ : Category C} {_ : MonoidalCategory C}
    {_ : MonoidalClosed C} {A B : C} (f : A ⟶ B) [IsIso f] (W : C) :
    (pre f).app W ≫ (pre (inv f)).app W = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← pre_map, IsIso.inv_hom_id, pre_id, NatTrans.id_app]

end CategoryTheory.Verdier

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme


-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **Global sections of the duality map of a proper model** (blueprint
`lemma-nearby-duality-proper-direct-image`, (E.14); `lemma-nearby-duality-proper-direct-image` (1),
(3)): if `X`, `X'` and the total space of the trait model `M` over the base are proper, then
```
χ_a ≫ RΓ(X', δ_{M,K}) ≫ δ_{a'} ≫ D(χ_a) = Ψ_S(δ_a) ≫ δ_S
```
where `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M` is the proper exchange of the structure morphism
(`NearbyCyclesModel.IsTraitModelOfBase.pushforwardExchange`), `δ_a`, `δ_{a'}` are global Verdier
duality on `X` and `X'` (the duality maps of `(Ra_*, μ, tr)`, isomorphisms by
`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_trace`), and `δ_S` is the duality map of
the trait at `RΓ(X_η̄, K)`, the canonical isomorphism of the monoidal functor `Ψ_S` with duals
(`NearbyCyclesModel.isIso_nearbyDualityMap_traitModel`). That is, `RΓ(X', δ_{M,K})` is identified
with the identity of `RHom(RΓ(X_η̄, K), ℚ̄_ℓ)`.

This is `CategoryTheory.Verdier.nearbyDualityMap_proper` for `G = Ra_*`, `G' = Ra'_*`, with the
compatibility of `χ_a` with the lax tensor maps
(`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_tensor`) and the proper axiom of
the dualizing maps
(`NearbyCyclesModel.NearbyDualizingData.pushforwardExchange_comp_map_θ_comp_trace`). -/
theorem pushforwardExchange_comp_lowerStar_map_nearbyDualityMap (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g) [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    [IsProper q] (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (h.pushforwardExchange ℓ).app ((ihom K).obj (dualizingComplex ℓ X)) ≫
        (boundedConstructibleLowerStar ℓ (toPoint X')).map
          (Verdier.nearbyDualityMap
            (Ψ := boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ))
            (boundedConstructibleTensorMap (h.preservesBoundedConstructible ℓ)) (D.θ h) K) ≫
        Verdier.nearbyDualityMap (Ψ := boundedConstructibleLowerStar ℓ (toPoint X'))
          (letI := boundedConstructibleLowerStarLaxMonoidal ℓ (toPoint X');
            Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ (toPoint X')))
          (trace ℓ X')
          ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj K) ≫
        (pre ((h.pushforwardExchange ℓ).app K)).app (𝟙_ _) =
      (traitSpecialization k k' (ℓ := ℓ)).map
          (Verdier.nearbyDualityMap (Ψ := boundedConstructibleLowerStar ℓ (toPoint X))
            (letI := boundedConstructibleLowerStarLaxMonoidal ℓ (toPoint X);
              Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ (toPoint X)))
            (trace ℓ X) K) ≫
        Verdier.nearbyDualityMap (Ψ := traitSpecialization k k' (ℓ := ℓ))
          (boundedConstructibleTensorMap
            (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ))
          (inv (traitSpecializationUnit k k' (ℓ := ℓ)))
          ((boundedConstructibleLowerStar ℓ (toPoint X)).obj K) := by
  have hθ := (D.pushforwardExchange_comp_map_θ_comp_trace h hgen).symm
  have t₁ : h.pushforwardExchange ℓ = h.toTrait.boundedConstructiblePushforwardExchange ℓ
      (h.preservesBoundedConstructible ℓ) (preservesBoundedConstructible_traitModel ℓ) := rfl
  rw [t₁] at hθ ⊢
  exact (Verdier.nearbyDualityMap_proper_natTrans
    (fun A B ↦ Hom.boundedConstructiblePushforwardExchange_tensor (f := toPoint X)
      (f' := toPoint X') h.toTrait (h.preservesBoundedConstructible ℓ)
      (preservesBoundedConstructible_traitModel ℓ) A B) hθ
    (fun A _ _ y ↦ letI := boundedConstructibleLowerStarLaxMonoidal ℓ (toPoint X')
      Functor.LaxMonoidal.μ_natural_right _ A y)
    (fun x y ↦ boundedConstructibleTensorMap_natural _ x y) K).symm

/-- **Global sections of the duality map of a proper model, solved** (blueprint
`lemma-nearby-duality-proper-direct-image`, (E.14)): in the situation of
`NearbyCyclesModel.pushforwardExchange_comp_lowerStar_map_nearbyDualityMap`, `RΓ(X', δ_{M,K})`
(`δ_{M,K} = NearbyCyclesModel.nearbyDualityMap ℓ D h K`, unfolded) is the composite of the
canonical isomorphisms
```
χ_a⁻¹ ≫ Ψ_S(δ_a) ≫ δ_S ≫ D(χ_a)⁻¹ ≫ δ_{a'}⁻¹,
```
the inverse of the proper exchange, global Verdier duality on `X`, the duality map of the trait,
the transpose of the inverse of the proper exchange, and the inverse of global Verdier duality on
`X'`. -/
theorem lowerStar_map_nearbyDualityMap_eq (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g) [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    [IsProper q] (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar ℓ (toPoint X')).map
        (Verdier.nearbyDualityMap
          (Ψ := boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ))
          (boundedConstructibleTensorMap (h.preservesBoundedConstructible ℓ)) (D.θ h) K) =
      inv (I := h.isIso_pushforwardExchange_app ℓ hgen _)
          ((h.pushforwardExchange ℓ).app ((ihom K).obj (dualizingComplex ℓ X))) ≫
        (traitSpecialization k k' (ℓ := ℓ)).map
          (Verdier.nearbyDualityMap (Ψ := boundedConstructibleLowerStar ℓ (toPoint X))
            (letI := boundedConstructibleLowerStarLaxMonoidal ℓ (toPoint X);
              Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ (toPoint X)))
            (trace ℓ X) K) ≫
        Verdier.nearbyDualityMap (Ψ := traitSpecialization k k' (ℓ := ℓ))
          (boundedConstructibleTensorMap
            (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ))
          (inv (traitSpecializationUnit k k' (ℓ := ℓ)))
          ((boundedConstructibleLowerStar ℓ (toPoint X)).obj K) ≫
        (pre (inv (I := h.isIso_pushforwardExchange_app ℓ hgen K)
          ((h.pushforwardExchange ℓ).app K))).app (𝟙_ _) ≫
        inv (I := isIso_nearbyDualityMap_lowerStar_trace ℓ X' _)
          (Verdier.nearbyDualityMap (Ψ := boundedConstructibleLowerStar ℓ (toPoint X'))
            (letI := boundedConstructibleLowerStarLaxMonoidal ℓ (toPoint X');
              Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ (toPoint X')))
            (trace ℓ X')
            ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj K)) := by
  have := h.isIso_pushforwardExchange_app ℓ hgen ((ihom K).obj (dualizingComplex ℓ X))
  have := h.isIso_pushforwardExchange_app ℓ hgen K
  have := isIso_nearbyDualityMap_lowerStar_trace ℓ X'
    ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj K)
  rw [← reassoc_of% (pushforwardExchange_comp_lowerStar_map_nearbyDualityMap ℓ D h hgen K),
    IsIso.inv_hom_id_assoc, Verdier.pre_app_comp_pre_inv_app_assoc, IsIso.hom_inv_id,
    Category.comp_id]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
