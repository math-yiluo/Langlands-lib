/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.TraceFormula.Specialization.NearbyDuality

/-!

# Nearby duality and open restriction: the concrete inputs

The compatibility of the duality map of nearby cycles with open restriction (blueprint
`lemma-nearby-duality-proper-direct-image` (2)) is the abstract identity
`CategoryTheory.Verdier.nearbyDualityMap_restrict_natTrans`. This file proves its concrete inputs
for trait models:
* the duality map of `(G, μ_G, e)` for a lax monoidal `G` is the internal-hom comparison of `G`
  followed by `e` (`CategoryTheory.Verdier.nearbyDualityMap_eq_ihomComparison`), so for an open
  immersion it is invertible by
  `ProEtale.CondensedRing.isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion`;
* the lax tensor map of nearby cycles on bounded constructible complexes is natural
  (`NearbyCyclesModel.boundedConstructibleTensorMap_natural`);
* the restricted pullback exchange is monoidal, in the lax form used there
  (`NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange_tensor`), from the ambient
  monoidality `NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`.

The remaining inputs are the invertibility of the pullback exchange for open immersions
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`) and the compatibility of the
dualizing maps with open restriction
(`NearbyCyclesModel.NearbyDualizingData.map_θ_comp_dualizingComplexUpperStarIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

namespace Verdier

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  {D : Type*} [Category* D] [MonoidalCategory D] [MonoidalClosed D]

/-- For a lax monoidal functor `G` and `e : G W ⟶ W'`, the duality map of `(G, μ_G, e)` is the
comparison `G [X, W] ⟶ [G X, G W] ⟶ [G X, W']` of internal homs followed by `e`. -/
lemma nearbyDualityMap_eq_ihomComparison (G : C ⥤ D) [G.LaxMonoidal] {W : C} {W' : D}
    (e : G.obj W ⟶ W') (X : C) :
    nearbyDualityMap (Functor.LaxMonoidal.μ G) e X =
      (Functor.LaxMonoidal.ihomComparison G X).app W ≫ (ihom (G.obj X)).map e := by
  apply uncurry_injective
  rw [uncurry_nearbyDualityMap, uncurry_natural_right, uncurry_eq, Category.assoc,
    Functor.LaxMonoidal.ihomComparison_ev_assoc]

omit [MonoidalClosed C] in
/-- An exchange `α : F' Ψ_X ⟶ Ψ_U F` between strong monoidal functors which is monoidal in the
oplax form `Ψ_U(δ_F) ∘ α ∘ F'(μ_X) = μ_U ∘ (α ⊗ α) ∘ δ_{F'}` is monoidal in the lax form. -/
lemma lax_of_oplax_aux {C' U U' : Type*} [Category* C'] [MonoidalCategory C'] [Category* U]
    [MonoidalCategory U] [Category* U'] [MonoidalCategory U'] {ΨX : C ⥤ C'} {ΨU : U ⥤ U'}
    {F : C ⥤ U} {F' : C' ⥤ U'} [F.Monoidal] [F'.Monoidal]
    (μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B))
    (μU : ∀ A B : U, ΨU.obj A ⊗ ΨU.obj B ⟶ ΨU.obj (A ⊗ B))
    (α : ∀ A : C, F'.obj (ΨX.obj A) ⟶ ΨU.obj (F.obj A)) (A B : C)
    (h : F'.map (μX A B) ≫ α (A ⊗ B) ≫ ΨU.map (Functor.OplaxMonoidal.δ F A B) =
      Functor.OplaxMonoidal.δ F' _ _ ≫ (α A ⊗ₘ α B) ≫ μU _ _) :
    (α A ⊗ₘ α B) ≫ μU _ _ ≫ ΨU.map (Functor.LaxMonoidal.μ F A B) =
      Functor.LaxMonoidal.μ F' _ _ ≫ F'.map (μX A B) ≫ α (A ⊗ B) := by
  rw [← Category.id_comp ((α A ⊗ₘ α B) ≫ _), ← Functor.Monoidal.μ_δ F', Category.assoc,
    ← reassoc_of% h, ← ΨU.map_comp, Functor.Monoidal.δ_μ, CategoryTheory.Functor.map_id,
    Category.comp_id]

end Verdier

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

omit [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] [IsSeparated X.hom]
  [IsSeparated X'.hom] in
/-- The lax tensor map of nearby cycles on bounded constructible complexes is natural. -/
lemma boundedConstructibleTensorMap_natural
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    {A A' B B' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (x : A ⟶ A') (y : B ⟶ B') :
    ((boundedConstructibleNearbyCycles hP).map x ⊗ₘ (boundedConstructibleNearbyCycles hP).map y) ≫
        boundedConstructibleTensorMap hP A' B' =
      boundedConstructibleTensorMap hP A B ≫ (boundedConstructibleNearbyCycles hP).map (x ⊗ₘ y) :=
  ObjectProperty.hom_ext _ (M.tensorMap_natural _ x.hom y.hom)

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {j : Y ⟶ X} {j' : Y' ⟶ X'} (φ : N.Hom M j.left j'.left)

/-- The restricted pullback exchange is `NearbyCyclesModel.liftExchange` of the ambient one. -/
lemma Hom.boundedConstructiblePullbackExchange_eq_liftExchange'
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) (hM :
        M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) :
    φ.boundedConstructiblePullbackExchange ℓ hN hM =
      liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _) (φ.pullbackExchange
            (Profinite.padicAlgClRingObj ℓ))
        (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
        (fun K ↦
          boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ j' K)
        (fun K ↦
          boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ j K) :=
  rfl

/-- The comparison `μ` of the restricted pullback is that of the ambient derived pullback. -/
lemma μ_boundedConstructibleUpperStar_hom {Z W : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom] (f : Z ⟶ W)
    (A B : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
      A B).hom = Functor.LaxMonoidal.μ L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) A.obj B.obj :=
  rfl

/-- The monoidality of `NearbyCyclesModel.liftExchange` of an arbitrary transformation
`α : Ψ_M ⋙ Lj'^* ⟶ Lj^* ⋙ Ψ_N`, deduced from that of `α`; the transformation is kept abstract so
that the kernel never unfolds the pullback exchange. -/
private lemma liftExchange_tensor_aux
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (α : M.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
        L((j'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      L((j.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ N.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (hα : ∀ A B, L((j'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        (M.tensorMap (Profinite.padicAlgClRingObj ℓ) A B) ≫ α.app (A ⊗ B) ≫
          (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
            (Functor.OplaxMonoidal.δ L((j.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) A B) =
      Functor.OplaxMonoidal.δ L((j'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) _ _ ≫
        (α.app A ⊗ₘ α.app B) ≫ N.tensorMap (Profinite.padicAlgClRingObj ℓ) _ _)
    (β : boundedConstructibleNearbyCycles hM ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j' ⟶
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
          boundedConstructibleNearbyCycles hN)
    (hβ : β = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _) α
        (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ j' K)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ j K))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (β.app A ⊗ₘ β.app B) ≫ boundedConstructibleTensorMap hN _ _ ≫
        (boundedConstructibleNearbyCycles hN).map (Functor.LaxMonoidal.μ
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j) A B) =
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j')
          _ _ ≫ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
          (boundedConstructibleTensorMap hM A B) ≫ β.app (A ⊗ B) := by
  subst hβ
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    μ_boundedConstructibleUpperStar_hom, ObjectProperty.tensorHom_hom', liftExchange_app_hom]
  exact Verdier.lax_of_oplax_aux (M.tensorMap _) (N.tensorMap _) (fun A ↦ α.app A) A.obj B.obj
    (hα A.obj B.obj)

/-- **The pullback exchange is monoidal on bounded constructible complexes**: the restriction of
`NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`, in the lax form. -/
lemma Hom.boundedConstructiblePullbackExchange_tensor
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((φ.boundedConstructiblePullbackExchange ℓ hN hM).app A ⊗ₘ
        (φ.boundedConstructiblePullbackExchange ℓ hN hM).app B) ≫
        boundedConstructibleTensorMap hN _ _ ≫
          (boundedConstructibleNearbyCycles hN).map (Functor.LaxMonoidal.μ
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j) A B) =
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j')
          _ _ ≫ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
          (boundedConstructibleTensorMap hM A B) ≫
        (φ.boundedConstructiblePullbackExchange ℓ hN hM).app (A ⊗ B) :=
  liftExchange_tensor_aux hN hM (φ.pullbackExchange _)
    (φ.map_tensorMap_comp_pullbackExchange_app _) _
    (φ.boundedConstructiblePullbackExchange_eq_liftExchange' hN hM) A B

/-- **Nearby duality and open restriction, on bounded constructible complexes** (blueprint
`lemma-nearby-duality-proper-direct-image` (2)): for a morphism of models `φ : N ⟶ M` over `j`, `j'`
whose pullback exchange is given, dualizing maps `θ_M`, `θ_N` compatible with the identifications
`ρ : j^* ω ⟶ ω_N`, `ρ' : j'^* ω' ⟶ ω'_N`, the restriction of the duality map of `M` is identified
with the duality map of `N`. -/
theorem nearbyDualityMap_restrict_boundedConstructible
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) (hM :
        M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    {ωX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {ωX' :
        Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {ωY : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj
            ℓ⟧}
    {ωY' : Dᵇc(Y'.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (θX : (boundedConstructibleNearbyCycles
        hM).obj ωX ⟶ ωX')
    (θY : (boundedConstructibleNearbyCycles hN).obj ωY ⟶ ωY')
    (ρ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj ωX ⟶ ωY)
    (ρ' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').obj ωX' ⟶ ωY')
    (hθ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map θX ≫ ρ' =
      (φ.boundedConstructiblePullbackExchange ℓ hN hM).app ωX ≫
        (boundedConstructibleNearbyCycles hN).map ρ ≫ θY)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
        (Verdier.nearbyDualityMap (boundedConstructibleTensorMap hM) θX K) ≫
        Verdier.nearbyDualityMap (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar
            (Profinite.padicAlgClRingObj ℓ) ℓ j'))
          ρ' ((boundedConstructibleNearbyCycles hM).obj K) =
      (φ.boundedConstructiblePullbackExchange ℓ hN hM).app _ ≫
        (boundedConstructibleNearbyCycles hN).map (Verdier.nearbyDualityMap
          (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              j)) ρ K) ≫
        Verdier.nearbyDualityMap (boundedConstructibleTensorMap hN) θY
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
        (MonoidalClosed.pre ((φ.boundedConstructiblePullbackExchange ℓ hN hM).app K)).app ωY' :=
  Verdier.nearbyDualityMap_restrict_natTrans _ _ θX θY ρ ρ'
    (fun x y ↦ boundedConstructibleTensorMap_natural hN x y)
    (φ.boundedConstructiblePullbackExchange ℓ hN hM)
    (fun A B ↦ φ.boundedConstructiblePullbackExchange_tensor hN hM A B) hθ K

section OpenIhom

variable {V W : Over (Spec (.of k'))} [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
  [IsSeparated V.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  (i : V ⟶ W) [IsOpenImmersion i.left]

-- the instance search goes through the instances on `Mod (Sheaf (ProEt.topology X) Ab) _`
/-- The projection map of `j_! ⊣ Lj^*` on `Dᵇc` is invertible
(`isIso_projectionMap_boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction`),
for the monoidal structure `ObjectProperty.fullMonoidalSubcategory` of `Dᵇc`. -/
private lemma isIso_projectionMap_openImmersion_aux
    (A : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Functor.Monoidal.projectionMap
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj
          ℓ) ℓ i) A) := by
  set adj := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ i
  have hη (T : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : IsIso (adj.unit.app T) := by
    have : IsIso ((boundedConstructible _).ι.map (adj.unit.app T)) := by
      simp only [adj, boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction,
        Adjunction.map_restrictFullyFaithful_unit_app]
      have := NatIso.isIso_app_of_isIso
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' (Profinite.padicAlgClRingObj
            ℓ) i.left).unit
        ((boundedConstructible _).ι.obj T)
      exact IsIso.comp_isIso' this inferInstance
    exact isIso_of_reflects_iso _ (boundedConstructible _).ι
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun T ↦ ?_
  have hε : IsIso (adj.counit.app (A ⊗ (boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
      T)) := by
    have : IsIso ((boundedConstructible _).ι.map (adj.counit.app
        (A ⊗ (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            T))) := by
      simp only [adj, boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction,
        Adjunction.map_restrictFullyFaithful_counit_app]
      have :=
        isIso_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction_counit_app_tensorObj
          (Profinite.padicAlgClRingObj ℓ) i.left A.obj T.obj
      exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance this)
    exact isIso_of_reflects_iso _ (boundedConstructible _).ι
  have := hη T
  dsimp only [Functor.Monoidal.projectionMap]
  infer_instance

/-- The comparison `j^* D ⟶ D j^*` of the duality functors along an open immersion `j`, for an
isomorphism `ρ : j^* ω ≅ ω'`, is an isomorphism: it is the internal-hom comparison of `j^*`, which
is invertible, followed by `ρ`. -/
lemma isIso_nearbyDualityMap_upperStar_of_isOpenImmersion {Ω :
    Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {Ω' : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (ρ : (boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ i).obj Ω ≅ Ω')
    (A : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap (Functor.LaxMonoidal.μ
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i)) ρ.hom A) := by
  rw [Verdier.nearbyDualityMap_eq_ihomComparison]
  have := isIso_projectionMap_openImmersion_aux (ℓ := ℓ) i
  have := Functor.Monoidal.isIso_ihomComparison_of_isIso_projectionMap
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        ℓ i) A
  infer_instance

end OpenIhom

variable (ℓ) [IsSepClosed k'] [Algebra k k'] [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **Nearby duality and open restriction** (blueprint `lemma-nearby-duality-proper-direct-image`
(2)): for a morphism `φ : N ⟶ M` of trait models over the base, over open immersions `j : Y ⟶ X` and
`j' : Y' ⟶ X'`, whose map of total spaces is an open immersion compatible with the structure
morphisms and whose square of geometric generic fibres is cartesian, the restriction `j'^* δ_{M,K}`
of the duality map of `M` is an isomorphism if and only if the duality map `δ_{N, j^* K}` of `N`
is: they are identified up to isomorphisms by `nearbyDualityMap_restrict_boundedConstructible`,
since the pullback exchange is invertible and `j^*` commutes with internal homs. -/
theorem isIso_map_nearbyDualityMap_iff_of_isOpenImmersion (D : NearbyDualizingData k k' ℓ)
    (hM : M.IsTraitModelOfBase k q g)
    (hN : N.IsTraitModelOfBase k qN gN) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : qN = φ.total ≫ q)
    (hg : gN = φ.generic ≫ g) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
        (nearbyDualityMap ℓ D hM K)) ↔
      IsIso (nearbyDualityMap ℓ D hN
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) := by
  have e := nearbyDualityMap_restrict_boundedConstructible φ (hN.preservesBoundedConstructible ℓ)
    (hM.preservesBoundedConstructible ℓ) (D.θ hM)
    (D.θ hN) (dualizingComplexUpperStarIso ℓ j).hom
    (dualizingComplexUpperStarIso ℓ j').hom
    (D.map_θ_comp_dualizingComplexUpperStarIso hM hN j j' φ hφ hq hg)
    K
  have : IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    φ.isIso_pullbackExchange_of_isOpenImmersion _ hφ
  have : IsIso (φ.boundedConstructiblePullbackExchange ℓ (hN.preservesBoundedConstructible ℓ)
      (hM.preservesBoundedConstructible ℓ)) :=
    φ.isIso_boundedConstructiblePullbackExchange ℓ _ _
  have := isIso_nearbyDualityMap_upperStar_of_isOpenImmersion j' (dualizingComplexUpperStarIso ℓ j')
    ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible ℓ)).obj K)
  have := isIso_nearbyDualityMap_upperStar_of_isOpenImmersion j (dualizingComplexUpperStarIso ℓ j) K
  rw [← isIso_comp_right_iff _ (Verdier.nearbyDualityMap (Functor.LaxMonoidal.μ
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j'))
    (dualizingComplexUpperStarIso ℓ j').hom
    ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible ℓ)).obj K))]
  unfold nearbyDualityMap
  rw [e, isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
