/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
import WeilConjectures.CategoryTheory.ProductShift.ProductCommShift
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.SmoothPurity.Completed.CompletedScalarShiftDescent

/-! Auxiliary signed shifts for every integral pullback.
(blueprint: lem-sf-automorphism-constructible-stage-equivalence) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

namespace AutomorphismIntegralShiftProof

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem reduction_shift_component (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r i : ℤ) :
    ((unrestrictedIntegralTransition l E Y n).app (P⟦r⟧)).f i =
      ((unrestrictedIntegralTransition l E Y n).app P).f (i + r) := by
  apply unrestrictedReduction_hom_ext l E Y (n + 1) (P.X (i + r))
  intro U s x
  exact ((unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec
    (P⟦r⟧) i U s x).trans
      ((unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec
        P (i + r) U s x).symm

private theorem pullback_shift_component (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r i : ℤ) :
    ((integralOperationsPullbackTransition l E g n).app (P⟦r⟧)).f i =
      ((integralOperationsPullbackTransition l E g n).app P).f (i + r) := by
  apply integralPullback_restricted_hom_ext l E g n
    (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).X (i + r))
    ((integralOperationsLevelPullback l E g n).obj
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X (i + r)))
  intro V x
  have hs := (integralOperationsPullbackTransition_existsUnique l E g n).exists.choose_spec
    (P⟦r⟧) i V x
  have ht := (integralOperationsPullbackTransition_existsUnique l E g n).exists.choose_spec
    P (i + r) V x
  have he := reduction_shift_component l E (Y := Y) n P r i
  rw [he] at hs
  exact hs.trans ht.symm

private abbrev level (n : ℕ) :
    CochainComplex (integralTowerModules.{u, u} l E Y) ℤ ⥤
      CochainComplex (integralTowerModules.{u, u} l E X) ℤ :=
  integralOperationsPullbackLevel.{u, u} l E g n

@[instance_reducible]
private def levelShiftData (n : ℕ) : (level l E g n).CommShift ℤ := by
  letI := unrestrictedIntegralReductionFunctor_additive.{u, u} l E Y n
  letI := integralOperationsLevelPullback_additive.{u, u} l E g n
  let F := unrestrictedIntegralReductionFunctor.{u, u} l E Y n ⋙
    integralOperationsLevelPullback.{u, u} l E g n ⋙
    SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n))
  exact inferInstanceAs ((F.mapHomologicalComplex (.up ℤ)).CommShift ℤ)

private instance level_commShift (n : ℕ) : (level l E g n).CommShift ℤ :=
  levelShiftData l E g n

private abbrev prodFunctor :
    CochainComplex (integralTowerModules.{u, u} l E Y) ℤ ⥤
      CochainComplex (integralTowerModules.{u, u} l E X) ℤ :=
  ProductShift.productFunctor (level l E g)

private instance prod_commShift : (prodFunctor l E g).CommShift ℤ :=
  ProductShift.productCommShift (level l E g)

private def transition : prodFunctor l E g ⟶ prodFunctor l E g where
  app := IntegralCompletedComparison.roosEnd l E g
  naturality P Q f := by
    change Limits.Pi.map
      (fun n ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).map f).app (op n)) ≫
        IntegralCompletedComparison.roosEnd l E g Q = _
    exact (integralOperationsRoos_square
      ((integralOperationsPullbackTowerFunctor.{u, u} l E g).map f)).symm

private theorem product_transition_shift
    {A D : Type*} [Category A] [Category D] [Preadditive D]
    [HasShift A ℤ] [HasShift D ℤ] [HasCountableProducts D]
    [∀ r : ℤ, (shiftFunctor D r).Additive]
    (F : ℕ → A ⥤ D) [∀ n, (F n).CommShift ℤ]
    (τ : ∀ n, F (n + 1) ⟶ F n)
    (hτ : ∀ n, NatTrans.CommShift (τ n) ℤ)
    (U : ProductShift.productFunctor F ⟶ ProductShift.productFunctor F)
    (hU : ∀ (P : A) (n : ℕ), U.app P ≫ Pi.π (fun k ↦ (F k).obj P) n =
      Pi.π (fun k ↦ (F k).obj P) n -
        Pi.π (fun k ↦ (F k).obj P) (n + 1) ≫ (τ n).app P) :
    letI := ProductShift.productCommShift F
    NatTrans.CommShift U ℤ := by
  let := ProductShift.productCommShift F
  let := hτ
  constructor
  intro r
  apply NatTrans.ext
  funext P
  change (ProductShift.productShiftIso F P r).hom ≫ (U.app P)⟦r⟧' =
    U.app (P⟦r⟧) ≫ (ProductShift.productShiftIso F P r).hom
  apply ProductShift.productShift_hom_ext F P r
  intro n
  rw [Category.assoc, ← Functor.map_comp, hU]
  rw [Category.assoc, ProductShift.productShiftIso_π]
  simp only [Functor.map_sub, Functor.map_comp, Preadditive.comp_sub]
  rw [ProductShift.productShiftIso_π, ProductShift.productShiftIso_π_assoc]
  conv_rhs => rw [← Category.assoc, hU]
  simp only [Preadditive.sub_comp, Category.assoc]
  rw [← NatTrans.shift_app_comm (τ n) r P]

private theorem transition_shift :
    let := prod_commShift l E g
    NatTrans.CommShift (transition l E g) ℤ := by
  let := prod_commShift l E g
  apply product_transition_shift
    (level l E g)
    (fun n ↦ integralOperationsPullbackTransition l E g n)
  · intro n
    constructor
    intro r
    apply NatTrans.ext
    funext P
    apply HomologicalComplex.hom_ext
    intro i
    change (𝟙 _) ≫ ((integralOperationsPullbackTransition l E g n).app P).f (i + r) =
      ((integralOperationsPullbackTransition l E g n).app (P⟦r⟧)).f i ≫ 𝟙 _
    simpa only [Category.id_comp, Category.comp_id] using
      (pullback_shift_component l E g n P r i).symm
  · intro P n
    change IntegralCompletedComparison.roosEnd l E g P ≫
        Pi.π (fun k ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj
          (op k)) n = _
    have h := (towerTransitionEndomorphism_eq_iff
      (K := fun n ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj (op n))
      (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E g).obj P))
      _).mp rfl n
    convert h using 1
    congr 2
    simp only [integralOperationsTowerStep, integralOperationsPullbackTowerFunctor,
      Functor.flip, Functor.ofOpSequence_map_homOfLE_succ]

@[instance_reducible]
private def chainShift : (integralOperationsPullbackComplexFunctor l E g).CommShift ℤ := by
  let := prod_commShift l E g
  let := transition_shift l E g
  exact SignedCoconeShift.coconeCommShift _ _ (transition l E g)

private theorem chainShift_coordinates :
    IntegralCompletedComparison.ShiftCoordinates l E g (chainShift l E g) := by
  let := prod_commShift l E g
  let := transition_shift l E g
  intro P r
  constructor
  · intro j
    exact SignedCoconeShift.coconeFunctorShiftIso_inl _ _
      (transition l E g) P r j
  · intro i j h
    exact SignedCoconeShift.coconeFunctorShiftIso_inr _ _
      (transition l E g) P r i j h

end AutomorphismIntegralShiftProof

attribute [local irreducible] AutomorphismIntegralShiftProof.chainShift

/-- Signed Roos shifts exist for every scheme morphism.
Source: the canonical shift paragraph of the Weil-structures proof
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Choose a normalized strict finite pullback tower, apply the signed mapping-cocone
construction, and descend the resulting shift through the derived comparison. -/
theorem automorphismConstructibleStage_integral_shift_data
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∀ (Z W : Scheme.{u}) (g : Z ⟶ W),
      ∃ (c : (integralOperationsPullbackComplexFunctor l E g).CommShift ℤ)
        (d : (integralDerivedPullback l E g).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E g c ∧
          IntegralCompletedComparison.ShiftDescent l E g c d := by
  intro X Y g
  let c := AutomorphismIntegralShiftProof.chainShift l E g
  let := c
  let := WeilConjectures.good_stable l E Y
  let G := integralOperationsGoodComplex.{u, u} l E Y
  let sh (n : ℤ) := G.lift (G.ι ⋙ shiftFunctor _ n)
    (fun P ↦ G.le_shift n _ P.property)
  let shi (n : ℤ) := G.liftCompιIso (G.ι ⋙ shiftFunctor _ n)
    (fun P ↦ G.le_shift n _ P.property)
  let := G.fullyFaithfulι.hasShift sh shi
  let : G.ι.CommShift ℤ :=
    Functor.CommShift.ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi
  have : (integralOperationsGoodLocalization l E Y).EssSurj :=
    WeilConjectures.goodLocalization_essSurj l E Y
  have : ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules.{u, u} l E X))).obj
      (integralOperationsGoodLocalization l E Y)).Full :=
    WeilConjectures.good_whisker_full l E Y _
  have : ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules.{u, u} l E X))).obj
      (integralOperationsGoodLocalization l E Y)).Faithful :=
    WeilConjectures.whiskeringLeft_faithful (integralOperationsGoodLocalization l E Y)
  have : ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules.{u, u} l E X))).obj
      (G.ι ⋙ DerivedCategory.Q)).Full := by
    change ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules.{u, u} l E X))).obj
      (integralOperationsGoodLocalization l E Y)).Full
    infer_instance
  have : ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules.{u, u} l E X))).obj
      (G.ι ⋙ DerivedCategory.Q)).Faithful := by
    change ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules.{u, u} l E X))).obj
      (integralOperationsGoodLocalization l E Y)).Faithful
    infer_instance
  obtain ⟨d, hd⟩ := WeilConjectures.descentShift
    (G.ι ⋙ DerivedCategory.Q)
    (G.ι ⋙ integralOperationsPullbackComplexFunctor l E g ⋙ DerivedCategory.Q)
    (integralDerivedPullback l E g) (integralDerivedPullbackComparison l E g)
    (Functor.FullyFaithful.ofFullyFaithful _)
  refine ⟨c, d, AutomorphismIntegralShiftProof.chainShift_coordinates l E g, ?_⟩
  intro P r
  refine ⟨WeilConjectures.good_shift l E Y P.obj P.property r, ?_⟩
  have h := hd r P
  simp only [Functor.commShiftIso_comp_hom_app,
    Functor.commShiftIso_comp_inv_app] at h
  have hi := Functor.shiftFunctorIso_ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi r
  rw [hi] at h
  simp only [shi, ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app] at h
  erw [DerivedCategory.Q.map_id, Category.comp_id,
    (integralOperationsPullbackComplexFunctor l E g ⋙ DerivedCategory.Q).map_id,
    Category.id_comp] at h
  exact h

end WeilConjectures
