/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedReductionAugmentationIso
import WeilConjectures.SmoothPurity.IntegralOnSlice.IsomorphismOrdinaryCompletionChain
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Generic tower augmentation and its mapping-cocone coordinates

The existing generic construction is separated from coefficient specialization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.FrobeniusCoefficientTwists
attribute [local instance_reducible] integralOperationsRoosFunctor integralOperationsRoos
attribute [local irreducible] CochainComplex.mappingCocone.fst CochainComplex.mappingCocone.snd

section AugmentationGeneric
universe a b c d
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {C : Type c} [Category.{d} C]

omit [HasCountableProducts A] in
/-- The two mapping-cocone coordinates determine an incoming chain map.
Source: Mathlib mappingCocone.id_X and the augmentation proof in coefficient-twist clause 4.
(blueprint: lem-weil-frobenius-augmentation-cocone-ext).
Proof: in each degree insert the identity decomposed through the two projections
and inclusions. The two hypotheses identify the resulting summands. Chain-map
extensionality then gives the asserted equality. -/
theorem augmentationCocone_ext {K L M : CochainComplex A ℤ} (phi : K ⟶ L)
    {f g : M ⟶ CochainComplex.mappingCocone phi}
    (hfst : f ≫ CochainComplex.mappingCocone.fst phi =
      g ≫ CochainComplex.mappingCocone.fst phi)
    (hsnd : ∀ i : ℤ, f.f i ≫ (CochainComplex.mappingCocone.snd phi).v
        i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd phi).v i (i - 1) (by omega)) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := CochainComplex.mappingCocone.id_X phi i (i - 1) (by omega)
  have hf := congrArg (fun k ↦ k.f i) hfst
  change f.f i ≫ _ = g.f i ≫ _ at hf
  calc
    f.f i = f.f i ≫ 𝟙 _ := by rw [Category.comp_id]
    _ = f.f i ≫ ((CochainComplex.mappingCocone.fst phi).f i ≫
        (CochainComplex.mappingCocone.inl phi).v i i (by omega) +
        (CochainComplex.mappingCocone.snd phi).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr phi).1.v (i - 1) i (by omega)) := by rw [h]
    _ = g.f i ≫ ((CochainComplex.mappingCocone.fst phi).f i ≫
        (CochainComplex.mappingCocone.inl phi).v i i (by omega) +
        (CochainComplex.mappingCocone.snd phi).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr phi).1.v (i - 1) i (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, hf, hsnd]
    _ = g.f i := by rw [h, Category.comp_id]

variable (F : C ⥤ CochainComplex A ℤ) (T : C ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ))
  (a : F ⋙ (Functor.const ℕᵒᵖ : CochainComplex A ℤ ⥤ _) ⟶ T)

private def productAug (P : C) :
    F.obj P ⟶ ∏ᶜ (fun n : ℕ ↦ (T.obj P).obj (op n)) :=
  Pi.lift (fun n ↦ (a.app P).app (op n))

private theorem productAug_condition (P : C) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain (F.obj P)
        (∏ᶜ (fun n : ℕ ↦ (T.obj P).obj (op n))) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (productAug F T a P ≫ towerTransitionEndomorphism
          (K := fun n : ℕ ↦ (T.obj P).obj (op n)) (integralOperationsTowerStep (T.obj P))) = 0 := by
  have h : productAug F T a P ≫ towerTransitionEndomorphism
      (K := fun n : ℕ ↦ (T.obj P).obj (op n)) (integralOperationsTowerStep (T.obj P)) = 0 := by
    apply Pi.hom_ext
    intro n
    have hn := (a.app P).naturality (homOfLE (Nat.le_succ n)).op
    simpa [productAug, towerTransitionEndomorphism, towerProductShift,
      integralOperationsTowerStep, Category.assoc] using sub_eq_zero.mpr hn
  rw [h]
  simp

private def chainAug (P : C) : F.obj P ⟶ integralOperationsRoos (T.obj P) :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ (T.obj P).obj (op n))
      (integralOperationsTowerStep (T.obj P)))
    (productAug F T a P) 0 (productAug_condition F T a P)

private theorem chainAug_fst (P : C) :
    chainAug F T a P ≫ CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ (T.obj P).obj (op n))
          (integralOperationsTowerStep (T.obj P))) = productAug F T a P := by
  exact CochainComplex.mappingCocone.lift_fst _ _ _ _

private theorem chainAug_snd (P : C) (i : ℤ) :
    (chainAug F T a P).f i ≫ (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ (T.obj P).obj (op n))
          (integralOperationsTowerStep (T.obj P)))).v i (i - 1) (by omega) = 0 := by
  exact CochainComplex.mappingCocone.lift_f_snd_v _ _ _ _ i (i - 1) (by omega)

private theorem chainAug_naturality {P Q : C} (f : P ⟶ Q) :
    F.map f ≫ chainAug F T a Q =
      chainAug F T a P ≫ integralOperationsRoosMap (T.map f) := by
  apply augmentationCocone_ext
  · rw [Category.assoc, chainAug_fst, Category.assoc,
      (IntegralAmbient.roosMap_coordinates (T.map f)).1, ← Category.assoc, chainAug_fst]
    apply Pi.hom_ext
    intro n
    simp only [productAug, Category.assoc, Pi.lift_comp_π, Pi.map_π, Pi.lift_comp_π_assoc]
    exact congrArg (fun t ↦ t.app (op n)) (a.naturality f)
  · intro i
    rw [HomologicalComplex.comp_f, Category.assoc, chainAug_snd, comp_zero,
      HomologicalComplex.comp_f, Category.assoc,
      (IntegralAmbient.roosMap_coordinates (T.map f)).2 i (i - 1) (by omega),
      ← Category.assoc, chainAug_snd, zero_comp]

private theorem chainAug_precomp (G : C ⥤ CochainComplex A ℤ) (b : G ⟶ F) (P : C) :
    chainAug G T (Functor.whiskerRight b (Functor.const ℕᵒᵖ) ≫ a) P =
      b.app P ≫ chainAug F T a P := by
  apply augmentationCocone_ext
  · rw [chainAug_fst, Category.assoc, chainAug_fst]
    apply Pi.hom_ext
    intro n
    simp only [productAug, Category.assoc, Pi.lift_comp_π]
    rfl
  · intro i
    rw [chainAug_snd, HomologicalComplex.comp_f, Category.assoc, chainAug_snd, comp_zero]

private def towerAugmentation : F ⟶ T ⋙ integralOperationsRoosFunctor where
  app := chainAug F T a
  naturality _ _ f := chainAug_naturality F T a f

attribute [local irreducible] productAug chainAug

end AugmentationGeneric

section AugmentationIsIso
universe u
open AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
private instance (priority := 4000) augmentationSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived
attribute [local irreducible] HasDerivedCategory.standard proEtaleRingModulePullback
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  IntegralOnSlice.ordinaryPull IntegralOnSlice.ordinaryAdjunction Scheme.residueField Padic
  completedIntegralCoefficientSheafUnrestricted MorphismProperty.Over.pullback constantSheaf
  Functor.mapHomologicalComplex DerivedCategory.Q
attribute [local instance_reducible] PurCompactSupport.completed IntegralOnSlice.Site
  IntegralOnSlice.topology IntegralOnSlice.restrict IntegralOnSlice.ring
  IntegralOnSlice.ordinaryComplexPull integralOperationsPullbackComplexFunctor
attribute [local irreducible] IntegralOnSlice.roosUnit
  IntegralOnSlice.ordinaryCompletionChain integralOperationsPullbackComplexFunctor
  integralOperationsRoos
attribute [local instance_reducible] IntegralOnSlice.roos
private theorem exactFunctor_Q_map_isIso {A B : Type*}
    [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (h : IsIso (DerivedCategory.Q.map f)) :
    IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f)) := by
  let δ := F.mapDerivedCategoryFactors
  change IsIso ((F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map f)
  rw [← NatIso.naturality_1 δ f]
  let := h
  exact IsIso.comp_isIso' (δ.app P).isIso_inv
    (IsIso.comp_isIso' (Functor.map_isIso F.mapDerivedCategory (DerivedCategory.Q.map f))
      (δ.app Q).isIso_hom)

private theorem map_comp_isIso_of_eq {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y Z : A} (f : X ⟶ Z) (a : X ⟶ Y) (b : Y ⟶ Z)
    (h : f = a ≫ b) (ha : IsIso (F.map a)) (hb : IsIso (F.map b)) :
    IsIso (F.map f) := by
  rw [h, Functor.map_comp]
  exact IsIso.comp_isIso' ha hb

private theorem auxiliaryDatum (l : ℕ) : ∃ D : FiniteFieldDatum.{0}, l ≠ D.p := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p, a := 1, q := p, prime := hprime, exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  refine ⟨D, ?_⟩
  change l ≠ p
  omega

/-- The exact ordinary inverse image carries the completeness unit to the specified
augmentation. A natural-isomorphism comparison and a chain factorization suffice;
no choice of the augmentation is used here.
Source: expanded DAG definition clause 4 and lem-weil-isomorphism-derived-pullback.
Proof: apply exact inverse image to the invertible completeness unit, then use the
ordinary completion-chain comparison and the given augmentation factorization. -/
private theorem augmentation_isIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (C : CochainComplex (integralTowerModules l E Y) ℤ)
    (hC : integralOperationsGoodComplex l E Y C)
    (hK : sfIntegralConstructible l E Y (DerivedCategory.Q.obj C))
    (F₀ : IntegralOnSlice.Mod l E Y none ⥤ IntegralOnSlice.Mod l E X none)
    [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    (e₀ : F₀ ≅ IntegralOnSlice.ordinaryPull l E g)
    (α : F₀.mapHomologicalComplex (.up ℤ) ⟶ integralOperationsPullbackComplexFunctor l E g)
    (γ : F₀.mapHomologicalComplex (.up ℤ) ⟶ IntegralOnSlice.ordinaryComplexPull l E g)
    (hγ : IsIso (γ.app C))
    (hα : α.app C = γ.app C ≫ IntegralOnSlice.ordinaryCompletionChain l E g C) :
    IsIso (DerivedCategory.Q.map (α.app C)) := by
  classical
  let : HasDerivedCategory
      (X.proEtaleRingModules ((PurCompactSupport.completed l E).ring X)) :=
    integralTowerHasDerivedCategory l E X
  obtain ⟨D, hl⟩ := auxiliaryDatum l
  have hcomplete : IsDerivedCompleteUnrestricted l E Y (DerivedCategory.Q.obj C) :=
    ⟨D, hl, (sfDerivedComplete_iff_legacy l E Y D hl _).mp hK.1⟩
  have hroos : IsIso (DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E Y none C)) := by
    have h := CompletedCoefficientPushforward.complete_roosUnit l E Y
      (DerivedCategory.Q.obj C) C hC.1 (Iso.refl _) hcomplete
    change IsIso ((𝟙 (DerivedCategory.Q.obj C)) ≫
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E Y none C)) at h
    simpa only [Category.id_comp] using h
  let F := IntegralOnSlice.ordinaryPull l E g
  let : F.Additive := Functor.additive_of_iso e₀
  let : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso e₀
  let : PreservesFiniteColimits F := preservesFiniteColimits_of_natIso e₀
  have hm : IsIso (DerivedCategory.Q.map
      ((IntegralOnSlice.ordinaryComplexPull l E g).map
        (IntegralOnSlice.roosUnit l E Y none C))) := by
    exact exactFunctor_Q_map_isIso F (IntegralOnSlice.roosUnit l E Y none C) hroos
  obtain ⟨e, he⟩ := IntegralOnSlice.isomorphismOrdinaryCompletionChain l E g C
  let QX : CochainComplex (integralTowerModules l E X) ℤ ⥤
      DerivedCategory (integralTowerModules l E X) := DerivedCategory.Q
  have hc : IsIso (DerivedCategory.Q.map (IntegralOnSlice.ordinaryCompletionChain l E g C)) :=
    map_comp_isIso_of_eq QX (IntegralOnSlice.ordinaryCompletionChain l E g C)
      ((IntegralOnSlice.ordinaryComplexPull l E g).map
        (IntegralOnSlice.roosUnit l E Y none C)) e.hom he.symm hm
      (QX.mapIso e).isIso_hom
  have hγ' : IsIso (QX.map (γ.app C)) :=
    (QX.mapIso (@asIso _ _ _ _ (γ.app C) hγ)).isIso_hom
  exact map_comp_isIso_of_eq QX _ _ _ hα hγ' hc

end AugmentationIsIso

end WeilConjectures.FrobeniusCoefficientTwists
