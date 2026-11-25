/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Derived.DerivedComplete

/-! # Comparison of the two augmented reduction towers

Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tags 06YY and 06YL.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u d
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

local instance (priority := 4000) instSfDerivedCompleteLegacyComparison1
    : EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{u} _

open CategoryTheory.Pretriangulated in
private theorem roos_transport {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {X Y : ℕ → C}
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    {K L : C} (e : K ≅ L) (a : ∀ n, X n ≅ Y n)
    (p : ∀ n, K ⟶ X n) (q : ∀ n, L ⟶ Y n)
    (ht : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    (hp : ∀ n, p n ≫ (a n).hom = e.hom ≫ q n)
    (h : ∃ hprod : HasProduct X, letI := hprod
      ∃ δ : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle f K (Pi.lift p) δ) :
    ∃ hprod : HasProduct Y, letI := hprod
      ∃ δ : (∏ᶜ Y) ⟶ L⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle g L (Pi.lift q) δ := by
  obtain ⟨hprod, δ, hδ⟩ := h
  let := hprod
  let : HasProduct Y :=
    hasProduct_of_equiv_of_iso X Y (Equiv.refl ℕ) (fun n ↦ (a n).symm)
  let A : (∏ᶜ X) ≅ (∏ᶜ Y) :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨inferInstance, A.inv ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom, ?_⟩
  apply isomorphic_distinguished _ hδ _
  refine Triangle.isoMk _ _ e.symm A.symm A.symm ?_ ?_ ?_
  · change Pi.lift q ≫ A.inv = e.inv ≫ Pi.lift p
    apply Pi.hom_ext
    intro n
    simp only [A, Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    apply (cancel_mono (a n).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using (congrArg (fun k ↦ e.inv ≫ k) (hp n)).symm
  · exact (towerTransitionEndomorphism_natural_backward g f
      (fun n ↦ (a n).inv) (fun n ↦ by
        apply (cancel_mono (a n).hom).1
        simpa [Category.assoc] using
          congrArg (fun k ↦ (a (n + 1)).inv ≫ k) (ht n))).symm
  · change (A.inv ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom) ≫
      (shiftFunctor C (1 : ℤ)).map e.inv = A.inv ≫ δ
    simp [Category.assoc, ← Functor.map_comp]

private theorem representative_isIso (n : ℕ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y) P) :
    IsIso (sfReductionRepresentativeComparison l E Y n P) := by
  unfold sfReductionRepresentativeComparison
  exact IsIso.comp_isIso'
    (@Functor.map_isIso _ _ _ _ _ _ _ _
      (unrestrictedTowerCounit_isIso.{u, u} l E Y n P hP))
    (NatIso.hom_app_isIso _ _)

private theorem transition_eq (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ) (n : ℕ) :
    integralTowerTransition l E Y D hl P n =
      (NatTrans.mapHomologicalComplex (sfReductionTransition l E Y n) (.up ℤ)).app P := by
  have h := (integralTowerMaps_existUnique l E Y D hl P).unique
    (integralTowerMaps_existUnique l E Y D hl P).exists.choose_spec
    (y₂ := (integralTowerUnit l E Y D hl P,
      fun m ↦ (NatTrans.mapHomologicalComplex (sfReductionTransition l E Y m)
        (.up ℤ)).app P))
  apply congrArg (fun z ↦ z.2 n) (h ?_)
  refine ⟨(integralTowerMaps_existUnique l E Y D hl P).exists.choose_spec.1, ?_⟩
  intro m i U a x
  exact (sfReductionTransition_existsUnique l E Y m).exists.choose_spec (P.X i) U a x

private theorem unit_eq (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ) (n : ℕ) :
    integralTowerUnit l E Y D hl P n = unrestrictedTowerUnit.{u, u} l E Y P n := by
  ext i U x
  exact ((integralTowerMaps_existUnique l E Y D hl P).exists.choose_spec.1 n i U x).trans
    (unrestrictedTowerUnit_condition.{u, u} l E Y P n i U x).symm

private theorem representative_unit (n : ℕ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y) P) :
    (sfDerivedReductionUnit l E Y n).app (DerivedCategory.Q.obj P) ≫
      sfReductionRepresentativeComparison l E Y n P =
      DerivedCategory.Q.map (unrestrictedTowerUnit.{u, u} l E Y P n) := by
  have h := (derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose_spec P hP
  have hu := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
    (scalarReductionExtension_adjunction.{u, u} l E Y n).choose P
  have hq : DerivedCategory.Qh.map
      (((scalarReductionExtension_adjunction.{u, u} l E Y n).choose.mapHomotopyCategory
        (.up ℤ)).unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Q.map (unrestrictedTowerUnit.{u, u} l E Y P n) := by
    exact congrArg (DerivedCategory.Qh.map) hu
  exact h.trans hq

private theorem roos_iff {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {X Y : ℕ → C}
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    {K : C} (a : ∀ n, X n ≅ Y n)
    (p : ∀ n, K ⟶ X n) (q : ∀ n, K ⟶ Y n)
    (ht : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    (hp : ∀ n, p n ≫ (a n).hom = q n) :
    (∃ hprod : HasProduct X, letI := hprod
      ∃ δ : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle f K (Pi.lift p) δ) ↔
    (∃ hprod : HasProduct Y, letI := hprod
      ∃ δ : (∏ᶜ Y) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle g K (Pi.lift q) δ) := by
  constructor
  · exact roos_transport f g (Iso.refl K) a p q ht (by simpa using hp)
  · apply roos_transport g f (Iso.refl K) (fun n ↦ (a n).symm) q p
    · intro n
      apply (cancel_epi (a (n + 1)).hom).1
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ (a n).inv) (ht n).symm
    · intro n
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ (a n).inv) (hp n).symm

private theorem resolution_completeness (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    {P G : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ}
    (q : P ⟶ G)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients.{u + 1, u, u + 1}
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y) q)
    {K : DerivedCategory (scalarReductionSource.{u, u} l E Y)}
    (e : DerivedCategory.Q.obj G ≅ K) :
    IsSfDerivedComplete l E Y K ↔
      ∃ hprod : HasProduct
          (fun n : ℕ ↦ (integralReductionTower l E Y D hl P).obj (op n)),
        letI : HasProduct
            (fun n : ℕ ↦ (integralReductionTower l E Y D hl P).obj (op n)) := hprod
        ∃ δ : (∏ᶜ fun n : ℕ ↦ (integralReductionTower l E Y D hl P).obj (op n)) ⟶
            K⟦(1 : ℤ)⟧,
          IsDerivedLimitTriangle
            (K := fun n : ℕ ↦ (integralReductionTower l E Y D hl P).obj (op n))
            (fun n : ℕ ↦ (integralReductionTower l E Y D hl P).map (homOfLE n.le_succ).op)
            K (Pi.lift (f := fun n : ℕ ↦
              (integralReductionTower l E Y D hl P).obj (op n)) (fun n : ℕ ↦
              ((integralReductionTowerCone l E Y D hl q hq).extend e.inv).π.app (op n)))
            δ := by
  let r : DerivedCategory.Q.obj P ≅ K := integralTowerAugmentationIso l E Y D hl q hq ≪≫ e
  let a (n : ℕ) : (sfDerivedReductionRestricted l E Y n).obj K ≅
      (integralReductionTower l E Y D hl P).obj (op n) :=
    (sfDerivedReductionRestricted l E Y n).mapIso r.symm ≪≫
      @asIso _ _ _ _ (sfReductionRepresentativeComparison l E Y n P)
        (representative_isIso l E Y n P hq.2)
  apply roos_iff _ _ a
  · intro n
    change (sfDerivedReductionTransition l E Y n).app K ≫
      (sfDerivedReductionRestricted l E Y n).map r.inv ≫
        sfReductionRepresentativeComparison l E Y n P =
      ((sfDerivedReductionRestricted l E Y (n + 1)).map r.inv ≫
        sfReductionRepresentativeComparison l E Y (n + 1) P) ≫ _
    erw [← Category.assoc, ← (sfDerivedReductionTransition l E Y n).naturality r.inv,
      Category.assoc]
    erw [(sfDerivedReductionTransition_existsUnique l E Y n).exists.choose_spec P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hq.2)]
    have hm : (integralReductionTower l E Y D hl P).map (homOfLE n.le_succ).op =
        DerivedCategory.Q.map (integralTowerTransition l E Y D hl P n) :=
      Functor.ofOpSequence_map_homOfLE_succ _ n
    erw [hm, transition_eq l E Y D hl P n]
    exact (Category.assoc _ _ _).symm
  · intro n
    change (sfDerivedReductionUnit l E Y n).app K ≫
      (sfDerivedReductionRestricted l E Y n).map r.inv ≫
        sfReductionRepresentativeComparison l E Y n P = _
    erw [← Category.assoc, ← (sfDerivedReductionUnit l E Y n).naturality r.inv,
      Category.assoc, representative_unit l E Y n P hq.2]
    change (e.inv ≫ (integralTowerAugmentationIso l E Y D hl q hq).inv) ≫
      DerivedCategory.Q.map _ = e.inv ≫
        ((integralTowerAugmentationIso l E Y D hl q hq).inv ≫ DerivedCategory.Q.map _)
    exact (Category.assoc _ _ _).trans (congrArg
      (fun f ↦ e.inv ≫ (integralTowerAugmentationIso l E Y D hl q hq).inv ≫
        DerivedCategory.Q.map f) (unit_eq l E Y D hl P n).symm)

/-- Intrinsic derived completeness agrees with the K-flat augmented-tower definition.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tags 06YY and 06YL
(blueprint: lem-sf-derived-complete-legacy-comparison).
Proof: choose a K-flat representative. The derived tensor counits identify the intrinsic
reductions with the ordinary tensor complexes. The normalized derived adjunction identifies
its unit with the localized chain unit. Uniqueness on pure tensors identifies the transitions.
The resulting isomorphism of augmented towers induces an isomorphism of their product Roos
triangles, which preserves distinguishedness. Every derived object has such a representative,
so the same argument gives both implications. -/
theorem sfDerivedComplete_iff_legacy (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y)) :
    IsSfDerivedComplete l E Y K ↔ IsDerivedComplete l E Y D hl K := by
  constructor
  · intro hK
    let G := DerivedCategory.Q.objPreimage K
    let e : DerivedCategory.Q.obj G ≅ K := DerivedCategory.Q.objObjPreimageIso K
    obtain ⟨P, q, hP, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y) G
    have hres : CochainComplex.IsKFlatResolutionIndependentCoefficients
        (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y) q := ⟨hq, hP⟩
    exact ⟨P, G, q, hres, e, (resolution_completeness l E Y D hl q hres e).mp hK⟩
  · rintro ⟨P, G, q, hq, e, hK⟩
    exact (resolution_completeness l E Y D hl q hq e).mpr hK

end WeilConjectures
