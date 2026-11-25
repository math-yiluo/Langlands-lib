/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Derived.DerivedComplete
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRRoosFiniteReduction
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatReductionModel
import Mathlib.Algebra.Homology.Functor

/-! # Effectivity of normalized DVR towers

Source: Weil conjectures blueprint, chap-The-six-operations-on-Dbctf, sk-prop-sf-biduality-general,
order 2132 (blueprint: lemma-sp-tower-adjunction-foundation--2).

The derived limit is specified by its Roos triangle on actual derived evaluations.
Comparisons are adjoints of the specified limit projections. Coherence is an equality
in the finite-coefficient derived category, including both identity and longer quotient
maps. No constructibility, boundedness, or Tor-amplitude hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  normalizedDVRResCompletedComp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The canonical size witness, registered only in this file. -/
abbrev normalizedDVREffectivityLocal1 :
    EssentiallySmall.{max u (t + 1)} X.ProEt :=
  essentiallySmallSelf.{u} X.ProEt
attribute [local instance 4000] normalizedDVREffectivityLocal1
/-- Canonical abelian sheafification, registered only in this file. -/
abbrev normalizedDVREffectivityLocal2 :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
attribute [local instance] normalizedDVREffectivityLocal2
/-- The canonical locally bijective sheafification criterion, registered locally. -/
abbrev normalizedDVREffectivityLocal3 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
attribute [local instance] normalizedDVREffectivityLocal3

/-- The actual completed-coefficient tensor-restriction adjunction, normalized on
K-flat representatives by the tensor unit x ↦ x tensor 1.
Source: Stacks Tags 06YY and 0DVC; blueprint order 2132
(blueprint: lemma-sp-tower-adjunction-foundation--2). -/
def normalizedDVRIntegralAdjunction (n : ℕ) :
    scalarReductionDerivedExtension l E X n ⊣ scalarReductionDerivedRestriction l E X n :=
  (derivedScalarExtensionRestrictionAdjunction l E X n).choose

/-- The canonical reduction transition is adjoint to the smaller quotient unit,
transported through the canonical composition comparison for restrictions.
Source: blueprint order 2132, last proof paragraph
(blueprint: lemma-sp-tower-adjunction-foundation--2). -/
def normalizedDVRReductionTransition (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m)
    (M : completedIntegralDerivedCategory l E X D hl) :
    (scalarReductionDerivedExtension l E X m).obj M ⟶
      (normalizedDVRRes l E X h).obj
        ((scalarReductionDerivedExtension l E X n).obj M) :=
  ((normalizedDVRIntegralAdjunction l E X m).homEquiv M _).symm
    ((normalizedDVRIntegralAdjunction l E X n).unit.app M ≫
      (normalizedDVRResCompletedComp l E X D hl h).inv.app
        ((scalarReductionDerivedExtension l E X n).obj M))

/-- The counit comparison at a finite level is the adjoint of that limit projection.
Source: blueprint order 2132, comparison in the statement
(blueprint: lemma-sp-tower-adjunction-foundation--2). -/
def normalizedDVRCounitComparison (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj M ⟶ T.M n :=
  ((normalizedDVRIntegralAdjunction l E X n).homEquiv M (T.M n)).symm
    (p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom)

attribute [local irreducible] normalizedDVRIntegralAdjunction
  scalarReductionExtension scalarReductionDerivedExtension scalarReductionCounit
  normalizedDVRKFlatComparison

private theorem adjacentRoosProjection
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle f L p δ) (n : ℕ) :
    p ≫ Pi.π K (n + 1) ≫ f n = p ≫ Pi.π K n := by
  have hz : p ≫ towerTransitionEndomorphism f = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₁₂ _ hc
  have hn := congrArg (fun a ↦ a ≫ Pi.π K n) hz
  simp only [towerTransitionEndomorphism, Preadditive.comp_sub, Category.comp_id,
    Preadditive.sub_comp, Category.assoc, towerProductShift, Pi.lift_comp_π,
    zero_comp] at hn
  exact (sub_eq_zero.mp hn).symm

private theorem adjointTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    {M : C} {P : A} {Q : B} (a : M ⟶ Rm.obj P) (b : M ⟶ Rn.obj Q)
    (v : P ⟶ S.obj Q) (h : a ≫ Rm.map v ≫ e.hom.app Q = b) :
    (am.homEquiv M P).symm a ≫ v =
      (am.homEquiv M (S.obj (Ln.obj M))).symm
          (an.unit.app M ≫ e.inv.app (Ln.obj M)) ≫
        S.map ((an.homEquiv M Q).symm b) := by
  apply (am.homEquiv M (S.obj Q)).injective
  rw [am.homEquiv_naturality_right, Equiv.apply_symm_apply,
    am.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply (cancel_mono (e.hom.app Q)).1
  simp only [Category.assoc]
  have he := e.hom.naturality ((an.homEquiv M Q).symm b)
  dsimp only [Functor.comp_map] at he
  rw [he]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← an.homEquiv_unit, Equiv.apply_symm_apply]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDVRTransition_comp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    normalizedDVRTowerTransition l E X D hl hrm ≫
        normalizedDVRTowerTransition l E X D hl hmn =
      normalizedDVRTowerTransition l E X D hl (le_trans hmn hrm) := by
  dsimp only [normalizedDVRTowerTransition]
  rw [Localization.comp_liftNatTrans]
  congr 1
  ext K
  change DerivedCategory.Q.map (K.asFunctor.map (homOfLE hrm).op) ≫
    DerivedCategory.Q.map (K.asFunctor.map (homOfLE hmn).op) =
    DerivedCategory.Q.map (K.asFunctor.map (homOfLE (le_trans hmn hrm)).op)
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDVRTransition_refl (n : ℕ) :
    normalizedDVRTowerTransition l E X D hl (Nat.le_refl n) =
      𝟙 (normalizedDVRTowerEvaluation l E X D hl n) := by
  have he : (evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E X D hl)).map
      (homOfLE (Nat.le_refl n)).op = 𝟙 _ :=
    (evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E X D hl)).map_id (op n)
  dsimp only [normalizedDVRTowerTransition]
  rw [he, NatTrans.mapHomologicalComplex_id, Functor.whiskerRight_id',
    Localization.liftNatTrans_id]

private theorem normalizedDVRRoosProjection (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
      M p δ) {m n : ℕ} (h : n ≤ m) :
    p ≫ Pi.π _ m ≫ (normalizedDVRTowerTransition l E X D hl h).app T.tower =
      p ≫ Pi.π _ n := by
  induction m, h using Nat.le_induction with
  | base => simp only [normalizedDVRTransition_refl, NatTrans.id_app, Category.comp_id]
  | succ m h ih =>
    rw [← normalizedDVRTransition_comp l E X D hl m.le_succ h, NatTrans.comp_app]
    calc
      _ = (p ≫ Pi.π _ (m + 1) ≫
          (normalizedDVRTowerTransition l E X D hl m.le_succ).app T.tower) ≫
          (normalizedDVRTowerTransition l E X D hl h).app T.tower := by
        simp only [Category.assoc]
      _ = _ := by rw [adjacentRoosProjection _ M p δ hc m]
                  simpa only [Category.assoc] using ih

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDVRCounitComparison_coherent
    (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
      M p δ) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRCounitComparison l E X D hl T M p m ≫ T.tau h =
      normalizedDVRReductionTransition l E X D hl h M ≫
        (normalizedDVRRes l E X h).map
          (normalizedDVRCounitComparison l E X D hl T M p n) := by
  apply adjointTransition (normalizedDVRIntegralAdjunction l E X m)
    (normalizedDVRIntegralAdjunction l E X n) (normalizedDVRRes l E X h)
    (normalizedDVRResCompletedComp l E X D hl h)
  simp only [Category.assoc]
  change p ≫ Pi.π _ m ≫ (T.evaluationIso m).hom ≫
    (normalizedDVRResCompleted l E X D hl m).map (T.tau h) ≫
      (normalizedDVRResCompletedComp l E X D hl h).hom.app (T.M n) = _
  rw [← T.tower_tau h]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ (T.evaluationIso n).hom)
    (normalizedDVRRoosProjection l E X D hl T M p δ hc h)

open CategoryTheory.Pretriangulated in
private theorem roosTransport
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y : ℕ → C} [HasProduct X]
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    (M : C) (p : M ⟶ ∏ᶜ X) (δ : (∏ᶜ X) ⟶ M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle f M p δ)
    (a : ∀ n, X n ≅ Y n) (q : ∀ n, M ⟶ Y n)
    (ht : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    (hp : ∀ n, p ≫ Pi.π X n ≫ (a n).hom = q n) :
    ∃ hprod : HasProduct Y, letI := hprod
      ∃ δ' : (∏ᶜ Y) ⟶ M⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle g M (Pi.lift q) δ' := by
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
  refine ⟨inferInstance, A.inv ≫ δ, ?_⟩
  apply isomorphic_distinguished _ hc _
  refine Triangle.isoMk _ _ (Iso.refl M) A.symm A.symm ?_ ?_ ?_
  · change Pi.lift q ≫ A.inv = 𝟙 M ≫ p
    apply Pi.hom_ext
    intro n
    simp only [A, Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π_assoc,
      Category.id_comp]
    apply (cancel_mono (a n).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using (hp n).symm
  · exact (towerTransitionEndomorphism_natural_backward g f
      (fun n ↦ (a n).inv) (fun n ↦ by
        apply (cancel_mono (a n).hom).1
        simpa [Category.assoc] using
          congrArg (fun k ↦ (a (n + 1)).inv ≫ k) (ht n))).symm
  · change (A.inv ≫ δ) ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 M) = A.inv ≫ δ
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem restrictionIsoSquare
    {C A B : Type*} [Category C] [Category A] [Category B]
    (Rm : A ⥤ C) (Rn : B ⥤ C) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    {L P : A} {N Q : B} (a : L ≅ P) (b : N ≅ Q)
    (v : P ⟶ S.obj Q) (w : L ⟶ S.obj N)
    (h : a.hom ≫ v = w ≫ S.map b.hom) :
    Rm.map v ≫ e.hom.app Q ≫ (Rn.mapIso b).inv =
      (Rm.mapIso a).inv ≫ Rm.map w ≫ e.hom.app N := by
  have hh : (Rm.mapIso a).hom ≫ Rm.map v ≫ e.hom.app Q =
      Rm.map w ≫ e.hom.app N ≫ (Rn.mapIso b).hom := by
    change Rm.map a.hom ≫ Rm.map v ≫ e.hom.app Q = _
    rw [← Rm.map_comp_assoc, h, Rm.map_comp]
    have hn := e.hom.naturality b.hom
    dsimp only [Functor.comp_map] at hn
    simpa only [Category.assoc, Functor.mapIso_hom] using
      congrArg (fun k ↦ Rm.map w ≫ k) hn
  calc
    _ = (Rm.mapIso a).inv ≫
        ((Rm.mapIso a).hom ≫ Rm.map v ≫ e.hom.app Q) ≫ (Rn.mapIso b).inv := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = _ := by rw [hh]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDVRTower_tau (T : NormalizedDVRTower l E X D hl)
    {m n : ℕ} (h : n ≤ m) :
    (normalizedDVRTowerTransition l E X D hl h).app T.tower ≫ (T.evaluationIso n).hom =
      (T.evaluationIso m).hom ≫ (scalarReductionDerivedRestriction l E X m).map (T.tau h) ≫
        (normalizedDVRResCompletedComp l E X D hl h).hom.app (T.M n) := by
  exact T.tower_tau h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDVRKFlatUnit (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P) :
    (normalizedDVRIntegralAdjunction l E X n).unit.app
        (DerivedCategory.Q.obj P) ≫ normalizedDVRKFlatComparison l E X n P =
      DerivedCategory.Q.map (integralTowerUnit l E X D hl P n) := by
  have h := (derivedScalarExtensionRestrictionAdjunction l E X n).choose_spec P hP
  have hu := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
    (scalarReductionExtension_adjunction l E X n).choose P
  have hq : DerivedCategory.Qh.map
      (((scalarReductionExtension_adjunction l E X n).choose.mapHomotopyCategory
        (.up ℤ)).unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Q.map (unrestrictedTowerUnit l E X P n) :=
    congrArg (DerivedCategory.Qh.map) hu
  have hg : integralTowerUnit l E X D hl P n = unrestrictedTowerUnit l E X P n := by
    ext i U x
    exact ((integralTowerMaps_existUnique l E X D hl P).exists.choose_spec.1 n i U x).trans
      (unrestrictedTowerUnit_condition l E X P n i U x).symm
  have h' := h.trans hq
  have hf := (scalarReductionRestriction l E X n).mapDerivedCategoryFactorsh_hom_app
    (unrestrictedTowerFiniteComplex l E X n P)
  change (scalarReductionRestriction l E X n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension l E X n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) = _ at hf
  have h' := (congrArg (fun k ↦
    (derivedScalarExtensionRestrictionAdjunction l E X n).choose.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (scalarReductionDerivedRestriction l E X n).map
        ((scalarReductionCounit l E X n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ k) hf).symm.trans h'
  unfold normalizedDVRKFlatComparison normalizedDVRIntegralAdjunction
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv] at h' ⊢
  erw [(scalarReductionDerivedExtension l E X n).map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id]
  conv at h' =>
    lhs
    rhs
    rhs
    erw [(scalarReductionDerivedRestriction l E X n).map_id,
      DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id]
  dsimp only [DerivedCategory.Qh, HomologicalComplexUpToQuasiIso.Qh,
    Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift, Functor.comp_obj] at h' ⊢
  exact h'.trans (congrArg DerivedCategory.Q.map hg.symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDVRComplete_of_isIso
    (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
      M p δ)
    (hi : ∀ n : ℕ, IsIso (normalizedDVRCounitComparison l E X D hl T M p n)) :
    IsDerivedComplete l E X D hl M := by
  obtain ⟨P, hP, e, a, ha, ht⟩ := normalizedDVR_kflat_reduction_model l E X D hl
    (fun n ↦ normalizedDVRIntegralAdjunction l E X n)
    (normalizedDVRKFlatUnit l E X D hl) M
  have hid : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheaf l E X D hl) (𝟙 P) := ⟨inferInstance, hP⟩
  let c (n : ℕ) := asIso (normalizedDVRCounitComparison l E X D hl T M p n)
  let r (n : ℕ) := (scalarReductionDerivedRestriction l E X n).mapIso (c n)
  let b (n : ℕ) := T.evaluationIso n ≪≫ (r n).symm ≪≫ a n
  refine ⟨P, P, 𝟙 P, hid, e, ?_⟩
  apply roosTransport _ _ M p δ hc b
  · intro n
    dsimp only [b, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc]
    change (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower ≫
      (T.evaluationIso n).hom ≫ (r n).inv ≫ (a n).hom =
      (T.evaluationIso (n + 1)).hom ≫ (r (n + 1)).inv ≫
        (a (n + 1)).hom ≫
          (integralReductionTower l E X D hl P).map (homOfLE n.le_succ).op
    have ht' := ht n
    change (scalarReductionDerivedRestriction l E X (n + 1)).map
      (normalizedDVRReductionTransition l E X D hl n.le_succ M) ≫
      (normalizedDVRResCompletedComp l E X D hl n.le_succ).hom.app
        ((scalarReductionDerivedExtension l E X n).obj M) ≫ (a n).hom = _ at ht'
    simp only [integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ]
    rw [← ht']
    have hτ := normalizedDVRTower_tau l E X D hl T n.le_succ
    have hτ' := congrArg (fun k ↦ k ≫ (r n).inv ≫ (a n).hom) hτ
    simp only [Category.assoc] at hτ'
    rw [hτ']
    have hs := restrictionIsoSquare
      (scalarReductionDerivedRestriction l E X (n + 1))
      (scalarReductionDerivedRestriction l E X n) (normalizedDVRRes l E X n.le_succ)
      (normalizedDVRResCompletedComp l E X D hl n.le_succ)
      (c (n + 1)) (c n) (T.tau n.le_succ)
      (normalizedDVRReductionTransition l E X D hl n.le_succ M)
      (normalizedDVRCounitComparison_coherent l E X D hl T M p δ hc n.le_succ)
    dsimp only [Functor.mapIso_inv] at hs
    dsimp only [r, Functor.mapIso_inv]
    simpa only [Category.assoc] using
      congrArg (fun k ↦ (T.evaluationIso (n + 1)).hom ≫ k ≫ (a n).hom) hs
  · intro n
    have hu : (normalizedDVRIntegralAdjunction l E X n).unit.app M ≫
        (scalarReductionDerivedRestriction l E X n).map (c n).hom =
      p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom := by
      change (normalizedDVRIntegralAdjunction l E X n).unit.app M ≫
        (scalarReductionDerivedRestriction l E X n).map
          (normalizedDVRCounitComparison l E X D hl T M p n) = _
      erw [← Adjunction.homEquiv_unit]
      exact ((normalizedDVRIntegralAdjunction l E X n).homEquiv M (T.M n)).apply_symm_apply _
    change p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom ≫ (r n).inv ≫ (a n).hom = _
    have hu' := congrArg (fun k ↦ k ≫ (r n).inv ≫ (a n).hom) hu
    simp only [Category.assoc] at hu'
    rw [← hu']
    change (normalizedDVRIntegralAdjunction l E X n).unit.app M ≫
      (r n).hom ≫ (r n).inv ≫ (a n).hom = _
    simpa only [Iso.hom_inv_id_assoc,
      CategoryTheory.Functor.map_id, Category.id_comp, integralReductionTowerCone,
      Cone.extend_π, integralReductionTowerMap, integralTowerAugmentationIso,
      asIso_inv, IsIso.inv_id, NatTrans.comp_app, Functor.const_map_app,
      Category.assoc] using ha n

/-- A normalized DVR tower is recovered by derived reduction of its derived inverse
limit, through coherent canonical counit isomorphisms; that inverse limit is derived
complete. Source: blueprint order 2132; Bhatt--Scholze, Lemmas 3.5.4--3.5.7
(blueprint: lemma-sp-tower-adjunction-foundation--2).

Proof: use the strict normalized adic cone model for the restricted derived finite
reduction. The adopted theorem on strict normalized adic towers makes its augmented
projection invertible, and exact faithful scalar restriction detects isomorphisms in
the derived category. This gives each canonical finite comparison.
The Roos triangle says that consecutive projections commute with the transitions;
induction gives this for every pair of levels. Naturality and injectivity of the
adjunction Hom equivalences give exactly the stated coherence equation.
Choose a K-flat representative of M. Its universal scalar-extension counits give
isomorphisms to the termwise reductions, and the tensor-unit normalization identifies
its units with the canonical chain-level units. The K-flat transition lemma makes
these identifications commute with consecutive transitions. Conjugate the finite
comparisons by these isomorphisms and transfer the original Roos triangle along their
product. Its first map is precisely the canonical augmentation used in
IsDerivedComplete. No boundedness or constructibility hypothesis is used. -/
theorem normalizedDVRTower_effectivity (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
      M p δ) :
    (∀ n : ℕ, IsIso (normalizedDVRCounitComparison l E X D hl T M p n)) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        normalizedDVRCounitComparison l E X D hl T M p m ≫ T.tau h =
          normalizedDVRReductionTransition l E X D hl h M ≫
            (normalizedDVRRes l E X h).map
              (normalizedDVRCounitComparison l E X D hl T M p n)) ∧
      IsDerivedComplete l E X D hl M := by
  have hi (n : ℕ) : IsIso (normalizedDVRCounitComparison l E X D hl T M p n) :=
    normalizedDVRRoos_finite_reduction l E X D hl T M p δ hc n
      (normalizedDVRIntegralAdjunction l E X n)
  exact ⟨hi, normalizedDVRCounitComparison_coherent l E X D hl T M p δ hc,
    normalizedDVRComplete_of_isIso l E X D hl T M p δ hc hi⟩

end WeilConjectures
