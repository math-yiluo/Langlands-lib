/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.PurReductionLimitShiftData
public import WeilConjectures.SmoothPurity.SequenceKInjectiveComparison.SequenceKInjectiveComparisonShifts
import all WeilConjectures.SmoothPurity.SequenceKInjectiveComparison.SequenceKInjectiveComparisonShifts
import all WeilConjectures.CategoryTheory.InjectiveTowerRoos.InjectiveTowerRoosShifts
import WeilConjectures.CategoryTheory.K.KInjectiveRoosAugmentation
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Tactic.TransportExact

/-! # Signed Roos triangles for the canonical coefficient limit

Source: Stacks 06YY, 07A6 and 0941; current blueprint
`sk-thm-sf-compatibility/fix-prop-coherence.proof.md`, coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a b w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

open CategoryTheory.Pretriangulated

section RoosModels

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
  [HasCountableProducts (DerivedCategory.{w} A)]

attribute [local instance] CategoryTheory.baseLimit_additive

private def productModelIso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    DerivedCategory.Q.obj (roosP I) ≅
      ∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n)) :=
  ((Fan.isLimitMapConeEquiv DerivedCategory.Q
    (fun n : ℕ ↦ I.asFunctor.obj (op n)) (limit.cone _))
      (CategoryTheory.injective_product I).2.some).conePointUniqueUpToIso
        (productIsProduct _)

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma productModelIso_π (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
    (n : ℕ) :
    (productModelIso I).hom ≫ Pi.π _ n =
      DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n) :=
  ((Fan.isLimitMapConeEquiv DerivedCategory.Q
    (fun n : ℕ ↦ I.asFunctor.obj (op n)) (limit.cone _))
      (CategoryTheory.injective_product I).2.some).conePointUniqueUpToIso_hom_comp
        (productIsProduct _) (Discrete.mk n)

private def derivedProductShift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj ((I⟦r⟧).asFunctor.obj (op n))) ≅
      (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n)))⟦r⟧ :=
  Pi.mapIso (fun n : ℕ ↦ (DerivedCategory.Q.commShiftIso r).app
    (I.asFunctor.obj (op n))) ≪≫
      (PreservesProduct.iso (shiftFunctor _ r)
        (fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n)))).symm

omit [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A] in
private lemma derivedProductShift_π (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) (n : ℕ) :
    (derivedProductShift I r).hom ≫ (Pi.π
        (fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n))) n)⟦r⟧' =
      Pi.π _ n ≫ (DerivedCategory.Q.commShiftIso r).hom.app (I.asFunctor.obj (op n)) := by
  rw [← piComparison_comp_π (shiftFunctor _ r)]
  simp only [derivedProductShift, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← PreservesProduct.iso_hom, Iso.inv_hom_id_assoc]
  exact Pi.mapIso_hom_π _ n

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma productModelIso_shift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] (r : ℤ) :
    (productModelIso (I⟦r⟧)).hom ≫ (derivedProductShift I r).hom =
      InjectiveTowerRoos.localizedShift CategoryTheory.productFunctor
        CategoryTheory.productShift I r ≫ (productModelIso I).hom⟦r⟧' := by
  apply (cancel_mono (PreservesProduct.iso (shiftFunctor (DerivedCategory.{w} A) r)
    (fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n)))).hom).1
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
    derivedProductShift_π]
  rw [← Functor.map_comp]
  rw [productModelIso_π]
  simp only [InjectiveTowerRoos.localizedShift, Category.assoc]
  rw [← Functor.commShiftIso_hom_naturality]
  rw [← Functor.map_comp_assoc]
  have hp :
      ((Functor.commShiftIso CategoryTheory.productFunctor
        (self := CategoryTheory.productShift) r).hom.app I) ≫
          (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n)⟦r⟧' =
        Pi.π (fun n : ℕ ↦ (I⟦r⟧).asFunctor.obj (op n)) n := by
    ext q
    have h := CategoryTheory.productShift_π I r q n
    simp only [CategoryTheory.productShiftComponent_eq, CategoryTheory.π,
      CategoryTheory.productShift_hom_f, HomologicalComplex.comp_f,
      CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, NatTrans.id_app] at h ⊢
    erw [Category.comp_id] at h
    exact h
  rw [← Category.assoc, productModelIso_π]
  exact congrArg (fun f ↦ DerivedCategory.Q.map f ≫
    (DerivedCategory.Q.commShiftIso r).hom.app (I.asFunctor.obj (op n))) hp.symm

private def limitModelShift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :=
  DerivedCategory.Q.map
      ((((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app I) ≫
    (DerivedCategory.Q.commShiftIso r).hom.app
      (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I)

omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory.{w} A)] in
private lemma limitModelIso_shift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    DerivedCategory.Q.map ((CategoryTheory.limitModelIso (A := A)).hom.app (I⟦r⟧)) ≫
        InjectiveTowerRoos.localizedShift roosLimitFunctor CategoryTheory.limitShift I r =
      limitModelShift I r ≫
        (DerivedCategory.Q.map ((CategoryTheory.limitModelIso (A := A)).hom.app I))⟦r⟧' := by
  let := CategoryTheory.baseLimit_additive (A := A)
  let := CategoryTheory.limitShift (A := A)
  have : NatTrans.CommShift (CategoryTheory.limitModelIso (A := A)).hom ℤ :=
    Functor.CommShift.ofIso_compatibility _ _
  have h := NatTrans.shift_app_comm (CategoryTheory.limitModelIso (A := A)).hom r I
  simp only [InjectiveTowerRoos.localizedShift, limitModelShift, Category.assoc]
  rw [← Functor.map_comp_assoc, ← h, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality]

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma productModelIso_transition (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.map (roosU I) ≫ (productModelIso I).hom =
      (productModelIso I).hom ≫ towerTransitionEndomorphism
        (fun n : ℕ ↦ DerivedCategory.Q.map
          (I.asFunctor.map (homOfLE (Nat.le_succ n)).op)) := by
  apply Pi.hom_ext
  intro n
  have ht := (towerTransitionEndomorphism_eq_iff
    (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op) (roosU I)).mp rfl n
  simp only [Category.assoc, productModelIso_π, ← Functor.map_comp, ht,
    Functor.map_sub]
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
    Category.id_comp, Preadditive.comp_sub, Pi.lift_comp_π, productModelIso_π]
  rw [Functor.map_comp, ← Category.assoc, productModelIso_π]

end RoosModels

private lemma inverse_square {C : Type*} [Category C] {X Y Z T : C}
    (a : X ≅ Y) (b : Z ≅ T) (f : X ⟶ Z) (g : Y ⟶ T)
    (h : a.hom ≫ g = f ≫ b.hom) : a.inv ≫ f = g ≫ b.inv := by
  apply (cancel_epi a.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

-- Identify the canonical coefficient functors with the generic derived-functor models.
private lemma coefficientLimitModel_shift
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ I)
    [I.IsKInjective] [QuasiIso j] (r : ℤ) [(I⟦r⟧).IsKInjective]
    [QuasiIso (purCoefficientShiftedResolution l E W N I j r)] :
    letI := SequenceKInjectiveComparison.totalLimitCommShift l E W
    (coefficientSequenceLimit l E W).map ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
      ((coefficientSequenceLimit l E W).commShiftIso r).hom.app (DerivedCategory.Q.obj N) ≫
      (purCoefficientLimitModel l E W N I j).hom⟦r⟧' =
    (purCoefficientLimitModel l E W (N⟦r⟧) (I⟦r⟧)
      (purCoefficientShiftedResolution l E W N I j r)).hom ≫ limitModelShift I r := by
  have h := (SequenceKInjectiveComparison.comparisonIso_shifts
    (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
    N I j r).symm
  transport_exact h

private def coefficientModelIso
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ I)
    [I.IsKInjective] [QuasiIso j] :
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj (limit I.asFunctor) :=
  purCoefficientLimitModel l E W N I j ≪≫
    DerivedCategory.Q.mapIso ((CategoryTheory.limitModelIso
      (A := scalarReductionSource l E W)).app I)

private lemma coefficientModelIso_shift
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ I)
    [I.IsKInjective] [QuasiIso j] (r : ℤ) [(I⟦r⟧).IsKInjective]
    [QuasiIso (purCoefficientShiftedResolution l E W N I j r)] :
    letI := SequenceKInjectiveComparison.totalLimitCommShift l E W
    (coefficientModelIso l E W (N⟦r⟧) (I⟦r⟧)
      (purCoefficientShiftedResolution l E W N I j r)).hom ≫
        InjectiveTowerRoos.localizedShift roosLimitFunctor CategoryTheory.limitShift I r =
      ((coefficientSequenceLimit l E W).map ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
        ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
          (DerivedCategory.Q.obj N)) ≫ (coefficientModelIso l E W N I j).hom⟦r⟧' := by
  simp only [coefficientModelIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc]
  rw [limitModelIso_shift, ← Category.assoc, ← coefficientLimitModel_shift]
  simp only [Functor.map_comp, Category.assoc]

private def coefficientRoosTriangle
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E W))]
    [IsGrothendieckAbelian.{max u (t + 1)} (ℕᵒᵖ ⥤ scalarReductionSource l E W)]
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ I)
    [I.IsKInjective] [QuasiIso j] : PurCoefficientRoosTriangle l E W N I j := by
  let := kInjectiveRoosAugmentation I
  let d := coefficientModelIso l E W N I j
  let e := productModelIso I
  let p := d.hom ≫ InjectiveTowerRoos.projection I ≫ e.hom
  let δ := e.inv ≫ CategoryTheory.normalizedBoundary I ≫ d.inv⟦(1 : ℤ)⟧'
  refine ⟨p, δ, ?_, ?_⟩
  · let T := Triangle.mk (InjectiveTowerRoos.projection I)
      (DerivedCategory.Q.map (roosU I)) (CategoryTheory.normalizedBoundary I)
    let U := Triangle.mk p (towerTransitionEndomorphism
      (fun n : ℕ ↦ DerivedCategory.Q.map
        (I.asFunctor.map (homOfLE (Nat.le_succ n)).op))) δ
    let q : T ≅ U := Triangle.isoMk _ _ d.symm e e
      (by simp [T, U, p])
      (productModelIso_transition I)
      (by simp [T, U, δ])
    exact isomorphic_distinguished _ (CategoryTheory.normalizedBoundary_distinguished I) _ q.symm
  · intro n
    simp only [p, d, e, coefficientModelIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc, productModelIso_π]
    simp only [InjectiveTowerRoos.projection, ← Functor.map_comp]
    rw [Pi.lift_comp_π, CategoryTheory.limitModel_hom_π]

private lemma coefficientRoosTriangle_shift
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E W))]
    [IsGrothendieckAbelian.{max u (t + 1)} (ℕᵒᵖ ⥤ scalarReductionSource l E W)]
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ I)
    [I.IsKInjective] [QuasiIso j] (r : ℤ) [(I⟦r⟧).IsKInjective]
    [QuasiIso (purCoefficientShiftedResolution l E W N I j r)] :
    letI := SequenceKInjectiveComparison.totalLimitCommShift l E W
    let R := coefficientRoosTriangle l E W N I j
    let Rr := coefficientRoosTriangle l E W (N⟦r⟧) (I⟦r⟧)
      (purCoefficientShiftedResolution l E W N I j r)
    let s := (coefficientSequenceLimit l E W).map
        ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
      ((coefficientSequenceLimit l E W).commShiftIso r).hom.app (DerivedCategory.Q.obj N)
    (Rr.p ≫ (purCoefficientRoosProductShift l E W I r).hom = s ≫ R.p⟦r⟧') ∧
    (Rr.δ ≫ s⟦(1 : ℤ)⟧' = r.negOnePow •
      ((purCoefficientRoosProductShift l E W I r).hom ≫ R.δ⟦r⟧' ≫
        (shiftFunctorComm _ 1 r).hom.app
          ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N)))) := by
  let := SequenceKInjectiveComparison.totalLimitCommShift l E W
  let := kInjectiveRoosAugmentation I
  let := kInjectiveRoosAugmentation (I⟦r⟧)
  let d := coefficientModelIso l E W N I j
  let dr := coefficientModelIso l E W (N⟦r⟧) (I⟦r⟧)
    (purCoefficientShiftedResolution l E W N I j r)
  let e := productModelIso I
  let er := productModelIso (I⟦r⟧)
  let s := (coefficientSequenceLimit l E W).map
      ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
    ((coefficientSequenceLimit l E W).commShiftIso r).hom.app (DerivedCategory.Q.obj N)
  have hd := coefficientModelIso_shift l E W N I j r
  have he := productModelIso_shift I r
  have hd' := inverse_square dr ((shiftFunctor _ r).mapIso d) s
    (InjectiveTowerRoos.localizedShift roosLimitFunctor CategoryTheory.limitShift I r) hd
  have he' := inverse_square er ((shiftFunctor _ r).mapIso e)
    (InjectiveTowerRoos.localizedShift CategoryTheory.productFunctor
      CategoryTheory.productShift I r)
    (derivedProductShift I r).hom he
  simp only [Functor.mapIso_inv] at hd' he'
  have hc := (shiftFunctorComm _ (1 : ℤ) r).hom.naturality d.inv
  change (d.inv⟦(1 : ℤ)⟧')⟦r⟧' ≫ _ =
    _ ≫ (d.inv⟦r⟧')⟦(1 : ℤ)⟧' at hc
  change (dr.hom ≫ InjectiveTowerRoos.projection (I⟦r⟧) ≫ er.hom) ≫
      (derivedProductShift I r).hom =
    s ≫ (d.hom ≫ InjectiveTowerRoos.projection I ≫ e.hom)⟦r⟧' ∧
    (er.inv ≫ CategoryTheory.normalizedBoundary (I⟦r⟧) ≫ dr.inv⟦(1 : ℤ)⟧') ≫ s⟦(1 : ℤ)⟧' =
      r.negOnePow • ((derivedProductShift I r).hom ≫
        (e.inv ≫ CategoryTheory.normalizedBoundary I ≫ d.inv⟦(1 : ℤ)⟧')⟦r⟧' ≫
          (shiftFunctorComm _ 1 r).hom.app _)
  constructor
  · simp only [Functor.map_comp, Category.assoc]
    rw [he, ← Category.assoc (InjectiveTowerRoos.projection (I⟦r⟧)),
      CategoryTheory.localized_inclusion_shift, Category.assoc,
      ← Category.assoc dr.hom, hd]
    simp only [s, d, e, Category.assoc]
  · simp only [Category.assoc, ← Functor.map_comp]
    rw [hd', Functor.map_comp]
    rw [← Category.assoc (CategoryTheory.normalizedBoundary (I⟦r⟧)),
      CategoryTheory.normalizedBoundary_shift]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, Functor.map_comp,
      Category.assoc]
    rw [← hc]
    rw [← Category.assoc er.inv, he']
    simp only [Category.assoc]

-- Elaborating the coefficient sheaf and tower instances unfolds their universe models.
/-- The canonical coefficient limit admits Roos triangles on every supplied
K-injective replacement, with the canonical replacement-model shift equation,
their actual projections and signed shift equations.
Source: Stacks 0941, proof of lemma-derived-limit-is-ok, and cochain cone convention
014E, refined by the explicit signed cone calculation
(blueprint: lem-pur-coefficient-roos-shift-normalization).

Proof: first use a K-injective replacement with injective tower terms. Evaluation
preserves K-injectivity, and the termwise product is a product after localization.
The prefix-tower lifting argument splits every transition in each degree. Thus
1-s is termwise split epic, its kernel is the actual limit, and the kernel
inclusion (0,x) into Cone(1-s)[-1] is a quasi-isomorphism. Inverse rotation and
localization give the distinguished triangle. Its first arrow consists of the
actual limit projections; transport its first vertex along purCoefficientLimitModel.
On the shifted cone the map (y,x) maps to ((-1)^r y,x). It commutes with the
kernel inclusion and with the projection to x. Insertion in y gains (-1)^r,
so the connecting map has exactly the displayed sign and shift commutator.
For an arbitrary K-injective tower I, compare it to a replacement with injective
terms. The comparison is a homotopy equivalence. Limit, evaluation, product and
the Roos cone preserve tower homotopies, so transport these identities back to I.
The same computation on comparison maps proves naturality and independence.
Choose the boundary by this natural transport; its shift square holds for every
shifted replacement, not only selected representatives. The proved canonical
replacement-shift equation identifies the transported limit shift with the fixed
one used here. Products need not be exact. Zero shift is identity; r=1 and -1
negate the first coordinate, and signs multiply for repeated shifts. Zero towers
and the empty scheme give the zero triangle. -/
theorem purCoefficientRoosShiftNormalization
    [products : HasCountableProducts (DerivedCategory (scalarReductionSource l E W))] :
    letI := SequenceKInjectiveComparison.totalLimitCommShift l E W
    (∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j]
    (r : ℤ) [(I⟦r⟧).IsKInjective]
    [QuasiIso (purCoefficientShiftedResolution l E W N I j r)],
    (coefficientSequenceLimit l E W).map
        ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
      ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
        (DerivedCategory.Q.obj N) ≫
      (purCoefficientLimitModel l E W N I j).hom⟦r⟧' =
    (purCoefficientLimitModel l E W (N⟦r⟧) (I⟦r⟧)
      (purCoefficientShiftedResolution l E W N I j r)).hom ≫
      DerivedCategory.Q.map
        ((((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app I) ≫
      (DerivedCategory.Q.commShiftIso r).hom.app
        (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∃ roos : (∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j],
      PurCoefficientRoosTriangle l E W N I j),
      (∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j]
      (r : ℤ) [(I⟦r⟧).IsKInjective]
      [QuasiIso (purCoefficientShiftedResolution l E W N I j r)],
      ((roos (N⟦r⟧) (I⟦r⟧) (purCoefficientShiftedResolution l E W N I j r)).p ≫
        (purCoefficientRoosProductShift l E W I r).hom =
      (coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
        ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
          (DerivedCategory.Q.obj N) ≫ (roos N I j).p⟦r⟧') ∧
      ((roos (N⟦r⟧) (I⟦r⟧) (purCoefficientShiftedResolution l E W N I j r)).δ ≫
        ((coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
          ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
            (DerivedCategory.Q.obj N))⟦(1 : ℤ)⟧' =
      r.negOnePow • ((purCoefficientRoosProductShift l E W I r).hom ≫
        (roos N I j).δ⟦r⟧' ≫ (shiftFunctorComm _ 1 r).hom.app
          ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N))))))  := by
  let := SequenceKInjectiveComparison.totalLimitCommShift l E W
  constructor
  · intro N I j hI hj r hIr hjr
    exact coefficientLimitModel_shift l E W N I j r
  · let A := scalarReductionSource l E W
    let : IsGrothendieckAbelian.{max u (t + 1)} A :=
      (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1,t,u}
        (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
    let : IsGrothendieckAbelian.{max u (t + 1)} (ℕᵒᵖ ⥤ A) := by
      have := diagrams_isGrothendieckAbelian A (AsSmall.{max u (t + 1)} ℕᵒᵖ)
      exact IsGrothendieckAbelian.of_equivalence
        (Equivalence.congrLeft (AsSmall.equiv (C := ℕᵒᵖ)).symm)
    refine ⟨fun N I j _ _ ↦ coefficientRoosTriangle l E W N I j, ?_⟩
    intro N I j hI hj r hIr hjr
    simpa only [Category.assoc] using coefficientRoosTriangle_shift l E W N I j r

end WeilConjectures
