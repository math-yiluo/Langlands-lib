/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherenceData
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift

/-! # Tensor coordinates of the two scalar augmentations

Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1 and Lemma 3.5.7;
Stacks Project, Tags 06YY and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

private theorem heq_apply
    {A C : Type v} {B D : Type w} {f : A → B} {g : C → D}
    (hBD : B = D) (h : HEq f g)
    {x : A} {y : C} (hxy : HEq x y) : HEq (f x) (g y) := by
  cases hBD
  exact heq_of_eq (congr_heq h hxy)

private theorem restriction_map_section
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) {M N : coefficientSequenceModules l E X} (f : M ⟶ N)
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceRestriction l E X).map f).app (op n)).val.app U
        (integralComparisonRestrictedSection l E X M n U x) =
      integralComparisonRestrictedSection l E X N n U (f.val.app (op (n, U.unop)) x) := by
  have h := (coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.2 f n U
  have hx : HEq (integralComparisonRestrictedSection l E X M n U x) x := cast_heq _ _
  exact eq_of_heq
    ((heq_apply (integralComparisonRestrictedSectionType l E X N n U) h hx).trans
      (cast_heq _ _).symm)

private theorem roosMap_fst
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {V W : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : V ⟶ W) (i : ℤ) :
    (integralOperationsRoosFunctor.map α).f i ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary W)).f i =
      (CochainComplex.mappingCocone.fst (scalarRoosBoundary V)).f i ≫
        (CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ α.app (op n))).f i := by
  apply SignedCoconeShift.cocone_ext_from (scalarRoosBoundary V) i
  · change (CochainComplex.mappingCocone.inl _).v i i _ ≫
      (SignedCoconeShift.coconeMap _ _ _).f i ≫ _ = _
    rw [SignedCoconeShift.coconeMap_inl_assoc]
    simp
  · change (CochainComplex.mappingCocone.inr _).1.v (i - 1) i _ ≫
      (SignedCoconeShift.coconeMap _ _ _).f i ≫ _ = _
    rw [SignedCoconeShift.coconeMap_inr_assoc]
    simp

private theorem roosMap_snd
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {V W : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : V ⟶ W) (i : ℤ) :
    (integralOperationsRoosFunctor.map α).f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary W)).v i (i - 1) (by omega) =
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary V)).v i (i - 1) (by omega) ≫
        (CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ α.app (op n))).f (i - 1) := by
  apply SignedCoconeShift.cocone_ext_from (scalarRoosBoundary V) i
  · change (CochainComplex.mappingCocone.inl _).v i i _ ≫
      (SignedCoconeShift.coconeMap _ _ _).f i ≫ _ = _
    rw [SignedCoconeShift.coconeMap_inl_assoc]
    simp
  · change (CochainComplex.mappingCocone.inr _).1.v (i - 1) i _ ≫
      (SignedCoconeShift.coconeMap _ _ _).f i ≫ _ = _
    rw [SignedCoconeShift.coconeMap_inr_assoc]
    simp

private theorem roosMap_level
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {V W : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : V ⟶ W) (n : ℕ) (i : ℤ) :
    (integralOperationsRoosFunctor.map α).f i ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary W)).f i ≫
        (Pi.π (fun m : ℕ ↦ W.obj (op m)) n).f i =
      (CochainComplex.mappingCocone.fst (scalarRoosBoundary V)).f i ≫
        (Pi.π (fun m : ℕ ↦ V.obj (op m)) n).f i ≫ (α.app (op n)).f i := by
  rw [← Category.assoc, roosMap_fst, Category.assoc]
  have h := congrArg (fun f ↦ f.f i) (CategoryTheory.Limits.Pi.map_π (fun m : ℕ ↦ α.app (op m)) n)
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg ((CochainComplex.mappingCocone.fst (scalarRoosBoundary V)).f i ≫ ·) h

private theorem roosMap_level_iso_hom
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {P Q : CochainComplex A ℤ} {V W : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (f : P ⟶ Q) (g : Q ⟶ integralOperationsRoosFunctor.obj V)
    (e : W ≅ V) (n : ℕ) (i : ℤ) :
    ((f ≫ g ≫ integralOperationsRoosFunctor.map e.inv).f i ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary W)).f i ≫
        (Pi.π (fun m : ℕ ↦ W.obj (op m)) n).f i) ≫ (e.hom.app (op n)).f i =
      (f ≫ g).f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary V)).f i ≫
        (Pi.π (fun m : ℕ ↦ V.obj (op m)) n).f i := by
  simp only [HomologicalComplex.comp_f, Category.assoc, roosMap_level]
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id_app, HomologicalComplex.id_f,
    Category.comp_id]

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F)
  (X : Scheme.{u})

private theorem scalarInverseCoordinate
    (P : CochainComplex (integralTowerModules l E X) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P)
    (qEL : (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E L ι X).obj P)
    (hqEL : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L X).obj.obj (op (n, U.unop)))
        (x : (P.X i).val.obj U),
        ((qEL.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l L X
            ((integralComparisonSequenceScalarModel l E L ι X).E.obj (C.X i)) n U
            (integralComparisonSequenceTensorSection l E L ι X (C.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (P.X i) U 1 x))))) =
          integralScalarTensorSection l E L ι X n (P.X i) U s x)
    (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
    (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
    (x : (P.X i).val.obj U) :
    let D := ((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
      (.up ℤ)).obj C
    let f := (completedScalarChainComparison l E L ι X).app P ≫
      integralOperationsRoosFunctor.map qEL.inv
    ((f.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex
        (.up ℤ)).obj D).asFunctor)).f i ≫
      (Pi.π (fun m : ℕ ↦
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U)
      (completedScalarTensorSection l E L ι X (P.X i) U t x) =
    integralComparisonRestrictedSection l L X (D.X i) n U
      (integralComparisonSequenceTensorSection l E L ι X (C.X i) (op (n, U.unop))
        ((completedIntegralCommRingProjectionUnrestricted l L X n).hom.app U t)
        (integralComparisonSequenceSection l E X (C.X i) n U
          (((κ n).inv.f i).val.app U
            (unrestrictedIntegralTensorSection l E X n (P.X i) U 1 x)))) := by
  dsimp only
  simp only [HomologicalComplex.comp_f, Category.assoc, roosMap_level]
  change ((qEL.inv.app (op n)).f i).val.app U
    ((((completedScalarChainComparison l E L ι X).app P).f i ≫
      (CochainComplex.mappingCocone.fst
        (completedScalarRoosEndomorphism l E L ι X P)).f i ≫
      (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι X).obj P).obj (op m))
        n).f i).val.app U
          (completedScalarTensorSection l E L ι X (P.X i) U t x)) = _
  rw [(completedScalarChainComparison_spec l E L ι X).1 P i n U t x]
  rw [← hqEL n i U
    ((completedIntegralCommRingProjectionUnrestricted l L X n).hom.app U t) x]
  change (((qEL.hom.app (op n) ≫ qEL.inv.app (op n)).f i).val.app U) _ = _
  simp only [Iso.hom_inv_id_app, HomologicalComplex.id_f, SheafOfModules.id_val,
    ]
  rfl

private theorem scalarAssociatorCoordinate
    (P : CochainComplex (integralTowerModules l E X) ℤ)
    (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
    (x : (P.X i).val.obj U) :
    ((((CompletedLineTensor.scalarAssociatorComplex l E X L ι F j
        (CompletedLineTensor.associatorData l E X L ι F j).sheaf).hom.app P ≫
        (completedScalarChainComparison l E F (j.comp ι) X).app P).f i ≫
        (CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E F (j.comp ι) X P)).f i ≫
        (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E F (j.comp ι) X).obj P).obj
          (op m)) n).f i).val.app U)
        (completedScalarTensorSection l L F j X
          (((completedOrdinaryScalarComplex l E L ι X).obj P).X i) U s
          (completedScalarTensorSection l E L ι X (P.X i) U t x)) =
      integralScalarTensorSection l E F (j.comp ι) X n (P.X i) U
        ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U
          (s * (completedCoefficientMap l L F j X).hom.app U t)) x := by
  change ((((completedScalarChainComparison l E F (j.comp ι) X).app P).f i ≫
    (CochainComplex.mappingCocone.fst
      (completedScalarRoosEndomorphism l E F (j.comp ι) X P)).f i ≫
    (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E F (j.comp ι) X).obj P).obj
      (op m)) n).f i).val.app U)
      (((CompletedLineTensor.associatorData l E X L ι F j).sheaf.hom.app
        (P.X i)).val.app U
        (completedScalarTensorSection l L F j X _ U s
          (completedScalarTensorSection l E L ι X (P.X i) U t x))) = _
  have hOrd := (CompletedLineTensor.associatorData_existsUnique l E X L ι F j).exists.choose_spec.1
    (P.X i) U t s x
  change ((CompletedLineTensor.associatorData l E X L ι F j).sheaf.hom.app
    (P.X i)).val.app U _ = _ at hOrd
  rw [hOrd, (completedScalarChainComparison_spec l E F (j.comp ι) X).1]

/-- Tensor associativity identifies the scalar change of a quotient augmentation
with the direct augmentation. This is entirely a statement about strict chain
maps, before localization or insertion of a derived counit.

Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1; Stacks 06YY;
step 3 of lem-trf-scalar-model-iterated-strict-calculation.
(blueprint: lem-trf-scalar-tensor-roos-coordinates).

Proof in words: the chain comparison from an ordinary scalar complex to its
quotient Roos tower has zero shifted coordinate. A Roos map induced by a map of
towers acts separately on the two product coordinates, so the same is true after
transport by qEL, qEF and the strict sequence scalar associator. For the
unshifted coordinate, first test on a nested tensor t tensor (s tensor x).
The qEL normalization and the first augmentation identify its inner coordinate
with the quotient of s tensored with kappa-inverse(1 tensor x). The system
scalar associator and qEF multiply the two quotient coefficients. The ordinary
sheaf associator followed by the direct augmentation gives the same product:
the quotient of t times the image under j of the quotient of s. The residue
formula for completedCoefficientMap identifies these coefficients. The hypothesis
identifying the inner tensor coordinate with y gives the displayed implication.
All equalities are degreewise strict
maps and commute with the actual quotient transitions and differentials. -/
theorem scalarTensorRoosCoordinates
    (P : CochainComplex (integralTowerModules l E X) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P)
    (qEL : (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E L ι X).obj P)
    (hqEL : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L X).obj.obj (op (n, U.unop)))
        (x : (P.X i).val.obj U),
        ((qEL.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l L X
            ((integralComparisonSequenceScalarModel l E L ι X).E.obj (C.X i)) n U
            (integralComparisonSequenceTensorSection l E L ι X (C.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (P.X i) U 1 x))))) =
          integralScalarTensorSection l E L ι X n (P.X i) U s x)
    (qEF : (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E F (j.comp ι) X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E F (j.comp ι) X).obj P)
    (hqEF : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l F X).obj.obj (op (n, U.unop)))
        (x : (P.X i).val.obj U),
        ((qEF.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l F X
            ((integralComparisonSequenceScalarModel l E F (j.comp ι) X).E.obj (C.X i)) n U
            (integralComparisonSequenceTensorSection l E F (j.comp ι) X (C.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (P.X i) U 1 x))))) =
          integralScalarTensorSection l E F (j.comp ι) X n (P.X i) U s x) :
    let P' := (completedOrdinaryScalarComplex l E L ι X).obj P
    let D := ((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
      (.up ℤ)).obj C
    let a := (NatIso.mapHomologicalComplex
      (integralComparisonSequenceScalarComposition l E L ι F j X) (.up ℤ)).app C
    let w := ((coefficientSequenceRestriction l F X).mapHomologicalComplex
      (.up ℤ)).mapIso a
    let wa := HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso w
    let f := (completedScalarChainComparison l E L ι X).app P ≫
      integralOperationsRoosFunctor.map qEL.inv
    let g := (CompletedLineTensor.scalarAssociatorComplex l E X L ι F j
        (CompletedLineTensor.associatorData l E X L ι F j).sheaf).hom.app P ≫
      (completedScalarChainComparison l E F (j.comp ι) X).app P ≫
      integralOperationsRoosFunctor.map (qEF.inv ≫ wa.inv)
    (∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor)).v i (i - 1) (by omega) = 0) ∧
    (∀ i : ℤ, g.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor)).v i (i - 1) (by omega) = 0) ∧
    (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : (P.X i).val.obj U) (y : (D.X i).val.obj (op (n, U.unop))),
      ((f.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U)
        (completedScalarTensorSection l E L ι X (P.X i) U t x) =
          integralComparisonRestrictedSection l L X (D.X i) n U y →
      ((g.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦
          (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
            (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
              (.up ℤ)).obj D)).asFunctor.obj (op m)) n).f i).val.app U)
        (completedScalarTensorSection l L F j X (P'.X i) U s
          (completedScalarTensorSection l E L ι X (P.X i) U t x)) =
      integralComparisonRestrictedSection l F X
        ((integralComparisonSequenceScalarModel l L F j X).E.obj (D.X i)) n U
        (integralComparisonSequenceTensorSection l L F j X (D.X i) (op (n, U.unop))
          ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s) y)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [HomologicalComplex.comp_f, Category.assoc]
    erw [roosMap_snd]
    erw [reassoc_of% (completedScalarChainComparison_spec l E L ι X).2 P i]
    simp only [zero_comp]
  · intro i
    simp only [HomologicalComplex.comp_f, Category.assoc]
    erw [roosMap_snd]
    erw [reassoc_of% (completedScalarChainComparison_spec l E F (j.comp ι) X).2 P i]
    simp only [zero_comp, comp_zero]
  · intro n i U s t x y h
    let D := ((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
      (.up ℤ)).obj C
    let z := integralComparisonSequenceSection l E X (C.X i) n U
      (((κ n).inv.f i).val.app U
        (unrestrictedIntegralTensorSection l E X n (P.X i) U 1 x))
    let tL := (completedIntegralCommRingProjectionUnrestricted l L X n).hom.app U t
    let sF := (completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s
    have hy : y = integralComparisonSequenceTensorSection l E L ι X (C.X i)
        (op (n, U.unop)) tL z := by
      apply (Equiv.cast
        (integralComparisonRestrictedSectionType l L X (D.X i) n U).symm).injective
      exact h.symm.trans (scalarInverseCoordinate l E L ι X P C κ qEL hqEL n i U t x)
    subst y
    let a := (NatIso.mapHomologicalComplex
      (integralComparisonSequenceScalarComposition l E L ι F j X) (.up ℤ)).app C
    let w := ((coefficientSequenceRestriction l F X).mapHomologicalComplex
      (.up ℤ)).mapIso a
    let wa := HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso w
    let eU := (SheafOfModules.evaluation _ U).mapIso
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso ((wa ≪≫ qEF).app (op n)))
    apply (ConcreteCategory.bijective_of_isIso eU.hom).1
    dsimp only [eU, Functor.mapIso_hom]
    change (((((CompletedLineTensor.scalarAssociatorComplex l E X L ι F j
        (CompletedLineTensor.associatorData l E X L ι F j).sheaf).hom.app P ≫
        (completedScalarChainComparison l E F (j.comp ι) X).app P ≫
        integralOperationsRoosFunctor.map (wa ≪≫ qEF).inv).f i ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary _)).f i ≫
        (Pi.π (fun m : ℕ ↦
          (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
            (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
              (.up ℤ)).obj D)).asFunctor.obj (op m)) n).f i) ≫
        ((wa ≪≫ qEF).hom.app (op n)).f i).val.app U) _ = _
    erw [roosMap_level_iso_hom _ _ (wa ≪≫ qEF) n i]
    refine (scalarAssociatorCoordinate l E L F ι j X P n i U s t x).trans ?_
    have hSeq := (integralComparisonSequenceScalarComposition_existsUnique
      l E L ι F j X).exists.choose_spec (C.X i) (op (n, U.unop)) sF tL z
    change ((integralComparisonSequenceScalarComposition l E L ι F j X).hom.app
      (C.X i)).val.app (op (n, U.unop)) _ = _ at hSeq
    change _ = ((qEF.hom.app (op n)).f i).val.app U
      (((((coefficientSequenceRestriction l F X).map
        ((integralComparisonSequenceScalarComposition l E L ι F j X).hom.app
          (C.X i))).app (op n)).val.app U)
        (integralComparisonRestrictedSection l F X
          ((integralComparisonSequenceScalarModel l L F j X).E.obj (D.X i)) n U
          (integralComparisonSequenceTensorSection l L F j X (D.X i)
            (op (n, U.unop)) sF
            (integralComparisonSequenceTensorSection l E L ι X (C.X i)
              (op (n, U.unop)) tL z))))
    erw [restriction_map_section, hSeq, hqEF]
    congr 1
    rw [map_mul]
    congr 1
    have hr := congrArg (fun f ↦ f.hom.app U)
      ((completedCoefficientMap_existsUnique l L F j X).exists.choose_spec n)
    have hr' := ConcreteCategory.congr_hom hr t
    exact hr'

end WeilConjectures
