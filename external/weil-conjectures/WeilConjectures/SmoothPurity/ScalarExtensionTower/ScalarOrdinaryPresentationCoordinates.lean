/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientScalarCochainEvaluation
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryQuotientIso
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionAssociationSuccessor
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryAssociationChain
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRestrictedTower
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationScalarUnits
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationQuotientUnits
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationTensorCoordinates
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.OrdinaryScalarTowerProof
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Scalar extension of ordinary quotient presentations

Source: Stacks 03EK, 03D7, 06YY and 07A4. The completed-ring tensor association,
its quotient successors, and its unit formula are proved before applying pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension integralOrdinaryScalar
  completedIntegralCommRingProjectionUnrestricted constantSheaf HasDerivedCategory.standard
  WeilConjectures.scalarAdjunction
  unrestrictedIntegralTensorSection integralOrdinaryTensorSection integralScalarTensorSection

attribute [local implicit_reducible] integralCoefficientCommRingSheaf integralCoefficientSheaf
  unrestrictedIntegralReductionFunctor
  SemilinearSections.systemRing coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf

private theorem finiteReductionUnit (Y : Scheme.{u})
    (M : scalarReductionSource l L Y) (n : ℕ) (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((scalarReductionExtension_adjunction l L Y n).choose.unit.app M).val.app U x =
      unrestrictedIntegralTensorSection l L Y n M U 1 x := by
  have h := (scalarReductionExtension_adjunction l L Y n).choose_spec M U x
  dsimp only [unrestrictedIntegralTensorSection, unrestrictedIntegralReductionFunctor,
    unrestrictedIntegralReductionExistence, scalarReductionExistence] at h ⊢
  with_unfolding_all exact h

private theorem completedScalarAdj_exists (Y : Scheme.{u}) :
    ∃ a : integralOrdinaryScalar l E L ι Y ⊣
      SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι Y)),
      ∀ (M : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = integralOrdinaryTensorSection l E L ι Y M U 1 x := by
  let ho := (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralCompletedScalarMap l E L ι Y)).choose_spec.choose_spec
      (integralOrdinaryScalar l E L ι Y) (integralOrdinaryScalar_obj l E L ι Y)
      (fun f ↦ integralOrdinaryScalar_map l E L ι Y f)
  refine ⟨ho.choose, ?_⟩
  intro M U x
  have ht := ho.choose_spec M ((integralOrdinaryScalar l E L ι Y).obj M)
    (eqToHom (integralOrdinaryScalar_obj l E L ι Y M).symm) U x
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at ht
  unfold integralOrdinaryTensorSection
  with_unfolding_all exact ht

private def completedScalarAdj (Y : Scheme.{u}) :
    integralOrdinaryScalar l E L ι Y ⊣
      SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι Y)) :=
  (completedScalarAdj_exists l E L ι Y).choose

private theorem completedScalarAdj_unit (Y : Scheme.{u})
    (M : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((completedScalarAdj l E L ι Y).unit.app M).val.app U x =
      integralOrdinaryTensorSection l E L ι Y M U 1 x :=
  (completedScalarAdj_exists l E L ι Y).choose_spec M U x

attribute [local irreducible] completedScalarAdj

private def completedFiniteAssociation (Y : Scheme.{u}) (n : ℕ) :
    integralOrdinaryScalar l E L ι Y ⋙ scalarReductionExtension l L Y n ≅
      integralScalarReduction l E L ι Y n := by
  let J := Scheme.ProEt.topology Y
  let F := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  exact (WeilConjectures.associationWithUnit
    (F.map (integralCompletedScalarMap l E L ι Y))
    (F.map (completedIntegralCommRingProjectionUnrestricted l L Y n))
    (F.map (integralScalarRho l E L ι Y n))
    (by rw [← F.map_comp, integralCompletedScalarMap_projection])
    (integralOrdinaryScalar l E L ι Y) (scalarReductionExtension l L Y n)
    (integralScalarReduction l E L ι Y n)
    (completedScalarAdj l E L ι Y)
    (scalarReductionExtension_adjunction l L Y n).choose
    (WeilConjectures.scalarAdjunction l E L ι Y n)).iso

private theorem completedFiniteAssociation_unit (Y : Scheme.{u}) (n : ℕ)
    (M : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((completedFiniteAssociation l E L ι Y n).hom.app M).val.app U
      (unrestrictedIntegralTensorSection l L Y n
        ((integralOrdinaryScalar l E L ι Y).obj M) U 1
        (integralOrdinaryTensorSection l E L ι Y M U 1 x)) =
      integralScalarTensorSection l E L ι Y n M U 1 x := by
  let J := Scheme.ProEt.topology Y
  let F := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have h := (WeilConjectures.associationWithUnit
    (F.map (integralCompletedScalarMap l E L ι Y))
    (F.map (completedIntegralCommRingProjectionUnrestricted l L Y n))
    (F.map (integralScalarRho l E L ι Y n))
    (by rw [← F.map_comp, integralCompletedScalarMap_projection])
    (integralOrdinaryScalar l E L ι Y) (scalarReductionExtension l L Y n)
    (integralScalarReduction l E L ι Y n)
    (completedScalarAdj l E L ι Y)
    (scalarReductionExtension_adjunction l L Y n).choose
    (WeilConjectures.scalarAdjunction l E L ι Y n)).unit M U x
  change ((completedFiniteAssociation l E L ι Y n).hom.app M).val.app U
    (((scalarReductionExtension_adjunction l L Y n).choose.unit.app
      ((integralOrdinaryScalar l E L ι Y).obj M)).val.app U
        (((completedScalarAdj l E L ι Y).unit.app M).val.app U x)) =
    ((WeilConjectures.scalarAdjunction l E L ι Y n).unit.app M).val.app U x at h
  have ha := completedScalarAdj_unit l E L ι Y M U x
  have hb := finiteReductionUnit l L Y ((integralOrdinaryScalar l E L ι Y).obj M) n U
    (integralOrdinaryTensorSection l E L ι Y M U 1 x)
  have hc := WeilConjectures.scalarAdjunction_unit l E L ι Y n M U x
  have he := (congrArg (fun z ↦
    ((scalarReductionExtension_adjunction l L Y n).choose.unit.app
      ((integralOrdinaryScalar l E L ι Y).obj M)).val.app U z) ha).trans hb
  exact (congrArg (fun z ↦
    ((completedFiniteAssociation l E L ι Y n).hom.app M).val.app U z) he).symm.trans
      (h.trans hc)

attribute [local irreducible] completedFiniteAssociation

private theorem directTensor_smul (Y : Scheme.{u}) (n : ℕ)
    (M : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : M.val.obj U) :
    integralScalarTensorSection l E L ι Y n M U s x =
      s • integralScalarTensorSection l E L ι Y n M U 1 x := by
  unfold integralScalarTensorSection
  rw [WeilConjectures.tensorSection_smul.{u + 1, u, u} (f := integralScalarRho l E L ι Y n)]
  exact (((integralScalarReductionIso l E L ι Y n).inv.app M).val.app U).hom.map_smul _ _

private def completedOrdinaryEvaluation (Y : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l L Y) (n : ℕ) :
    integralOrdinaryScalar l E L ι Y ⋙ M.tensor ⋙ coefficientSequenceEvaluation l L Y n ≅
      integralScalarReduction l E L ι Y n :=
  Functor.isoWhiskerLeft (integralOrdinaryScalar l E L ι Y) (M.evaluation n) ≪≫
    completedFiniteAssociation l E L ι Y n

private theorem completedOrdinaryEvaluation_inverse (Y : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l L Y) (n : ℕ)
    (K : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : K.val.obj U) :
    ((completedOrdinaryEvaluation l E L ι Y M n).inv.app K).val.app U
      (integralScalarTensorSection l E L ι Y n K U s x) =
      s • CoefficientExtensionAssociation.quotientUnitSection l L Y M
        ((integralOrdinaryScalar l E L ι Y).obj K) n U
        (integralOrdinaryTensorSection l E L ι Y K U 1 x) := by
  rw [directTensor_smul, map_smul]
  congr 1
  have h := completedFiniteAssociation_unit l E L ι Y n K U x
  have hc := congrArg
    (fun z ↦ ((completedFiniteAssociation l E L ι Y n).inv.app K).val.app U z) h
  have hi := congrArg (fun z ↦ z.val.app U
    (unrestrictedIntegralTensorSection l L Y n
      ((integralOrdinaryScalar l E L ι Y).obj K) U 1
      (integralOrdinaryTensorSection l E L ι Y K U 1 x)))
    ((completedFiniteAssociation l E L ι Y n).app K).hom_inv_id
  dsimp only [completedOrdinaryEvaluation, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv]
  change ((M.evaluation n).inv.app _).val.app U
    (((completedFiniteAssociation l E L ι Y n).inv.app K).val.app U
      (integralScalarTensorSection l E L ι Y n K U 1 x)) = _
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply,
    Iso.app_hom, Iso.app_inv] at hi
  rw [← hc, hi]
  unfold CoefficientExtensionAssociation.quotientUnitSection
  rw [OrdinaryScalarTowerProof.finiteUnit_eq]

private theorem completedOrdinaryEvaluation_transition (Y : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l L Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) (i : ℤ)
    (U : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l L Y (n + 1)).obj
      (M.tensor.obj ((integralOrdinaryScalar l E L ι Y).obj (P.X i)))).val.obj U) :
    HEq (((coefficientSequenceTransition l L Y (Nat.le_succ n)).app
      (M.tensor.obj ((integralOrdinaryScalar l E L ι Y).obj (P.X i)))).val.app U x)
      (((completedOrdinaryEvaluation l E L ι Y M n).inv.app (P.X i)).val.app U
        ((((integralScalarTransition l E L ι Y n).app P).f i).val.app U
          (((completedOrdinaryEvaluation l E L ι Y M (n + 1)).hom.app
            (P.X i)).val.app U x))) := by
  apply WeilConjectures.tensorTransition_of_generators l E L ι Y
    (M.tensor.obj ((integralOrdinaryScalar l E L ι Y).obj (P.X i))) P n i
    (fun k ↦ (completedOrdinaryEvaluation l E L ι Y M k).app (P.X i))
    ?_ U x
  intro V s y
  let K := (integralOrdinaryScalar l E L ι Y).obj (P.X i)
  let z := integralOrdinaryTensorSection l E L ι Y (P.X i) V 1 y
  let τ := (coefficientSequenceTransition l L Y (Nat.le_succ n)).app (M.tensor.obj K)
  let r := (integralCoefficientSheafTransition l L Y n).hom.app V s
  have hi := completedOrdinaryEvaluation_inverse l E L ι Y M (n + 1) (P.X i) V s y
  have hj := completedOrdinaryEvaluation_inverse l E L ι Y M n (P.X i) V r y
  have hs : (normalizedDVRQuotient l L Y (Nat.le_succ n)).hom.app V s = r :=
    congrArg (fun f ↦ f.hom.app V s)
      (Functor.ofOpSequence_map_homOfLE_succ (integralCoefficientSheafTransition l L Y) n)
  exact CoefficientExtensionAssociation.map_balanced_units
    (normalizedDVRQuotient l L Y (Nat.le_succ n)) τ V s r
    (((completedOrdinaryEvaluation l E L ι Y M (n + 1)).inv.app (P.X i)).val.app V
      (integralScalarTensorSection l E L ι Y (n + 1) (P.X i) V s y))
    (CoefficientExtensionAssociation.quotientUnitSection l L Y M K (n + 1) V z)
    (((completedOrdinaryEvaluation l E L ι Y M n).inv.app (P.X i)).val.app V
      (integralScalarTensorSection l E L ι Y n (P.X i) V r y))
    (CoefficientExtensionAssociation.quotientUnitSection l L Y M K n V z) hs hi hj
    (CoefficientExtensionAssociation.quotientUnitSection_transition l L Y M K n V z)

private theorem strictScalarAssociation (Y : Scheme.{u})
    (A : CoefficientExtensionSystems l E L ι Y)
    (ME : CompletionUnit.OrdinaryModel l E Y)
    (ML : CompletionUnit.OrdinaryModel l L Y)
    (ρ : ∀ n, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L Y n ≅
      coefficientSequenceEvaluation l E Y n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι Y A ρ)
    (association : ∀ n, scalarReductionExtension l E Y n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι Y n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι Y A association) :
    let := coefficientScalarModelZero A.scalar
    let F := ME.quotient l E Y ⋙ A.scalar.model.E.mapHomologicalComplex (.up ℤ)
    let G := (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ) ⋙
      ML.quotient l L Y
    let a := OrdinaryScalarTowerProof.directEvaluation l E L ι Y A ME ρ association
    let b (n : ℕ) : G ⋙
        (coefficientSequenceEvaluation l L Y n).mapHomologicalComplex (.up ℤ) ≅
        integralScalarFiniteComplex l E L ι Y n :=
      NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
        (fun i ↦ (completedOrdinaryEvaluation l E L ι Y ML n).app (P.X i))
        (by intro i j _hij; exact
          ((completedOrdinaryEvaluation l E L ι Y ML n).hom.naturality (P.d i j)).symm))
        (by intro P Q f; apply HomologicalComplex.hom_ext; intro i
            exact (completedOrdinaryEvaluation l E L ι Y ML n).hom.naturality (f.f i))
    ∃ β : F ≅ G, ∀ P n,
      ((coefficientSequenceEvaluation l L Y n).mapHomologicalComplex (.up ℤ)).map
        (β.hom.app P) = (a n).hom.app P ≫ (b n).inv.app P := by
  classical
  dsimp only
  let := coefficientScalarModelZero A.scalar
  let F := ME.quotient l E Y ⋙ A.scalar.model.E.mapHomologicalComplex (.up ℤ)
  let G := (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ) ⋙
    ML.quotient l L Y
  let a := OrdinaryScalarTowerProof.directEvaluation l E L ι Y A ME ρ association
  let b (n : ℕ) : G ⋙
      (coefficientSequenceEvaluation l L Y n).mapHomologicalComplex (.up ℤ) ≅
      integralScalarFiniteComplex l E L ι Y n :=
    NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (completedOrdinaryEvaluation l E L ι Y ML n).app (P.X i))
      (by intro i j _hij; exact
        ((completedOrdinaryEvaluation l E L ι Y ML n).hom.naturality (P.d i j)).symm))
      (by intro P Q f; apply HomologicalComplex.hom_ext; intro i
          exact (completedOrdinaryEvaluation l E L ι Y ML n).hom.naturality (f.f i))
  let e (n : ℕ) := a n ≪≫ (b n).symm
  have hs := OrdinaryScalarTowerProof.directTransition l E L ι Y A ME ρ hρ
    association hassociation
  have he (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) (i : ℤ) :
      ((e (n + 1)).hom.app P).f i ≫
          (coefficientSequenceTransition l L Y (Nat.le_succ n)).app ((G.obj P).X i) =
        (coefficientSequenceTransition l L Y (Nat.le_succ n)).app ((F.obj P).X i) ≫
          (normalizedDVRModuleRes l L Y (Nat.le_succ n)).map
            (((e n).hom.app P).f i) := by
    exact WeilConjectures.successor_square l L Y ((F.obj P).X i) ((G.obj P).X i)
      (fun k ↦ ((integralScalarFiniteComplex l E L ι Y k).obj P).X i)
      (fun k ↦ HomologicalComplex.Hom.isoApp ((a k).app P) i)
      (fun k ↦ HomologicalComplex.Hom.isoApp ((b k).app P) i)
      (fun k U x ↦ (((integralScalarTransition l E L ι Y k).app P).f i).val.app U x)
      (fun k U x ↦ hs P k i U x)
      (fun k U x ↦ completedOrdinaryEvaluation_transition l E L ι Y ML P k i U x) n
  exact WeilConjectures.complexIsoOfSuccessor l L Y F G e he

/-- Scalar extension carries a coherent ordinary quotient presentation to the
ordinary quotient of completed scalar extension, with its tensor-unit coordinates.
Source: Stacks 03EK, 03D7, 06YY and 07A4; scalar association in the quotient
calculation of step 8 of scalar-extension tower coherence.
(blueprint: lem-trf-scalar-ordinary-presentation-coordinates).

Proof: associate completed scalar extension followed by finite reduction with direct
finite scalar extension by uniqueness of normalized tensor adjoints. The unit equation
fixes its tensor generators. Linearity and compatibility of quotient units with the
successor maps identify the transitions. Compare with finite sequence scalar extension
and glue the successor squares into a strict sequence isomorphism on complexes.
Transport it along the given presentation isomorphism. Naturality of the scalar unit
and the prescribed finite presentation comparisons give the displayed coordinate formula.
No flatness is used: the same tensor formulas cover zero complexes, n=0, empty sites,
identity embeddings and ramified coefficient extensions. -/
theorem scalarOrdinaryPresentationCoordinates (Y : Scheme.{u})
    (A : CoefficientExtensionSystems l E L ι Y)
    (ME : CompletionUnit.OrdinaryModel l E Y)
    (ML : CompletionUnit.OrdinaryModel l L Y)
    (ρ : ∀ n, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L Y n ≅
      coefficientSequenceEvaluation l E Y n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι Y A ρ)
    (association : ∀ n, scalarReductionExtension l E Y n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι Y n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι Y A association)
    (F : coefficientSequenceModules l E Y ⥤ coefficientSequenceModules l L Y)
    [F.Additive] (hF : A.scalar.model.E = F)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (a : (ME.quotient l E Y).obj P ≅ C)
    (κ : ∀ n, ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
      (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (hκ : ∀ n,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        κ n = (NatIso.mapHomologicalComplex (ME.evaluation n) (.up ℤ)).app P) :
    ∃ v : (F.mapHomologicalComplex (.up ℤ)).obj C ≅
      (ML.quotient l L Y).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P),
      ∀ (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ) (x : (P.X i).val.obj U)
        (y : (F.obj (C.X i)).val.obj (op (n, U.unop))),
        HEq y ((A.scalar.ordinaryAdjunction.unit.app (C.X i)).val.app
          (op (n, U.unop)) (integralComparisonSequenceSection l E Y (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l E Y n (P.X i) U 1 x)))) →
        (((coefficientSequenceEvaluation l L Y n).map (v.hom.f i) ≫
            (ML.evaluation n).hom.app ((integralOrdinaryScalar l E L ι Y).obj (P.X i))).val.app
          U (coefficientEvaluationSection l L Y (F.obj (C.X i)) n U y)) =
        unrestrictedIntegralTensorSection l L Y n
          ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) U 1
          (integralOrdinaryTensorSection l E L ι Y (P.X i) U 1 x) := by
  subst F
  let := coefficientScalarModelZero A.scalar
  obtain ⟨β, hβ⟩ := strictScalarAssociation l E L ι Y A ME ML ρ hρ
    association hassociation
  let v := (A.scalar.model.E.mapHomologicalComplex (.up ℤ)).mapIso a.symm ≪≫ β.app P
  refine ⟨v, ?_⟩
  intro n i U x y hy
  let w := integralComparisonSequenceSection l E Y (C.X i) n U
    (((κ n).inv.f i).val.app U
      (unrestrictedIntegralTensorSection l E Y n (P.X i) U 1 x))
  let z := CoefficientExtensionAssociation.quotientUnitSection l E Y ME (P.X i) n U x
  have hp := OrdinaryScalarTowerProof.presentationUnit l E Y ME P C a κ hκ n i U x
  have hn := congrArg (fun f ↦ f.val.app (op (n, U.unop)) w)
    (A.scalar.ordinaryAdjunction.unit.naturality (a.inv.f i))
  change (A.scalar.ordinaryAdjunction.unit.app (ME.tensor.obj (P.X i))).val.app
      (op (n, U.unop)) ((a.inv.f i).val.app (op (n, U.unop)) w) =
    (A.scalar.model.E.map (a.inv.f i)).val.app (op (n, U.unop))
      ((A.scalar.ordinaryAdjunction.unit.app (C.X i)).val.app (op (n, U.unop)) w) at hn
  rw [hp] at hn
  have hu : coefficientEvaluationSection l L Y
      (A.scalar.model.E.obj (ME.tensor.obj (P.X i))) n U
      ((A.scalar.model.E.map (a.inv.f i)).val.app (op (n, U.unop)) y) =
      CoefficientExtensionAssociation.evaluatedUnitSection l E L ι Y A ρ
        (ME.tensor.obj (P.X i)) n U z := by
    rw [eq_of_heq hy, ← hn]
    exact eq_of_heq ((OrdinaryScalarTowerProof.evaluation_section_heq l L
      (A.scalar.model.E.obj (ME.tensor.obj (P.X i))) n U _).trans
      (CoefficientExtensionAssociation.evaluatedUnitSection_raw l E L ι Y A ρ hρ
        (ME.tensor.obj (P.X i)) n U z).symm)
  have hh := congrArg (fun k ↦ (k.f i).val.app U
    (CoefficientExtensionAssociation.evaluatedUnitSection l E L ι Y A ρ
      (ME.tensor.obj (P.X i)) n U z)) (hβ P n)
  change ((coefficientSequenceEvaluation l L Y n).map ((β.hom.app P).f i)).val.app U
      (CoefficientExtensionAssociation.evaluatedUnitSection l E L ι Y A ρ
        (ME.tensor.obj (P.X i)) n U z) =
    ((completedOrdinaryEvaluation l E L ι Y ML n).inv.app (P.X i)).val.app U
      (((OrdinaryScalarTowerProof.finiteComparison l E L ι Y A ME ρ association n).hom.app
        (P.X i)).val.app U
          (CoefficientExtensionAssociation.evaluatedUnitSection l E L ι Y A ρ
            (ME.tensor.obj (P.X i)) n U z)) at hh
  have hf := OrdinaryScalarTowerProof.finiteComparison_unit l E L ι Y A ME ρ
    association hassociation (P.X i) n U 1 x
  rw [one_smul] at hf
  rw [hf, completedOrdinaryEvaluation_inverse, one_smul] at hh
  change ((ML.evaluation n).hom.app _).val.app U
    (((coefficientSequenceEvaluation l L Y n).map
      ((A.scalar.model.E.map (a.inv.f i)) ≫ (β.hom.app P).f i)).val.app U
        (coefficientEvaluationSection l L Y (A.scalar.model.E.obj (C.X i)) n U y)) = _
  rw [Functor.map_comp]
  change ((ML.evaluation n).hom.app _).val.app U
    (((coefficientSequenceEvaluation l L Y n).map ((β.hom.app P).f i)).val.app U
      (((coefficientSequenceEvaluation l L Y n).map
        (A.scalar.model.E.map (a.inv.f i))).val.app U
          (coefficientEvaluationSection l L Y (A.scalar.model.E.obj (C.X i)) n U y))) = _
  rw [OrdinaryScalarTowerProof.evaluation_map_section]
  erw [hu, hh]
  exact (CoefficientExtensionAssociation.quotientUnitSection_evaluation l L Y ML
    ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) n U
    (integralOrdinaryTensorSection l E L ι Y (P.X i) U 1 x)).trans
      (OrdinaryScalarTowerProof.finiteUnit_eq l L Y
        ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) n U
        (integralOrdinaryTensorSection l E L ι Y (P.X i) U 1 x))

end WeilConjectures.ScalarExtensionTower
