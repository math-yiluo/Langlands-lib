/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
import WeilConjectures.TraceFormula.Supporting.RoosAdjunctionTranspose
import WeilConjectures.TraceFormula.Scalar.ScalarIdentityRoosAugmentation
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Scalar model normalization before inverting completion

Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1;
Stacks Project, Tags 06YY and 0941.
(blueprint: lem-trf-scalar-model-unit)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u})

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel integralScalarExtensionOfUniverses
  completedIntegralCoefficientSheafUnrestricted

private theorem systemUnit_on_complex
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ) :
    (integralComparisonSystemScalarUnit l E X).hom.app (DerivedCategory.Q.obj C) =
      (integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X).ε.app C ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (integralComparisonSequenceScalarUnit l E X)
            (.up ℤ)).hom.app C) := by
  let m := integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X
  let μ := NatIso.mapHomologicalComplex (integralComparisonSequenceScalarUnit l E X) (.up ℤ)
  let α := Functor.whiskerLeft DerivedCategory.Q
    (integralComparisonSystemScalarUnit l E X).hom
  let β := m.ε ≫ Functor.whiskerRight μ.hom DerivedCategory.Q
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E X) C
  let := hf
  have hP' := (integralComparisonSystemScalarUnit_existsUnique l E X).exists.choose_spec P hP
  change α.app P = β.app P at hP'
  change α.app C = β.app C
  apply (cancel_epi (m.T.map (DerivedCategory.Q.map f))).1
  exact (α.naturality f).trans (by rw [hP']; exact (β.naturality f).symm)

private theorem scalarModelUnit_onGood
    (SE : CoefficientDerivedSystemCalculus l E X)
    (ρE : IntegralComparisonRoosModel l E X)
    (bEE : IntegralComparisonScalarModel l E E (AlgHom.id ℚ_[l] E) X SE ρE)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).app
        (DerivedCategory.Q.obj P.obj) ≫
      bEE.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (coefficientSequenceLimit l E X).map
        ((integralComparisonSystemScalarUnit l E X).hom.app
          (SE.reduction.obj (DerivedCategory.Q.obj P.obj))) =
    (CompletedLineTensor.ordinaryUnit l E X).hom.app (DerivedCategory.Q.obj P.obj) ≫
      SE.adjunction.unit.app (DerivedCategory.Q.obj P.obj) := by
  classical
  let R := coefficientSequenceRestriction l E X
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let L := coefficientSequenceLimit l E X
  let H := coefficientConstantTowerLimit l E X
  let m := integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X
  let T := integralComparisonDerivedSequenceScalar l E E (AlgHom.id ℚ_[l] E) X
  let U := integralComparisonSystemScalarUnit l E X
  let μ := NatIso.mapHomologicalComplex (integralComparisonSequenceScalarUnit l E X) (.up ℤ)
  let δ := (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
    ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategoryFactors
  let A := integralComparisonConstantAdjunction l E X
  obtain ⟨C, e, κ, hp, hc⟩ := coherentPrimitiveReductionPresentation l E SE P
  obtain ⟨q, hq, hn⟩ := bEE.normalization P C e κ hp hc
  rw [IsIntegralComparisonPresentationCoherent] at hc
  obtain ⟨b, hb, hc⟩ := hc
  let D := (m.E.mapHomologicalComplex (.up ℤ)).obj C
  let cunit : D ≅ C := μ.app C
  let v : C ⟶ D := cunit.inv
  let w : D ⟶ C := cunit.hom
  let k := L.map (U.inv.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫
    L.map (T.map e.hom) ≫ L.map (m.ε.app C) ≫
    (integralComparisonRoosBridge l E X ρE D).hom ≫
    DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)
  have hk : IsIso k := by
    have hpost : IsIso
        (L.map (T.map e.hom) ≫ L.map (m.ε.app C) ≫
          (integralComparisonRoosBridge l E X ρE D).hom ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)) := by
      exact IsIso.of_isIso_fac_left hn
    dsimp only [k]
    infer_instance
  apply (cancel_mono k).1
  have hχ := (finiteFreeCompletedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).2.2 P
  have hμ := (CompletedLineTensor.ordinaryUnit_existsUnique l E X).exists.choose_spec P
  change (CompletedLineTensor.ordinaryUnit l E X).hom.app _ = _ at hμ
  have hv : v ≫ w = 𝟙 C := cunit.inv_hom_id
  have hs : U.inv.app (DerivedCategory.Q.obj C) ≫ m.ε.app C =
      DerivedCategory.Q.map v := by
    have hu := systemUnit_on_complex l E X C
    change U.hom.app (DerivedCategory.Q.obj C) =
      m.ε.app C ≫ DerivedCategory.Q.map w at hu
    apply (cancel_mono (DerivedCategory.Q.map w)).1
    calc
      _ = 𝟙 (DerivedCategory.Q.obj C) := by
        rw [Category.assoc, ← hu]
        exact U.inv_hom_id_app _
      _ = _ := by rw [← DerivedCategory.Q.map_comp, hv, CategoryTheory.Functor.map_id]
  have ha :
      SE.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫ L.map e.hom =
        A.homEquiv _ _ (δ.hom.app P.obj ≫ DerivedCategory.Q.map b ≫
          R.mapDerivedCategoryFactors.inv.app C) := by
    have hc' : (A.homEquiv (DerivedCategory.Q.obj P.obj)
        (R.mapDerivedCategory.obj (DerivedCategory.Q.obj C))).symm
        (SE.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫ L.map e.hom) =
        δ.hom.app P.obj ≫ DerivedCategory.Q.map b ≫
          R.mapDerivedCategoryFactors.inv.app C := hc
    exact (Equiv.symm_apply_eq (A.homEquiv (DerivedCategory.Q.obj P.obj)
      (R.mapDerivedCategory.obj (DerivedCategory.Q.obj C)))).1 hc'
  have ht := integralComparisonRoosTranspose l E X ρE P.obj (Rc.obj D)
    (b ≫ Rc.map v)
  have hchain :
      ((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E X)).mapHomologicalComplex
        (.up ℤ)).homEquiv P.obj (Rc.obj D) (b ≫ Rc.map v) ≫
        integralComparisonLimitToRoos l E X (Rc.obj D) ≫
        integralOperationsRoosFunctor.map q.hom =
      (completedScalarIdentityUnit l E X).app P.obj :=
    scalarIdentityRoosAugmentation l E X P.obj C κ b hb q hq
  have hz : R.mapDerivedCategoryFactors.inv.app C ≫
      R.mapDerivedCategory.map (DerivedCategory.Q.map v) ≫
        R.mapDerivedCategoryFactors.hom.app D =
      DerivedCategory.Q.map (Rc.map v) := by
    rw [R.mapDerivedCategoryFactors_hom_naturality v]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rfl
  have hfac :
      (A.homEquiv _ _ (δ.hom.app P.obj ≫ DerivedCategory.Q.map b ≫
        R.mapDerivedCategoryFactors.inv.app C) ≫
        H.map (R.mapDerivedCategory.map (DerivedCategory.Q.map v)) ≫
        H.map (R.mapDerivedCategoryFactors.hom.app D)) =
      A.homEquiv _ _ (δ.hom.app P.obj ≫
        DerivedCategory.Q.map (b ≫ Rc.map v)) := by
    rw [← Category.assoc, ← A.homEquiv_naturality_right,
      ← A.homEquiv_naturality_right]
    congr 1
    simp only [Category.assoc, hz, CategoryTheory.Functor.map_comp]
  have heU : U.inv.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
      T.map e.hom = e.hom ≫ U.inv.app (DerivedCategory.Q.obj C) :=
    (U.inv.naturality e.hom).symm
  have hunit : SE.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫ k =
      DerivedCategory.Q.map ((completedScalarIdentityUnit l E X).app P.obj) := by
    calc
      _ = (SE.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫ L.map e.hom) ≫
          L.map (U.inv.app (DerivedCategory.Q.obj C) ≫ m.ε.app C) ≫
          (integralComparisonRoosBridge l E X ρE D).hom ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) := by
        dsimp only [k]
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
        rw [← L.map_comp_assoc, heU, L.map_comp]
        simp only [Category.assoc]
      _ = (A.homEquiv _ _ (δ.hom.app P.obj ≫ DerivedCategory.Q.map b ≫
            R.mapDerivedCategoryFactors.inv.app C) ≫
            H.map (R.mapDerivedCategory.map (DerivedCategory.Q.map v)) ≫
            H.map (R.mapDerivedCategoryFactors.hom.app D)) ≫
          ρE.comparison.hom.app (Rc.obj D) ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) := by
        rw [ha, hs]
        simp only [L, coefficientSequenceLimit, coefficientSequenceDerivedRestriction,
          Functor.comp_map, integralComparisonRoosBridge, Iso.trans_hom,
          Functor.mapIso_hom, Iso.app_hom, Category.assoc]
        rfl
      _ = (A.homEquiv _ _ (δ.hom.app P.obj ≫
            DerivedCategory.Q.map (b ≫ Rc.map v))) ≫
          ρE.comparison.hom.app (Rc.obj D) ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) := by rw [hfac]
      _ = DerivedCategory.Q.map
          (((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E X)).mapHomologicalComplex
              (.up ℤ)).homEquiv P.obj _
              (b ≫ Rc.map v) ≫ integralComparisonLimitToRoos l E X _) ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) := by
        rw [← Category.assoc, ht]
      _ = _ := by rw [← CategoryTheory.Functor.map_comp, Category.assoc, hchain]
  -- Cancel the scalar-unit factors before using the realization normalization.
  have hcancel :
      L.map (U.hom.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫
        L.map (U.inv.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫
        L.map (T.map e.hom) ≫ L.map (m.ε.app C) ≫
        (integralComparisonRoosBridge l E X ρE D).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
      L.map (T.map e.hom) ≫ L.map (m.ε.app C) ≫
        (integralComparisonRoosBridge l E X ρE D).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) :=
    (L.mapIso (U.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj)))).hom_inv_id_assoc _
  calc
    _ = (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).app
          (DerivedCategory.Q.obj P.obj) ≫
        (integralScalarExtensionComparisonOfUniverses l E E
          (AlgHom.id ℚ_[l] E) X).hom.app P := by
      dsimp only [k]
      simp only [Category.assoc]
      rw [hcancel]
      exact congrArg (_ ≫ ·) hn
    _ = (CompletedLineTensor.ordinaryUnit l E X).hom.app
          (DerivedCategory.Q.obj P.obj) ≫
        DerivedCategory.Q.map ((completedScalarIdentityUnit l E X).app P.obj) := by
      rw [hμ, Category.assoc]
      exact hχ
    _ = _ := by rw [← hunit, Category.assoc]

/-- The normalized scalar identity model sends the ordinary multiplication unitor
to the actual reduction-realization unit, before completion is inverted.
Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1;
Stacks 06YY, 0941, the scalar calculation in step 11 of the parent.
(blueprint: lem-trf-scalar-model-unit)

Proof: on a flat-term K-flat representative P, use a simultaneous strict quotient
presentation with whole-tower adjunction coherence. Normalize the scalar realization
on this same presentation. Extend the system scalar-unit formula from K-flat
complexes to arbitrary complexes by a K-flat resolution and naturality. Its inverse
followed by the scalar counit is therefore the localization of inverse ordinary
multiplication. The coherent presentation and the strict constant/limit adjunction
identify the actual unit with a strict compatible family. The normalized Roos
comparison takes its adjunct to the ordinary limit lift; tensor insertion and the
normalization of the scalar-tower identification make its unshifted coordinate
1 tensor x and its shifted coordinate zero. This is completedScalarIdentityUnit.
Postcompose the desired equation with the invertible normalization factor. The
finite-free identity formula and ordinary multiplication-unit normalization identify
both sides. Cancel that factor and extend by essential surjectivity of the good
localization and naturality to every K. No finite-projection faithfulness or inverse
to a chain completion map is used. -/
theorem scalarModelUnit
    (SE : CoefficientDerivedSystemCalculus l E X)
    (ρE : IntegralComparisonRoosModel l E X)
    (bEE : IntegralComparisonScalarModel l E E (AlgHom.id ℚ_[l] E) X SE ρE)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).app K ≫
      bEE.realization.hom.app K ≫
      (coefficientSequenceLimit l E X).map
        ((integralComparisonSystemScalarUnit l E X).hom.app (SE.reduction.obj K)) =
    (CompletedLineTensor.ordinaryUnit l E X).hom.app K ≫ SE.adjunction.unit.app K := by
  classical
  let L := coefficientSequenceLimit l E X
  let U := integralComparisonSystemScalarUnit l E X
  let := integralOperationsGoodLocalization_isLocalization
    l E X
  let := Localization.essSurj (integralOperationsGoodLocalization l E X)
    ((HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E X).ι)
  let P := (integralOperationsGoodLocalization l E X).objPreimage K
  let e := (integralOperationsGoodLocalization l E X).objObjPreimageIso K
  let F := completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X
  let G := SE.reduction ⋙ L
  let α : F ⟶ G := completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X ≫
    bEE.realization.hom ≫ Functor.whiskerLeft SE.reduction (Functor.whiskerRight U.hom L)
  let β : F ⟶ G := (CompletedLineTensor.ordinaryUnit l E X).hom ≫ SE.adjunction.unit
  have hP : α.app ((integralOperationsGoodLocalization l E X).obj P) =
      β.app ((integralOperationsGoodLocalization l E X).obj P) := by
    change α.app (DerivedCategory.Q.obj P.obj) = β.app (DerivedCategory.Q.obj P.obj)
    simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using scalarModelUnit_onGood l E X SE ρE bEE P
  change α.app K = β.app K
  apply (cancel_epi (F.map e.hom)).1
  rw [α.naturality, β.naturality, hP]

end WeilConjectures
