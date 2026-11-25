/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryQuotientIso
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
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
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Normalization of strict finite scalar tensors

Source: Stacks 03EK, 03D7, 06YY, 07A6 and 0941; the integral-operations
coefficient-extension proof, step 3 of stage3-pur-extension-strict-representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard integralScalarReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

private theorem finiteScalar_isKFlat
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l L W n)
      ((integralScalarFiniteComplex l E L ι W n).obj P.obj) := by
  let : (integralScalarReduction l E L ι W n).Additive :=
    integralScalarReduction_additive l E L ι W n
  apply (SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (integralScalarRho l E L ι W n) P.obj
    (integralScalarReduction l E L ι W n)
    (integralScalarReduction_obj l E L ι W n)
    (fun f ↦ integralScalarReduction_map l E L ι W n f) P.property.1 ?_).1
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso
      (completedIntegralCommRingSheafUnrestricted l E W) (P.obj.X i)) (P.property.2 i)

set_option synthInstance.maxSize 256 in
open MonoidalCategory in
private theorem isKFlat_of_iso
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{r}}
    {P Q : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (e : P ≅ Q) (hP : P.IsKFlatIndependentCoefficients) : Q.IsKFlatIndependentCoefficients := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  intro A hA n
  let F := (curriedTensor (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let e' : CochainComplex.mapBifunctor A P (curriedTensor _) ≅
      CochainComplex.mapBifunctor A Q (curriedTensor _) :=
    HomologicalComplex₂.total.mapIso ((F.obj A).mapIso e) (ComplexShape.up ℤ)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hP A hA n)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e').symm |>
      (HomologicalComplex.exactAt_iff_isZero_homology _ n).2

private theorem strictTransition_localization {m n : ℕ} (h : n ≤ m)
    (X : CochainComplex (coefficientSequenceModules l L W) ℤ) :
    (coefficientSequenceDerivedTransition l L W h).app (DerivedCategory.Q.obj X) ≫
      (normalizedDVRRes l L W h).map
        ((coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app X) ≫
      (normalizedDVRModuleRes l L W h).mapDerivedCategoryFactors.hom.app
        (((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj X) =
    (coefficientSequenceEvaluation l L W m).mapDerivedCategoryFactors.hom.app X ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (coefficientSequenceTransition l L W h) (.up ℤ)).app X) := by
  have he : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (coefficientSequenceEvaluation l L W n ⋙ normalizedDVRModuleRes l L W h))
      (.up ℤ)).hom.app X = 𝟙 _ := by
    ext i
    simp
  have hf := Functor.mapDerivedCategoryCompIso_fac
    (coefficientSequenceEvaluation l L W n) (normalizedDVRModuleRes l L W h) X
  erw [he, CategoryTheory.Functor.map_id, Category.comp_id] at hf
  unfold coefficientSequenceDerivedTransition
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, hf]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rfl

/-- Normalization for a good representative with its actual quotient transitions.

Source: Stacks 03D7, 06YY, 07A6 and 0941; step 3 of
stage3-pur-extension-strict-representatives
(blueprint: stage3-pur-extension-strict-tensor-normalized).

Proof: fix m at least n and a good representative P. Change of rings sends P
to a flat-term K-flat complex over the mth L-quotient, even for a ramified
extension E to L. Thus derived extension from level m to level n is computed by
ordinary tensor on that representative. Balanced tensor association gives an
isomorphism (B_m tensor_R P) tensor_{B_m} B_n to B_n tensor_R P; its inverse
inserts 1 in the middle factor. Both maps commute with differentials and with
restriction to objects of the site. Under directEvaluation the successor maps
are the prescribed quotient tensor maps by htransition. Compose the successor
equations (and use identity for m=n) to identify the actual m-to-n transition.
The normalized tensor/restriction adjunction sends this transition to the
balanced associator just constructed: check on each local tensor b tensor x,
where both maps reduce b and retain x. Local tensor generation and
sheafification give the equality of chain maps, and localization preserves it.
The adjunct is therefore invertible. Composition with its isomorphism followed
by the derived tensor/restriction Hom equivalence is the Hom map in the
normalization predicate, so that map is bijective for every target object.
No boundedness and no flatness of B_m to B_n is used. -/
theorem coefficientExtensionStrictTensor_normalized
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (htransition : IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    IsNormalizedCoefficientSequence l L W (DerivedCategory.Q.obj (direct.obj P)) := by
  obtain ⟨S, _⟩ := coefficientDerivedSystemEvaluationCalculus l L W
  let D := S.quotientCalculus
  let X := direct.obj P
  let C (n : ℕ) :=
    ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj X
  have hC (n : ℕ) : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l L W n) (C n) :=
    isKFlat_of_iso ((directEvaluation n).app P).symm
      (finiteScalar_isKFlat l E L ι W P n)
  intro m n h Z
  obtain ⟨a, ha⟩ := coefficientExtensionOrdinaryQuotientIso l E L ι W
    h (D.ordinaryAdjunction h) (D.ordinary_unit h) P.obj X
    (fun n ↦ (directEvaluation n).app P) (htransition P)
  let R := normalizedDVRRes l L W h
  let em := (coefficientSequenceEvaluation l L W m).mapDerivedCategoryFactors.app X
  let en := (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.app X
  let q := coefficientFiniteQuotientModel l L W h (C m) (hC m)
  let b := q ≪≫ DerivedCategory.Q.mapIso a
  have hu : (D.adjunction h).unit.app (DerivedCategory.Q.obj (C m)) ≫
      R.map b.hom ≫ (normalizedDVRModuleRes l L W h).mapDerivedCategoryFactors.hom.app
        (C n) = DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (coefficientSequenceTransition l L W h)
        (.up ℤ)).app X) := by
    calc
      _ = ((D.adjunction h).unit.app (DerivedCategory.Q.obj (C m)) ≫
          R.map q.hom ≫
          (normalizedDVRModuleRes l L W h).mapDerivedCategoryFactors.hom.app
            (((coefficientFiniteQuotientExtension l L W h).mapHomologicalComplex
              (.up ℤ)).obj (C m))) ≫
          DerivedCategory.Q.map
            (((normalizedDVRModuleRes l L W h).mapHomologicalComplex (.up ℤ)).map a.hom) := by
        simp only [b, Iso.trans_hom, Functor.mapIso_hom, R.map_comp, Category.assoc]
        have hn := (normalizedDVRModuleRes l L W h).mapDerivedCategoryFactors.hom.naturality
          a.hom
        dsimp only [Functor.comp_map] at hn
        have hn' : R.map (DerivedCategory.Q.map a.hom) ≫
            (normalizedDVRModuleRes l L W h).mapDerivedCategoryFactors.hom.app (C n) =
          (normalizedDVRModuleRes l L W h).mapDerivedCategoryFactors.hom.app
              (((coefficientFiniteQuotientExtension l L W h).mapHomologicalComplex
                (.up ℤ)).obj (C m)) ≫
            DerivedCategory.Q.map
              (((normalizedDVRModuleRes l L W h).mapHomologicalComplex (.up ℤ)).map a.hom) := hn
        rw [hn']
      _ = _ := by
        rw [D.unit_model h (C m) (hC m), ← DerivedCategory.Q.map_comp, ha]
  let c : (coefficientFiniteQuotientDerived l L W h).obj
      ((coefficientSequenceDerivedEvaluation l L W m).obj (DerivedCategory.Q.obj X)) ≅
        (coefficientSequenceDerivedEvaluation l L W n).obj (DerivedCategory.Q.obj X) :=
    (coefficientFiniteQuotientDerived l L W h).mapIso em ≪≫ b ≪≫ en.symm
  have hc : ((D.adjunction h).homEquiv _ _ c.hom) ≫ R.map en.hom =
      em.hom ≫ ((D.adjunction h).homEquiv _ _ b.hom) := by
    calc
      _ = ((D.adjunction h).homEquiv _ _) (c.hom ≫ en.hom) :=
        ((D.adjunction h).homEquiv_naturality_right c.hom en.hom).symm
      _ = ((D.adjunction h).homEquiv _ _)
          ((coefficientFiniteQuotientDerived l L W h).map em.hom ≫ b.hom) := by
        have he : c.hom ≫ en.hom =
            (coefficientFiniteQuotientDerived l L W h).map em.hom ≫ b.hom := by
          simp only [c, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
            en.inv_hom_id]
          erw [Category.comp_id]
        dsimp only [coefficientSequenceDerivedEvaluation, Functor.comp_obj]
        rw [he]
      _ = _ := (D.adjunction h).homEquiv_naturality_left em.hom b.hom
  have ht : (coefficientSequenceDerivedTransition l L W h).app
      (DerivedCategory.Q.obj X) = (D.adjunction h).homEquiv _ _ c.hom := by
    apply (cancel_mono (R.map en.hom)).1
    apply (cancel_mono
      ((normalizedDVRModuleRes l L W h).mapDerivedCategoryFactors.hom.app (C n))).1
    rw [hc, Adjunction.homEquiv_apply]
    simpa only [C, em, en, R, Functor.comp_obj, Iso.app_hom, Category.assoc] using
      (strictTransition_localization l L W h X).trans
        (congrArg (fun f ↦ em.hom ≫ f) hu.symm)
  have hb := ((Iso.homCongr c.symm (Iso.refl Z)).trans
    ((D.adjunction h).homEquiv _ Z)).bijective
  change Function.Bijective
    (fun f ↦ ((D.adjunction h).homEquiv _ Z) (c.hom ≫ f ≫ 𝟙 Z)) at hb
  simpa only [Category.comp_id, Adjunction.homEquiv_naturality_right, ← ht] using hb

end WeilConjectures
