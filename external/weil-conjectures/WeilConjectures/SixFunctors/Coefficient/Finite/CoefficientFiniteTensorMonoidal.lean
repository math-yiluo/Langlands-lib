/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.CategoryTheory.Ringed.RingedScalarTensorMonoidal
import WeilConjectures.SixFunctors.Coefficient.Finite.CoefficientFiniteScalarSection
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Limits.Final

/-! # Monoidality of the fixed finite coefficient tensor comparison

Source: Stacks 06YY and 07A4.
(blueprint: lem-coef-finite-tensor-monoidal).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionExtension
  coefficientTotalTensor
  coefficientFiniteReductionModel coefficientLocalizedCounitModel

attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  CategoryTheory.uniformProd
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralReductionTargetHasDerivedCategory coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat

-- The cochain presentation uses exactly the recorded homotopy counit.
@[reducible] private noncomputable def finiteCochainModel (n : ℕ) :
    SheafOfModules.DerivedChangeOfRingsCochainModel.{t+1, t, max u (t+1),
      max (t+2) (u+1), max (t+2) (u+1)}
      (completedIntegralCommRingProjectionUnrestricted l E W n) := by
  let A := scalarReductionSource l E W
  let B := normalizedDVRModules l E W n
  let F := scalarReductionExtension l E W n
  let : F.Additive := coefficientFiniteExtensionAdditive l E W n
  let T := coefficientFiniteDerivedExtension l E W n
  let ε := scalarReductionCounit l E W n
  let H := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let : H.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := by
    simpa only [H, F, scalarReductionExtension] using
      (scalarReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose_spec.2.1
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) :=
    (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.1
  let q := HomotopyCategory.quotient A (.up ℤ)
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh H T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ H ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β := Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  have hβ := pointwise_change_iso T i j α hα
  refine
    { E := F
      obj_eq := by
        simpa only [F, scalarReductionExtension] using
          (scalarReductionExistence l E W n).choose_spec.choose
      map_eq := by
        intro M N f
        with_unfolding_all exact
          (scalarReductionExistence l E W n).choose_spec.choose_spec.choose f
      additive := coefficientFiniteExtensionAdditive l E W n
      preserves := by
        intro P Q f hP hQ hf
        simpa only [F, scalarReductionExtension] using
          (scalarReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose_spec.1
            f hP hQ hf
      T := T
      pointwise := ?_
      ε := β
      universal := ⟨hβ.isRightKanExtension⟩
      triangulated :=
        (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.2.1
      computes := ?_ }
  · intro X
    exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
        (HomologicalComplex.quasiIso A (.up ℤ)) X).2
      ((hβ _).hasPointwiseRightKanExtensionAt)
  · intro P hP
    have hcomp : IsIso (ε.app (q.obj P)) :=
      coefficientFiniteReductionCounit_isIso l E W P hP n
    let e := T.mapIso (i.app P).symm ≪≫
      @asIso _ _ _ _ (ε.app (q.obj P)) hcomp ≪≫ j.app P
    have he : β.app P = e.hom := by
      with_unfolding_all
        calc
          β.app P = T.map (i.inv.app P) ≫
              (𝟙 _ ≫ ε.app (q.obj P)) ≫ j.hom.app P := rfl
          _ = T.map (i.inv.app P) ≫ ε.app (q.obj P) ≫ j.hom.app P :=
            congrArg (fun f ↦ T.map (i.inv.app P) ≫ f ≫ j.hom.app P)
              (Category.id_comp (ε.app (q.obj P)))
          _ = e.hom := rfl
    change IsIso (β.app P)
    rw [he]
    infer_instance

private theorem finiteCochainModel_counit (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    (finiteCochainModel l E W n).ε.app P =
      (coefficientFiniteReductionModel l E W P hP n).hom := by
  unfold finiteCochainModel coefficientFiniteReductionModel coefficientLocalizedCounitModel
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
  simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp]
  change _ ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ = _
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  rfl

-- Compare the fixed tensorator through its recorded localization model.
/-- The fixed finite tensorator is the inverse tensorator of a monoidal functor.
Source: Stacks 07A4 and 06YY.
(blueprint: lem-coef-finite-tensor-monoidal).

Proof: precompose the recorded homotopy universal counit with the full, essentially
surjective cochain quotient and transport across its localization comparison. This
is the same cochain universal model, with exactly the recorded finite computation
map. The scalar tensor comparison from the ringed-site theorem agrees with the
prescribed comparison by their common local tensor-generator formula. The finite
normalization hypothesis is therefore precisely the scalar monoidality theorem's
counit square. Apply that theorem with the two supplied tensor coherence witnesses. -/
theorem coefficientFiniteTensorMonoidal
    (R : CoefficientDerivedSystemReduction l E W)
    (hT : CoefficientDerivedSystemTensorCoherence l E W R.toCoefficientDerivedSystemTensors)
    (hF : CoefficientFiniteTensorNormalization l E W R) (n : ℕ) :
    ∃ m : @Functor.CoreMonoidal _ _ R.integralClosed.monoidal
        _ _ (R.finiteClosed n).monoidal (coefficientFiniteDerivedExtension l E W n),
      ∀ P Q, (@Functor.CoreMonoidal.μIso _ _ R.integralClosed.monoidal
        _ _ (R.finiteClosed n).monoidal (coefficientFiniteDerivedExtension l E W n)
        m P Q).hom = (R.finiteTensor n).inv.app (P, Q) := by
  classical
  obtain ⟨⟨βI, ⟨cI⟩⟩, _, hN⟩ := hT
  obtain ⟨βN, ⟨cN⟩⟩ := hN n
  let J := Scheme.ProEt.topology W
  let φ := completedIntegralCommRingProjectionUnrestricted l E W n
  let D := finiteCochainModel l E W n
  -- Keep the counit formula in terms of D so simp can match it without expanding the model.
  have hε (P : CochainComplex (scalarReductionSource l E W) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := J) (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
      D.ε.app P = (coefficientFiniteReductionModel l E W P hP n).hom :=
    finiteCochainModel_counit l E W n P hP
  obtain ⟨κ, hκ, _⟩ := ringedFiniteFreeHomBaseChange_complex.{t+1, t, u,
    max (t+2) (u+1)} J φ D
  have hc (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
      κ.app (P, Q) = coefficientScalarTensorIso l E W n P Q := by
    apply (coefficientScalarTensorIso_exists l E W n P Q).unique
    · intro p q k hpq U x y
      subst k
      have h := hκ P Q p q U x y
      dsimp only [D, finiteCochainModel] at h
      dsimp only [J, φ] at h
      simp only [coefficientFiniteScalarSection] at h
      exact h
    · unfold coefficientScalarTensorIso coefficientUniqueComparisonChoice
      exact (coefficientScalarTensorIso_exists l E W n P Q).choose_spec.1
  obtain ⟨m, hm⟩ := ringedScalarTensorMonoidal.{t+1, t, u, max (t+2) (u+1)}
    J φ D R.integralClosed (R.finiteClosed n) R.integralTensorModel
    (R.finiteTensorModel n) βI βN cI cN κ (R.finiteTensor n) hκ (by
      intro P Q hP hQ
      refine ⟨(coefficientTensorModelPreservation l E W).1 P hP n,
        (coefficientTensorModelPreservation l E W).1 Q hQ n, ?_⟩
      have hh := hF n P Q hP hQ
      unfold CoefficientTensorComparisonSquare at hh
      simp only [show κ.hom.app (P, Q) = (coefficientScalarTensorIso l E W n P Q).hom from
        congrArg Iso.hom (hc P Q), hε P hP, hε Q hQ, hε _
          (coefficientTotalTensor_isKFlat.{u, t+1, t} J
            (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ)]
      dsimp only [coefficientIntegralTensorModelIso, coefficientFiniteTensorModelIso] at hh
      with_unfolding_all exact hh)
  exact ⟨m, hm⟩

end WeilConjectures
