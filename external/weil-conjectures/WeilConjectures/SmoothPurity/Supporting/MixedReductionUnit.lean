/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
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
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # Normalized mixed reduction unit

Source: proposition-six-operations-change-coefficients, tensor reassociation and completed
comparison (blueprint: def-weil-mixed-reduction-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct
open scoped ChangeOfRings

private theorem leftDerived_of_resolutions
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory B)
    [F.CommShift ℤ] [F.IsTriangulated]
    (G : DerivedCategory A ⥤ DerivedCategory B) (α : DerivedCategory.Qh ⋙ G ⟶ F)
    (P : Set (HomotopyCategory A (.up ℤ)))
    (hres : ∀ X, ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
      Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s)
    (hα : ∀ X, X ∈ P → IsIso (α.app X)) :
    G.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ)) := by
  have hinv (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y)
      (hX : X ∈ P) (hY : Y ∈ P) (hs : HomotopyCategory.quasiIso A (.up ℤ) s) :
      IsIso (F.map s) := by
    have := hα X hX
    have := hα Y hY
    have := Localization.inverts DerivedCategory.Qh _ _ hs
    have hn := α.naturality s
    rw [← isIso_comp_left_iff (α.app X), ← hn]
    change IsIso (G.map (DerivedCategory.Qh.map s) ≫ α.app Y)
    infer_instance
  obtain ⟨_, D, β, hD, _, hβ⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F P hres hinv
  have := hD
  let δ := D.leftDerivedLift β (HomotopyCategory.quasiIso A (.up ℤ)) G α
  have hd (X : HomotopyCategory A (.up ℤ)) (hX : X ∈ P) :
      IsIso (δ.app (DerivedCategory.Qh.obj X)) := by
    have := hβ X hX
    have := hα X hX
    have he : δ.app (DerivedCategory.Qh.obj X) ≫ β.app X = α.app X :=
      D.leftDerived_fac_app β _ G α X
    rw [← isIso_comp_right_iff _ (β.app X), he]
    infer_instance
  have hδapp (X : DerivedCategory A) : IsIso (δ.app X) := by
    obtain ⟨Y, ⟨e⟩⟩ := (inferInstance : DerivedCategory.Qh.EssSurj).mem_essImage X
    obtain ⟨Z, s, hZ, hs⟩ := hres Y
    have := Localization.inverts DerivedCategory.Qh _ _ hs
    have := hd Z hZ
    have hY : IsIso (δ.app (DerivedCategory.Qh.obj Y)) := by
      have hn := δ.naturality (DerivedCategory.Qh.map s)
      rw [← isIso_comp_left_iff (G.map (DerivedCategory.Qh.map s)), hn]
      infer_instance
    exact NatTrans.isIso_app_of_iso δ e.symm
  have hδ : IsIso δ := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ δ hδapp
  exact (D.isLeftDerivedFunctor_iff_isIso_leftDerivedLift β _ G α).mpr hδ

private def composeDerivedComparisons
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
    {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
    {F' : A' ⥤ B'} {G' : B' ⥤ C'} {H' : C' ⥤ D'}
    (α : QA ⋙ F' ⟶ F ⋙ QB) (β : QB ⋙ G' ⟶ G ⋙ QC)
    (γ : QC ⋙ H' ⟶ H ⋙ QD) :
    QA ⋙ F' ⋙ G' ⋙ H' ⟶ F ⋙ G ⋙ H ⋙ QD where
  app X := H'.map (G'.map (α.app X) ≫ β.app (F.obj X)) ≫ γ.app (G.obj (F.obj X))
  naturality X Y f := by
    let τ := Functor.whiskerRight α (G' ⋙ H') ≫
      Functor.whiskerLeft F (Functor.whiskerRight β H') ≫
      Functor.whiskerLeft (F ⋙ G) γ
    simpa only [τ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.comp_obj, Functor.comp_map,
      Functor.map_comp, Category.assoc] using τ.naturality f

namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  completedIntegralCoefficientSheafUnrestricted

section ScalarUnit
variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) (n : ℕ)

private theorem mixedReduction_projection :
    integralCompletedScalarMap l E L ι W ≫
        completedIntegralCommRingProjectionUnrestricted.{u, u} l L W n =
      completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n ≫
        integralScalarQuotientSheafMap l E L ι W n :=
  (integralCompletedScalarMap_existsUnique l E L ι W).exists.choose_spec n

private theorem mixedReduction_tensor_smul
    (M : scalarReductionSource.{u, u} l E W) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : M.val.obj U) :
    sfReductionTensor l E W n M U s x =
      s • sfReductionTensor l E W n M U 1 x := by
  let a := (eqToHom ((scalarReductionExistence.{u, u} l E W n).choose_spec.choose M).symm).val.app U
  let b := ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (integralCoefficientSheaf l E W n).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n) M)).app U
  change a (b (s ⊗ₜ[_,
    ((completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n).hom.app U).hom] x)) =
    s • a (b ((1 : (integralCoefficientCommRingSheaf l E W n).obj.obj U) ⊗ₜ[_,
      ((completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n).hom.app U).hom] x))
  let : Module ((completedIntegralCommRingSheafUnrestricted.{u, u} l E W).obj.obj U)
      ((integralCoefficientCommRingSheaf l E W n).obj.obj U) :=
    Module.compHom _
      ((completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n).hom.app U).hom
  have ht : s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted.{u, u} l E W).obj.obj U,
      ((completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n).hom.app U).hom] x =
      s • ((1 : (integralCoefficientCommRingSheaf l E W n).obj.obj U) ⊗ₜ[_,
        ((completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n).hom.app U).hom] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact (congrArg (fun z ↦ a (b z)) ht).trans
    ((congrArg a (b.hom.map_smul s _)).trans (a.hom.map_smul s _))

/-- The ordinary mixed-reduction unit, uniquely prescribed on sheafified tensors.
Source: proposition-six-operations-change-coefficients, tensor reassociation paragraph
(blueprint: def-weil-mixed-reduction-unit).
Proof: send s tensor x to ι_n(s) tensor (1 tensor x). The projection identity
for integralCompletedScalarMap makes this balanced. It commutes with restrictions;
sheafification gives the transformation. Pure tensors locally generate, giving uniqueness. -/
theorem sfMixedReductionUnit_existsUnique :
    ∃! η : scalarReductionExtension l E W n ⟶
      integralOrdinaryScalar l E L ι W ⋙ scalarReductionExtension l L W n ⋙
        proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n),
      ∀ (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : M.val.obj U),
        (η.app M).val.app U (sfReductionTensor l E W n M U s x) =
          sfReductionTensor l L W n ((integralOrdinaryScalar l E L ι W).obj M) U
            ((integralScalarQuotientSheafMap l E L ι W n).hom.app U s)
            (integralOrdinaryTensorSection l E L ι W M U 1 x) := by
  let F := integralOrdinaryScalar l E L ι W
  let T := scalarReductionExtension.{u, u} l L W n
  let V := proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)
  let H := F ⋙ T ⋙ V
  obtain ⟨aF, haF⟩ :=
    SheafOfModules.ScalarReductionProof.tensorAdjunction_of_identifications
      (K := AlgebraicGeometry.Scheme.ProEt.topology W)
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
      (S := completedIntegralCommRingSheafUnrestricted.{u, u} l L W)
      (integralCompletedScalarMap l E L ι W) F
      (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
      (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose
  obtain ⟨aE, haE⟩ := scalarReductionExtension_adjunction.{u, u} l E W n
  obtain ⟨aL, haL⟩ := scalarReductionExtension_adjunction.{u, u} l L W n
  have hc (U : W.ProEtᵒᵖ)
      (r : (completedIntegralCommRingSheafUnrestricted.{u, u} l E W).obj.obj U) :
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l L W n).hom.app U
          ((integralCompletedScalarMap l E L ι W).hom.app U r) =
        (integralScalarQuotientSheafMap l E L ι W n).hom.app U
          ((completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n).hom.app U r) :=
    ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app U)
      (mixedReduction_projection l E L ι W n)) r
  let j (M : scalarReductionSource.{u, u} l E W) :
      M ⟶ (scalarReductionRestriction.{u, u} l E W n).obj (H.obj M) :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          (X := M.val.obj U)
          (Y := ((scalarReductionRestriction.{u, u} l E W n).obj (H.obj M)).val.obj U)
          { toFun := fun x ↦ (aL.unit.app (F.obj M)).val.app U
              ((aF.unit.app M).val.app U x)
            map_add' := by intros; simp only [map_add]
            map_smul' := by
              intro r x
              change (aL.unit.app (F.obj M)).val.app U
                ((aF.unit.app M).val.app U (r • x)) = _
              rw [map_smul]
              change (aL.unit.app (F.obj M)).val.app U
                  ((integralCompletedScalarMap l E L ι W).hom.app U r •
                    (show (F.obj M).val.obj U from (aF.unit.app M).val.app U x)) = _
              rw [map_smul]
              change (completedIntegralCommRingProjectionUnrestricted.{u, u} l L W n).hom.app U
                  ((integralCompletedScalarMap l E L ι W).hom.app U r) •
                  (show ((T.obj (F.obj M)).val.obj U) from
                    (aL.unit.app (F.obj M)).val.app U ((aF.unit.app M).val.app U x)) = _
              rw [hc]
              rfl }
        naturality := by
          intro U U' f
          ext x
          exact (congrArg ((aL.unit.app (F.obj M)).val.app U')
            (PresheafOfModules.naturality_apply (aF.unit.app M).val f x)).trans
              (PresheafOfModules.naturality_apply (aL.unit.app (F.obj M)).val f
                ((aF.unit.app M).val.app U x)) } }
  let η : scalarReductionExtension.{u, u} l E W n ⟶ H :=
    { app := fun M ↦ (aE.homEquiv M (H.obj M)).symm (j M)
      naturality := by
        intro M N f
        apply (aE.homEquiv M (H.obj N)).injective
        rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
          Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
        ext U x
        change (aL.unit.app (F.obj N)).val.app U
            ((aF.unit.app N).val.app U (f.val.app U x)) =
          (T.map (F.map f)).val.app U
            ((aL.unit.app (F.obj M)).val.app U ((aF.unit.app M).val.app U x))
        have hF := congrArg (fun k ↦ k.val.app U x) (aF.unit.naturality f)
        have hL := congrArg (fun k ↦ k.val.app U ((aF.unit.app M).val.app U x))
          (aL.unit.naturality (F.map f))
        exact (congrArg ((aL.unit.app (F.obj N)).val.app U) hF).trans hL }
  have hη (M : scalarReductionSource.{u, u} l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      (η.app M).val.app U (sfReductionTensor l E W n M U 1 x) =
        sfReductionTensor l L W n (F.obj M) U 1
          (integralOrdinaryTensorSection l E L ι W M U 1 x) := by
    have h := (aE.homEquiv M (H.obj M)).apply_symm_apply (j M)
    rw [Adjunction.homEquiv_unit] at h
    have hx := congrArg (fun k ↦ k.val.app U x) h
    change (η.app M).val.app U ((aE.unit.app M).val.app U x) = _ at hx
    rw [haE] at hx
    change (η.app M).val.app U (sfReductionTensor l E W n M U 1 x) = _ at hx
    rw [hx]
    change (aL.unit.app (F.obj M)).val.app U ((aF.unit.app M).val.app U x) = _
    rw [haF, haL]
    rfl
  refine ⟨η, ?_, ?_⟩
  · intro M U s x
    rw [mixedReduction_tensor_smul, map_smul, hη]
    change (integralScalarQuotientSheafMap l E L ι W n).hom.app U s •
      sfReductionTensor l L W n (F.obj M) U 1 _ = _
    exact (mixedReduction_tensor_smul l L W n _ U _ _).symm
  · intro τ hτ
    apply NatTrans.ext
    funext M
    apply (aE.homEquiv M (H.obj M)).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext U x
    change (τ.app M).val.app U ((aE.unit.app M).val.app U x) =
      (η.app M).val.app U ((aE.unit.app M).val.app U x)
    rw [haE]
    change (τ.app M).val.app U (sfReductionTensor l E W n M U 1 x) =
      (η.app M).val.app U (sfReductionTensor l E W n M U 1 x)
    rw [hτ, map_one, hη]

/-- The actual mixed tensor unit, with no choice of a comparison isomorphism.
Source: proposition-six-operations-change-coefficients, tensor reassociation paragraph
(blueprint: def-weil-mixed-reduction-unit). -/
def sfMixedReductionUnit := (sfMixedReductionUnit_existsUnique l E L ι W n).exists.choose

/-- The homotopy-level mixed unit, with the tensor composites explicitly associated.
Source: proposition-six-operations-change-coefficients, tensor reassociation paragraph
(blueprint: def-weil-mixed-reduction-unit). -/
def sfMixedReductionUnitHomotopy :
    (scalarReductionExtension l E W n).mapHomotopyCategory (.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι W).mapHomotopyCategory (.up ℤ) ⋙
        (scalarReductionExtension l L W n).mapHomotopyCategory (.up ℤ) ⋙
          (proEtaleCoefficientRestrictScalars W
            (integralScalarQuotientMap l E L ι n)).mapHomotopyCategory (.up ℤ) :=
  letI : (scalarReductionExtension l L W n ⋙
      proEtaleCoefficientRestrictScalars W
        (integralScalarQuotientMap l E L ι n)).Additive := inferInstance
  letI : (integralOrdinaryScalar l E L ι W ⋙ scalarReductionExtension l L W n ⋙
      proEtaleCoefficientRestrictScalars W
        (integralScalarQuotientMap l E L ι n)).Additive := inferInstance
  NatTrans.mapHomotopyCategory (sfMixedReductionUnit l E L ι W n) (.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (F := integralOrdinaryScalar l E L ι W)
      (G := scalarReductionExtension l L W n ⋙
        proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n))
      (Iso.refl _) (.up ℤ)).inv ≫
      Functor.whiskerLeft _ (Functor.mapHomotopyCategoryCompIso
        (F := scalarReductionExtension l L W n)
        (G := proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n))
        (Iso.refl _) (.up ℤ)).inv

private abbrev mixedReductionDerivedTarget :=
  integralOrdinaryDerivedScalar l E L ι W ⋙ scalarReductionDerivedExtension.{u, u} l L W n ⋙
    (proEtaleCoefficientRestrictScalars W
      (integralScalarQuotientMap l E L ι n)).mapDerivedCategory

private def mixedReductionDerivedComparison :
    DerivedCategory.Qh ⋙ mixedReductionDerivedTarget l E L ι W n ⟶
      (integralOrdinaryScalar l E L ι W).mapHomotopyCategory (.up ℤ) ⋙
        (scalarReductionExtension.{u, u} l L W n).mapHomotopyCategory (.up ℤ) ⋙
          (proEtaleCoefficientRestrictScalars W
            (integralScalarQuotientMap l E L ι n)).mapHomotopyCategory (.up ℤ) ⋙
              DerivedCategory.Qh :=
  composeDerivedComparisons
    (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactorsh.hom
    (scalarReductionCounit.{u, u} l L W n)
    (proEtaleCoefficientRestrictScalars W
      (integralScalarQuotientMap l E L ι n)).mapDerivedCategoryFactorsh.hom

private theorem mixedReductionDerivedComparison_isLeftDerived :
    (mixedReductionDerivedTarget l E L ι W n).IsLeftDerivedFunctor
      (mixedReductionDerivedComparison l E L ι W n)
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E W) (.up ℤ)) := by
  let : HasDerivedCategory (scalarReductionSource.{u, u} l E W) :=
    scalarReductionSourceDerived.{u, u} l E W
  let : HasDerivedCategory (scalarReductionTarget.{u, u} l E W n) :=
    scalarReductionTargetDerived.{u, u} l E W n
  have : EssentiallySmall.{u + 1} W.ProEt := scalarReductionSiteSmall.{u, u} W
  let F := integralOrdinaryScalar l E L ι W
  let T := scalarReductionExtension.{u, u} l L W n
  let V := proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)
  let P : Set (HomotopyCategory (scalarReductionSource.{u, u} l E W) (.up ℤ)) :=
    {X | ∃ C : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ,
      X = (HomotopyCategory.quotient _ (.up ℤ)).obj C ∧
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) C}
  apply leftDerived_of_resolutions _ _ _ P
  · intro X
    obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, s, hK, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) C
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, ⟨K, rfl, hK⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).mpr hs⟩
  · rintro X ⟨C, rfl, hC⟩
    have hFC := SheafOfModules.changeOfRings_isKFlat_independentCoefficients.{u + 1, u, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
      (S := completedIntegralCommRingSheafUnrestricted.{u, u} l L W)
      (integralCompletedScalarMap l E L ι W) C F
      (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
      (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose hC
    have hε : IsIso ((scalarReductionCounit.{u, u} l L W n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj C))) :=
      (scalarReductionDerivedExistence.{u, u} l L W n).choose_spec.choose_spec.2.2
        ((F.mapHomologicalComplex (.up ℤ)).obj C) hFC
    have hε' : IsIso ((scalarReductionCounit.{u, u} l L W n).app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj C))) := by
      let e : (F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj C) ≅
          (HomotopyCategory.quotient _ (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj C) :=
        (F.mapHomotopyCategoryFactors (.up ℤ)).app C
      exact NatTrans.isIso_app_of_iso (scalarReductionCounit.{u, u} l L W n) e
    dsimp only [mixedReductionDerivedComparison, composeDerivedComparisons,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance

/-- Localization of the tensor-unit map. The equation is on the whole homotopy
category, including both coordinates of every Roos complex; it is not a choice of
maps after evaluation of a derived inverse limit.
Source: proposition-six-operations-change-coefficients, tensor reassociation paragraph
(blueprint: def-weil-mixed-reduction-unit).
Proof: ordinary finite free extension is exact, and restriction is exact. Derive
the ordinary mixed unit using the two universal left-derived tensor counits.
On K-flat complexes those counits are invertible, so the equation determines the
map there. K-flat resolutions and the localization universal property give existence,
naturality and uniqueness on all complexes. -/
theorem sfMixedReductionDerivedUnit_existsUnique :
    ∃! η : scalarReductionDerivedExtension l E W n ⟶
      integralOrdinaryDerivedScalar l E L ι W ⋙ scalarReductionDerivedExtension l L W n ⋙
        (proEtaleCoefficientRestrictScalars W
          (integralScalarQuotientMap l E L ι n)).mapDerivedCategory,
      ∀ P : HomotopyCategory (scalarReductionSource l E W) (.up ℤ),
        η.app (DerivedCategory.Qh.obj P) ≫
          (proEtaleCoefficientRestrictScalars W
            (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map
            ((scalarReductionDerivedExtension l L W n).map
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactorsh.hom.app P) ≫
              (scalarReductionCounit l L W n).app
                (((integralOrdinaryScalar l E L ι W).mapHomotopyCategory (.up ℤ)).obj P)) ≫
          (proEtaleCoefficientRestrictScalars W
            (integralScalarQuotientMap l E L ι n)).mapDerivedCategoryFactorsh.hom.app
            (((scalarReductionExtension l L W n).mapHomotopyCategory (.up ℤ)).obj
              (((integralOrdinaryScalar l E L ι W).mapHomotopyCategory (.up ℤ)).obj P)) =
        (scalarReductionCounit l E W n).app P ≫
          DerivedCategory.Qh.map ((sfMixedReductionUnitHomotopy l E L ι W n).app P) := by
  let G := mixedReductionDerivedTarget l E L ι W n
  let α := mixedReductionDerivedComparison l E L ι W n
  have : G.IsLeftDerivedFunctor α
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E W) (.up ℤ)) :=
    mixedReductionDerivedComparison_isLeftDerived l E L ι W n
  let β : DerivedCategory.Qh ⋙ scalarReductionDerivedExtension.{u, u} l E W n ⟶ _ :=
    scalarReductionCounit.{u, u} l E W n ≫
      Functor.whiskerRight (sfMixedReductionUnitHomotopy l E L ι W n) DerivedCategory.Qh
  let η := G.leftDerivedLift α
    (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E W) (.up ℤ)) _ β
  have hη (P : HomotopyCategory (scalarReductionSource.{u, u} l E W) (.up ℤ)) :
      η.app (DerivedCategory.Qh.obj P) ≫ α.app P = β.app P :=
    G.leftDerived_fac_app α
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E W) (.up ℤ)) _ β P
  refine ⟨η, ?_, ?_⟩
  · intro P
    exact hη P
  · intro τ hτ
    apply G.leftDerived_ext α
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E W) (.up ℤ))
    apply NatTrans.ext
    funext P
    change τ.app (DerivedCategory.Qh.obj P) ≫ α.app P =
      η.app (DerivedCategory.Qh.obj P) ≫ α.app P
    exact (hτ P).trans (hη P).symm

/-- The derived unit is selected from a unique universally normalized transformation.
Source: proposition-six-operations-change-coefficients, tensor reassociation paragraph
(blueprint: def-weil-mixed-reduction-unit). -/
def sfMixedReductionDerivedUnit :=
  (sfMixedReductionDerivedUnit_existsUnique l E L ι W n).exists.choose

/-- Complete the target of the ordinary tensor-unit map using the prescribed diagonal
Roos completion map. This retains its quotient augmentation and shifted cone coordinate.
Source: proposition-six-operations-change-coefficients, completed comparison paragraph
(blueprint: def-weil-mixed-reduction-unit). -/
def sfMixedCompletedReductionUnit
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (scalarReductionDerivedExtension l E W n).obj K ⟶
      (proEtaleCoefficientRestrictScalars W
        (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.obj
          ((scalarReductionDerivedExtension l L W n).obj
            ((integralScalarExtension l E L ι W).obj K)) :=
  (sfMixedReductionDerivedUnit l E L ι W n).app K ≫
    (proEtaleCoefficientRestrictScalars W
      (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map
        ((scalarReductionDerivedExtension l L W n).map
          ((scalarCompletion l E L ι W).app K))
end ScalarUnit

end WeilConjectures
