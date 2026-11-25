/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
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

/-! # Data of the normalized scalar Roos lift -/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ChangeOfRings
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension
  completedScalarCounit
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap

attribute [local irreducible] completedScalarChangeData

namespace ScalarRoosLiftProof

variable (l : ℕ) [Fact l.Prime]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

private abbrev R := integralComparisonRestrictionCurried.{u, u} l L X

private abbrev V := SheafOfModules.restrictScalars.{u + 1, u, u + 1, u + 1}
  ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (completedCoefficientMap.{u, u} l L F j X))

private theorem adjData :
    ∃ a : completedOrdinaryScalarExtension.{u, u} l L F j X ⊣ V l L F j X,
      ∀ (M : integralTowerModules.{u, u} l L X) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x =
          completedScalarTensorSection.{u, u} l L F j X M U 1 x := by
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} X
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} X
  have hobj (M : integralTowerModules.{u, u} l L X) :
      (completedOrdinaryScalarExtension.{u, u} l L F j X).obj M =
        SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (completedCoefficientMap.{u, u} l L F j X) M :=
    completedOrdinaryScalarExtension_obj.{u, u} l L F j X M
  have hmap {M N : integralTowerModules.{u, u} l L X} (f : M ⟶ N) :
      (completedOrdinaryScalarExtension.{u, u} l L F j X).map f =
        eqToHom (hobj M) ≫
          SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
            (completedCoefficientMap.{u, u} l L F j X) M f ≫
          eqToHom (hobj N).symm :=
    completedOrdinaryScalarExtension_map.{u, u} l L F j X f
  obtain ⟨a, ha⟩ :=
    (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction.{u + 1, u + 1, u}
      (C := X.ProEt) (J := Scheme.ProEt.topology X)
      (O := completedIntegralCommRingSheafUnrestricted.{u, u} l L X)
      (O' := completedIntegralCommRingSheafUnrestricted.{u, u} l F X)
      (completedCoefficientMap.{u, u} l L F j X)).choose_spec.choose_spec
        (completedOrdinaryScalarExtension.{u, u} l L F j X)
        hobj hmap
  refine ⟨a, ?_⟩
  intro M U x
  change (show ((completedOrdinaryScalarExtension.{u, u} l L F j X).obj M).val.obj U from
    (a.unit.app M).val.app U x) = _
  let e := eqToIso (completedOrdinaryScalarExtension_obj.{u, u} l L F j X M)
  have h := ha M ((completedOrdinaryScalarExtension.{u, u} l L F j X).obj M) e.inv U x
  have he : eqToHom (completedOrdinaryScalarExtension_obj.{u, u} l L F j X M) ≫ e.inv =
      𝟙 _ := e.hom_inv_id
  rw [he] at h
  rw [Adjunction.homEquiv_id] at h
  dsimp only [completedScalarTensorSection, e, eqToIso.inv,
    completedOrdinaryScalarExtension] at h ⊢
  with_unfolding_all exact h

private def adj : completedOrdinaryScalarExtension.{u, u} l L F j X ⊣ V l L F j X :=
  (adjData l L F j X).choose

private theorem adj_unit (M : integralTowerModules.{u, u} l L X) (U : X.ProEtᵒᵖ)
    (x : M.val.obj U) :
    ((adj l L F j X).unit.app M).val.app U x =
      completedScalarTensorSection.{u, u} l L F j X M U 1 x :=
  (adjData l L F j X).choose_spec M U x

private def unitComponent (M : coefficientSequenceModules l L X) (n : ℕ) :
    ((R l L X).obj M).obj (op n) ⟶
      (V l L F j X).obj (((R l F X).obj
        ((integralComparisonSequenceScalarModel.{u, u} l L F j X).E.obj M)).obj (op n)) where
  val :=
    { app U := ModuleCat.ofHom
        (X := (((R l L X).obj M).obj (op n)).val.obj U)
        (Y := ((V l L F j X).obj (((R l F X).obj
          ((integralComparisonSequenceScalarModel.{u, u} l L F j X).E.obj M)).obj
            (op n))).val.obj U)
        { toFun := fun (x : (((R l L X).obj M).obj (op n)).val.obj U) ↦
            show ((V l L F j X).obj (((R l F X).obj
              ((integralComparisonSequenceScalarModel.{u, u} l L F j X).E.obj M)).obj
                (op n))).val.obj U from
              ((sequenceScalarAdjunction.{u, u} l L F j X).choose.unit.app M).val.app
                (op (n, U.unop)) x
          map_add' := map_add _
          map_smul' := by
            intro s x
            have hs := congrArg (fun f ↦ (f.hom.app U).hom s)
              (completedScalarResidue.{u, u} l L F j X n)
            have h := (((sequenceScalarAdjunction.{u, u} l L F j X).choose.unit.app M).val.app
              (op (n, U.unop))).hom.map_smul
                (((completedIntegralCommRingProjectionUnrestricted.{u, u} l L X n).hom.app U) s) x
            change
              (((sequenceScalarAdjunction.{u, u} l L F j X).choose.unit.app M).val.app
                (op (n, U.unop)))
                (((completedIntegralCommRingProjectionUnrestricted.{u, u} l L X n).hom.app U s)
                  • (show M.val.obj (op (n, U.unop)) from x)) =
              ((completedIntegralCommRingProjectionUnrestricted.{u, u} l F X n).hom.app U
                ((completedCoefficientMap.{u, u} l L F j X).hom.app U s)) •
                (show (((integralComparisonSequenceScalarModel l L F j X).E.obj M).val.obj
                  (op (n, U.unop))) from
                  (((sequenceScalarAdjunction.{u, u} l L F j X).choose.unit.app M).val.app
                    (op (n, U.unop))) x)
            change
              (completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U
                ((completedCoefficientMap.{u, u} l L F j X).hom.app U s) =
                  (integralScalarRho l L F j X n).hom.app U s at hs
            rw [hs]
            exact h }
      naturality := by
        intro U W a
        ext x
        exact PresheafOfModules.naturality_apply
          ((sequenceScalarAdjunction.{u, u} l L F j X).choose.unit.app M).val
          ((Prod.sectR n X.ProEt).op.map a) x }

private theorem unitComponent_horizontal (M : coefficientSequenceModules l L X)
    {n m : ℕᵒᵖ} (a : n ⟶ m) :
    ((R l L X).obj M).map a ≫ unitComponent l L F j X M m.unop =
      unitComponent l L F j X M n.unop ≫
        (V l L F j X).map (((R l F X).obj
          ((integralComparisonSequenceScalarModel.{u, u} l L F j X).E.obj M)).map a) := by
  ext U x
  exact PresheafOfModules.naturality_apply
    ((sequenceScalarAdjunction.{u, u} l L F j X).choose.unit.app M).val
    (Prod.mkHom a.unop (𝟙 U.unop)).op x

private theorem unitComponent_naturality {M N : coefficientSequenceModules l L X}
    (f : M ⟶ N) (n : ℕ) :
    (((R l L X).map f).app (op n)) ≫ unitComponent l L F j X N n =
      unitComponent l L F j X M n ≫
        (V l L F j X).map (((R l F X).map
          ((integralComparisonSequenceScalarModel.{u, u} l L F j X).E.map f)).app (op n)) := by
  ext U x
  exact congrArg (fun f ↦ f.val.app (op (n, U.unop)) x)
    ((sequenceScalarAdjunction.{u, u} l L F j X).choose.unit.naturality f)

private def component (M : coefficientSequenceModules l L X) (n : ℕ) :
    (completedOrdinaryScalarExtension.{u, u} l L F j X).obj (((R l L X).obj M).obj (op n)) ⟶
      ((R l F X).obj ((integralComparisonSequenceScalarModel.{u, u} l L F j X).E.obj M)).obj
        (op n) :=
  ((adj l L F j X).homEquiv _ _).symm (unitComponent l L F j X M n)

private theorem component_horizontal (M : coefficientSequenceModules l L X)
    {n m : ℕᵒᵖ} (a : n ⟶ m) :
    (completedOrdinaryScalarExtension.{u, u} l L F j X).map (((R l L X).obj M).map a) ≫
        component l L F j X M m.unop =
      component l L F j X M n.unop ≫
        ((R l F X).obj ((integralComparisonSequenceScalarModel.{u, u} l L F j X).E.obj M)).map
          a := by
  apply ((adj l L F j X).homEquiv _ _).injective
  unfold component
  rw [(adj l L F j X).homEquiv_naturality_left, Equiv.apply_symm_apply,
    (adj l L F j X).homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact unitComponent_horizontal l L F j X M a

private def componentNat (n : ℕ) :
    R l L X ⋙ (evaluation ℕᵒᵖ _).obj (op n) ⋙
        completedOrdinaryScalarExtension.{u, u} l L F j X ⟶
      (integralComparisonSequenceScalarModel.{u, u} l L F j X).E ⋙ R l F X ⋙
        (evaluation ℕᵒᵖ _).obj (op n) where
  app M := component l L F j X M n
  naturality {M N} f := by
    apply ((adj l L F j X).homEquiv _ _).injective
    change (adj l L F j X).homEquiv _ _
      ((completedOrdinaryScalarExtension.{u, u} l L F j X).map
        (((R l L X).map f).app (op n)) ≫ component l L F j X N n) =
      (adj l L F j X).homEquiv _ _
        (component l L F j X M n ≫
          (((R l F X).map
            ((integralComparisonSequenceScalarModel l L F j X).E.map f)).app (op n)))
    rw [(adj l L F j X).homEquiv_naturality_left,
      (adj l L F j X).homEquiv_naturality_right]
    simp only [component, Equiv.apply_symm_apply]
    exact unitComponent_naturality l L F j X f n

private theorem component_one (M : coefficientSequenceModules l L X) (n : ℕ)
    (U : X.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    (component l L F j X M n).val.app U
        (completedScalarTensorSection.{u, u} l L F j X (((R l L X).obj M).obj (op n)) U 1 x) =
      integralComparisonSequenceTensorSection l L F j X M (op (n, U.unop)) 1 x := by
  have h := congrArg (fun f ↦ f.val.app U x)
    (((adj l L F j X).homEquiv _ _).apply_symm_apply
      (unitComponent l L F j X M n))
  change (component l L F j X M n).val.app U
    (((adj l L F j X).unit.app _).val.app U x) = _ at h
  rw [adj_unit] at h
  exact h.trans ((sequenceScalarAdjunction.{u, u} l L F j X).choose_spec M
    (op (n, U.unop)) x)

private theorem tensor_smul (M : integralTowerModules.{u, u} l L X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted.{u, u} l F X).obj.obj U)
    (x : M.val.obj U) :
    completedScalarTensorSection.{u, u} l L F j X M U s x =
      s • completedScalarTensorSection.{u, u} l L F j X M U 1 x := by
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} X
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} X
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l F X)).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (completedCoefficientMap.{u, u} l L F j X) M)
  have hη := PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l F X)).obj)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (completedCoefficientMap.{u, u} l L F j X) M)
  unfold completedScalarTensorSection
  rw [← hη]
  dsimp only [completedOrdinaryScalarExtension] at η ⊢
  change (eqToHom (completedOrdinaryScalarExtension_obj.{u, u} l L F j X M).symm).val.app U
    (η.app U (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted.{u, u} l L X).obj.obj U,
      ((completedCoefficientMap.{u, u} l L F j X).hom.app U).hom] x)) =
      s • (eqToHom (completedOrdinaryScalarExtension_obj.{u, u} l L F j X M).symm).val.app U
        (η.app U ((1 : (completedIntegralCommRingSheafUnrestricted.{u, u} l F X).obj.obj U)
          ⊗ₜ[(completedIntegralCommRingSheafUnrestricted.{u, u} l L X).obj.obj U,
          ((completedCoefficientMap.{u, u} l L F j X).hom.app U).hom] x))
  rw [← ((eqToHom (completedOrdinaryScalarExtension_obj.{u, u} l L F j X M).symm).val.app
    U).hom.map_smul, ← (η.app U).hom.map_smul]
  congr 2
  congr 1
  change s = s * 1
  exact (mul_one s).symm

private theorem component_tensor (M : coefficientSequenceModules l L X) (n : ℕ)
    (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted.{u, u} l F X).obj.obj U)
    (x : M.val.obj (op (n, U.unop))) :
    (component l L F j X M n).val.app U
        (completedScalarTensorSection.{u, u} l L F j X (((R l L X).obj M).obj (op n)) U s x) =
      integralComparisonSequenceTensorSection l L F j X M (op (n, U.unop))
        ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s) x := by
  rw [tensor_smul, (component l L F j X M n).val.app U |>.hom.map_smul,
    component_one]
  change ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s) •
    integralComparisonSequenceTensorSection l L F j X M (op (n, U.unop)) 1 x = _
  rw [sequenceTensorSection_eq, sequenceTensorSection_eq]
  simp only [SheafOfModules.systemModelTmul, one_smul]

private def restrictionIso : R l L X ≅ coefficientSequenceRestriction l L X :=
  eqToIso (integralComparisonRestrictionCurried_eq l L X)

private theorem eqToHom_section {M N : scalarReductionSource l L X} (e : M = N)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    HEq ((eqToHom e).val.app U x) x := by
  subst e
  rfl

private theorem restrictionIso_section (M : coefficientSequenceModules l L X)
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    (((restrictionIso l L X).hom.app M).app (op n)).val.app U x =
      integralComparisonRestrictedSection l L X M n U x := by
  have he : HEq ((((restrictionIso l L X).hom.app M).app (op n)).val.app U x) x := by
    simp only [restrictionIso, eqToIso.hom, eqToHom_app]
    exact eqToHom_section l L X
      (M := ((R l L X).obj M).obj (op n))
      (N := ((coefficientSequenceRestriction l L X).obj M).obj (op n)) _ U x
  exact eq_of_heq (he.trans (cast_heq _ x).symm)

private theorem restrictionIso_inv_section (M : coefficientSequenceModules l L X)
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    (((restrictionIso l L X).inv.app M).app (op n)).val.app U
      (integralComparisonRestrictedSection l L X M n U x) = x := by
  rw [← restrictionIso_section l L X M n U x]
  exact congrArg (fun f ↦ (f.app (op n)).val.app U x)
    ((restrictionIso l L X).hom_inv_id_app M)

private def componentTower (M : coefficientSequenceModules l L X) :
    ((R l L X).obj M) ⋙ completedOrdinaryScalarExtension.{u, u} l L F j X ⟶
      (R l F X).obj ((integralComparisonSequenceScalarModel l L F j X).E.obj M) where
  app n := component l L F j X M n.unop
  naturality _ _ a := component_horizontal l L F j X M a

private def scalarComponentTower (M : coefficientSequenceModules l L X) :
    ((coefficientSequenceRestriction l L X).obj M) ⋙
        completedOrdinaryScalarExtension.{u, u} l L F j X ⟶
      (coefficientSequenceRestriction l F X).obj
        ((integralComparisonSequenceScalarModel l L F j X).E.obj M) :=
  Functor.whiskerRight ((restrictionIso l L X).inv.app M)
      (completedOrdinaryScalarExtension.{u, u} l L F j X) ≫
    componentTower l L F j X M ≫
    (restrictionIso l F X).hom.app
      ((integralComparisonSequenceScalarModel l L F j X).E.obj M)

private def scalarComponentNat (n : ℕ) :
    coefficientSequenceRestriction l L X ⋙ (evaluation ℕᵒᵖ _).obj (op n) ⋙
        completedOrdinaryScalarExtension.{u, u} l L F j X ⟶
      (integralComparisonSequenceScalarModel l L F j X).E ⋙
        coefficientSequenceRestriction l F X ⋙ (evaluation ℕᵒᵖ _).obj (op n) :=
  Functor.whiskerRight (restrictionIso l L X).inv
      ((evaluation ℕᵒᵖ _).obj (op n) ⋙ completedOrdinaryScalarExtension.{u, u} l L F j X) ≫
    componentNat l L F j X n ≫
    Functor.whiskerLeft (integralComparisonSequenceScalarModel l L F j X).E
      (Functor.whiskerRight (restrictionIso l F X).hom
        ((evaluation ℕᵒᵖ _).obj (op n)))

private theorem scalarComponent_horizontal (M : coefficientSequenceModules l L X)
    {n m : ℕᵒᵖ} (a : n ⟶ m) :
    (completedOrdinaryScalarExtension.{u, u} l L F j X).map
        (((coefficientSequenceRestriction l L X).obj M).map a) ≫
          (scalarComponentNat l L F j X m.unop).app M =
      (scalarComponentNat l L F j X n.unop).app M ≫
        (((coefficientSequenceRestriction l F X).obj
          ((integralComparisonSequenceScalarModel l L F j X).E.obj M)).map a) :=
  (scalarComponentTower l L F j X M).naturality a

private theorem scalarComponent_tensor (M : coefficientSequenceModules l L X) (n : ℕ)
    (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted.{u, u} l F X).obj.obj U)
    (x : M.val.obj (op (n, U.unop))) :
    ((scalarComponentNat l L F j X n).app M).val.app U
        (completedScalarTensorSection.{u, u} l L F j X
          (((coefficientSequenceRestriction l L X).obj M).obj (op n)) U s
            (integralComparisonRestrictedSection l L X M n U x)) =
      integralComparisonRestrictedSection l F X
        ((integralComparisonSequenceScalarModel l L F j X).E.obj M) n U
        (integralComparisonSequenceTensorSection l L F j X M (op (n, U.unop))
          ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s) x) := by
  change (((restrictionIso l F X).hom.app _).app (op n)).val.app U
    ((component l L F j X M n).val.app U
      (((completedOrdinaryScalarExtension.{u, u} l L F j X).map
        (((restrictionIso l L X).inv.app M).app (op n))).val.app U _)) = _
  rw [completedScalarTensorSection_naturality, restrictionIso_inv_section,
    component_tensor, restrictionIso_section]

private def levelChange (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (n : ℕ) :
    (completedOrdinaryScalarComplex l L F j X).obj
        ((((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
          D).asFunctor.obj (op n)) ⟶
      ((((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor.obj (op n)) :=
  (NatTrans.mapHomologicalComplex (scalarComponentNat l L F j X n) (.up ℤ)).app D

private theorem levelChange_horizontal
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    {n m : ℕᵒᵖ} (a : n ⟶ m) :
    (completedOrdinaryScalarComplex l L F j X).map
        ((((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
          D).asFunctor.map a) ≫ levelChange l L F j X D m.unop =
      levelChange l L F j X D n.unop ≫
        ((((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor.map a) := by
  ext i : 1
  exact scalarComponent_horizontal l L F j X (D.X i) a

private theorem cocone_d_snd
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {K T : CochainComplex A ℤ} (δ : K ⟶ T) (i : ℤ) :
    (CochainComplex.mappingCocone δ).d i (i + 1) ≫
        (CochainComplex.mappingCocone.snd δ).v (i + 1) i (by omega) =
      -((CochainComplex.mappingCocone.fst δ).f i ≫ δ.f i) -
        (CochainComplex.mappingCocone.snd δ).v i (i - 1) (by omega) ≫
          T.d (i - 1) i := by
  simp only [CochainComplex.mappingCocone, Int.reduceNeg, Int.reduceSub,
    CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctor_obj_d',
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    CochainComplex.mappingCocone.snd,
    CochainComplex.HomComplex.Cochain.leftShift_v
      (CochainComplex.mappingCone.snd δ) (-1) (-1) (zero_add _) (i + 1) i
      (by omega) i (add_zero i),
    mul_neg, mul_one, neg_neg, Int.reduceAdd, neg_mul, one_mul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
    Int.negOnePow_even 2 ⟨1, rfl⟩, CochainComplex.shiftFunctorObjXIso,
    Preadditive.neg_comp, HomologicalComplex.d_comp_XIsoOfEq_hom_assoc,
    CochainComplex.mappingCocone.fst, HomologicalComplex.neg_f_apply,
    CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cocycle.leftShift_coe,
    CochainComplex.HomComplex.Cochain.leftShift_v
      (CochainComplex.mappingCone.fst δ).1 (-1) 0 (add_neg_cancel 1) i i
      (add_zero i) (i - 1) (by omega),
    mul_zero, zero_add, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.assoc, Category.id_comp,
    CochainComplex.HomComplex.Cochain.leftShift_v
      (CochainComplex.mappingCone.snd δ) (-1) (-1) (zero_add _) i (i - 1)
      (by omega) (i - 1) (add_zero _)]
  change -((CochainComplex.mappingCone δ).d (i - 1) i ≫
      (CochainComplex.mappingCone.snd δ).v i i (add_zero i)) =
    -((CochainComplex.mappingCone.fst δ).1.v (i - 1) i (by omega) ≫ δ.f i) -
      (CochainComplex.mappingCone.snd δ).v (i - 1) (i - 1) (add_zero _) ≫
        T.d (i - 1) i
  rw [CochainComplex.mappingCone.d_snd_v δ (i - 1) i (by omega)]
  simp only [neg_add, sub_eq_add_neg]

private theorem cocone_fst_zero
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {K T P : CochainComplex A ℤ} (δ : K ⟶ T)
    (f : P ⟶ CochainComplex.mappingCocone δ)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd δ).v i (i - 1) (by omega) = 0) :
    f ≫ CochainComplex.mappingCocone.fst δ ≫ δ = 0 := by
  ext i : 1
  have hc := congrArg
    (fun k ↦ k ≫ (CochainComplex.mappingCocone.snd δ).v (i + 1) i (by omega))
    (f.comm i (i + 1))
  have hzero (p q : ℤ) (e : p - 1 = q) :
      f.f p ≫ (CochainComplex.mappingCocone.snd δ).v p q (by omega) = 0 := by
    subst q
    exact hf p
  have hf' : f.f (i + 1) ≫
      (CochainComplex.mappingCocone.snd δ).v (i + 1) i (by omega) = 0 :=
    hzero (i + 1) i (by omega)
  rw [Category.assoc, cocone_d_snd, Preadditive.comp_sub, Preadditive.comp_neg,
    ← Category.assoc, ← Category.assoc, hf i, zero_comp, sub_zero,
    Category.assoc (P.d i (i + 1)), hf', comp_zero] at hc
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, neg_eq_zero,
    Category.assoc] using hc

private theorem roos_compatible
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) {P : CochainComplex A ℤ}
    (f : P ⟶ integralOperationsRoos C)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v
        i (i - 1) (by omega) = 0) (n : ℕ) :
    (f ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
        Pi.π (fun m : ℕ ↦ C.obj (op m)) (n + 1)) ≫ integralOperationsTowerStep C n =
      f ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
        Pi.π (fun m : ℕ ↦ C.obj (op m)) n := by
  have h := congrArg (fun k ↦ k ≫ Pi.π (fun m : ℕ ↦ C.obj (op m)) n)
    (cocone_fst_zero (scalarRoosBoundary C) f hf)
  simp only [scalarRoosBoundary, towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp, Category.assoc,
    Pi.lift_comp_π, zero_comp, sub_eq_zero] at h
  simpa only [scalarRoosBoundary, towerTransitionEndomorphism, towerProductShift,
    Category.assoc] using h.symm

private theorem roos_boundary_zero
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) {P : CochainComplex A ℤ}
    (a : ∀ n : ℕ, P ⟶ C.obj (op n))
    (ha : ∀ n : ℕ, a (n + 1) ≫ integralOperationsTowerStep C n = a n) :
    Pi.lift a ≫ scalarRoosBoundary C = 0 := by
  apply Pi.hom_ext
  intro n
  have hb := (towerTransitionEndomorphism_eq_iff
    (integralOperationsTowerStep C) (scalarRoosBoundary C)).mp rfl n
  rw [Category.assoc, hb, Preadditive.comp_sub, ← Category.assoc,
    Pi.lift_comp_π, Pi.lift_comp_π, ha n, sub_self, zero_comp]

end ScalarRoosLiftProof

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

abbrev scalarModelRoosZeroLiftType
    (_SL : CoefficientDerivedSystemCalculus l L X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ) : Type _ :=
  (completedOrdinaryScalarComplex l L F j X).obj
      ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ⟶
    integralOperationsRoos
      (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor

def scalarModelRoosZeroLiftZero
    (SL : CoefficientDerivedSystemCalculus l L X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D) : Prop :=
  ∀ i : ℤ, h.f i ≫
    (CochainComplex.mappingCocone.snd (scalarRoosBoundary
      (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor)).v i (i - 1) (by omega) = 0

def scalarModelRoosZeroLiftCoordinates
    (SL : CoefficientDerivedSystemCalculus l L X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
    (x : (P.obj.X i).val.obj U) (y : (D.X i).val.obj (op (n, U.unop))),
    ((f.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex
        (.up ℤ)).obj D).asFunctor)).f i ≫
      (Pi.π (fun m : ℕ ↦
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U)
      (completedScalarTensorSection l E L ι X (P.obj.X i) U t x) =
        integralComparisonRestrictedSection l L X (D.X i) n U y →
    ((h.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
      (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor)).f i ≫
      (Pi.π (fun m : ℕ ↦
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor.obj (op m)) n).f i).val.app U)
      (completedScalarTensorSection l L F j X
        (((completedOrdinaryScalarComplex l E L ι X).obj P.obj).X i) U s
        (completedScalarTensorSection l E L ι X (P.obj.X i) U t x)) =
      integralComparisonRestrictedSection l F X
        ((integralComparisonSequenceScalarModel l L F j X).E.obj (D.X i)) n U
        (integralComparisonSequenceTensorSection l L F j X (D.X i)
          (op (n, U.unop))
          ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s) y)

-- The existing statement retains realization choices unused by the strict construction.
set_option linter.unusedVariables false in
/-- The realization/transpose construction supplies a lift with its two strict
conditions. The factorization identity is deliberately isolated in the next
stage, so this theorem records only the construction data.

Source: Stacks 06YY, 0941; Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-zero-lift-core)

Proof in words: transpose the normalized quotient-system scalar unit through
ordinary scalar adjunction to obtain a comparison at each quotient level. Its
naturality and tensor formula follow from the scalar residue square and the
normalized units. The vanishing shifted coordinate of f makes its first
coordinates strictly compatible. Extend these coordinates, compose with the
levelwise comparisons, and lift their product to the mapping cocone with zero
shifted cochain. The projection identities and tensor naturality give both
required properties. -/
theorem scalarModelRoosZeroLift_core
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor)).v i (i - 1) (by omega) = 0) :
    ∃ h : scalarModelRoosZeroLiftType l E L F ι j X SL P D,
      scalarModelRoosZeroLiftZero l E L F ι j X SL P D h ∧
      scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h := by
  let C := ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D
  let C' := ((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
    (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
      (.up ℤ)).obj D)
  let T := completedOrdinaryScalarComplex l L F j X
  let a (n : ℕ) := f ≫ CochainComplex.mappingCocone.fst
    (scalarRoosBoundary C.asFunctor) ≫ Pi.π (fun m : ℕ ↦ C.asFunctor.obj (op m)) n
  let c (n : ℕ) := T.map (a n) ≫ ScalarRoosLiftProof.levelChange l L F j X D n
  have hc (n : ℕ) : c (n + 1) ≫ integralOperationsTowerStep C'.asFunctor n = c n := by
    have ha : a (n + 1) ≫ integralOperationsTowerStep C.asFunctor n = a n :=
      ScalarRoosLiftProof.roos_compatible C.asFunctor f hf n
    dsimp only [c]
    unfold integralOperationsTowerStep at ha ⊢
    rw [Category.assoc, ← ScalarRoosLiftProof.levelChange_horizontal l L F j X D
      ((homOfLE (Nat.le_succ n)).op), ← Category.assoc, ← T.map_comp, ha]
  have hz : Pi.lift c ≫ scalarRoosBoundary C'.asFunctor = 0 :=
    ScalarRoosLiftProof.roos_boundary_zero C'.asFunctor c hc
  let h : scalarModelRoosZeroLiftType l E L F ι j X SL P D :=
    CochainComplex.mappingCocone.lift (scalarRoosBoundary C'.asFunctor) (Pi.lift c) 0
      (by rw [hz]; simp)
  refine ⟨h, ?_, ?_⟩
  · intro i
    change (CochainComplex.mappingCocone.lift (scalarRoosBoundary C'.asFunctor)
      (Pi.lift c) 0 _).f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary C'.asFunctor)).v
          i (i - 1) (by omega) = 0
    exact CochainComplex.mappingCocone.lift_f_snd_v _ _ _ _ i (i - 1) (by omega)
  · intro n i U s t x y hxy
    have hp : h ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C'.asFunctor) ≫
        Pi.π (fun m : ℕ ↦ C'.asFunctor.obj (op m)) n = c n := by
      rw [← Category.assoc, CochainComplex.mappingCocone.lift_fst, Pi.lift_comp_π]
    change ((h ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C'.asFunctor) ≫
      Pi.π (fun m : ℕ ↦ C'.asFunctor.obj (op m)) n).f i).val.app U _ = _
    rw [hp]
    change ((ScalarRoosLiftProof.scalarComponentNat l L F j X n).app (D.X i)).val.app U
      (((completedOrdinaryScalarExtension l L F j X).map ((a n).f i)).val.app U
        (completedScalarTensorSection l L F j X _ U s
          (completedScalarTensorSection l E L ι X _ U t x))) = _
    rw [completedScalarTensorSection_naturality]
    have hxy' : ((a n).f i).val.app U
        (completedScalarTensorSection l E L ι X _ U t x) =
      integralComparisonRestrictedSection l L X (D.X i) n U y := hxy
    rw [hxy']
    exact ScalarRoosLiftProof.scalarComponent_tensor l L F j X (D.X i) n U s y

end WeilConjectures
