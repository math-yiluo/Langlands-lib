/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AffineSpaceRationalLine
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralTateLineConstructible
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseRestriction

/-! # Tensor calculus for rational affine-space induction

Source: blueprint `sk-cor-affine-space-rational-induction.proof.md`, both paragraphs
(blueprint: lem-sfb-rational-affine-tensor-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj MonoidalCategory TensorProduct
open Opposite
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] InternalAbelianSheafModule.sheafTensorIso
  DerivedCategory.singleFunctors
  RationalP1.line upperStar Functor.leftDerivedFunctor
  Functor.singleFunctorCompLeftDerivedFunctorIso RationalP1.lineComparison
  leftDerivedUpperStarComp monoidal_leftDerivedUpperStar
  InternalAbelianSheafModule.comparison_closed
  Mod.monoidalClosed DerivedCategory.monoidalClosed upperStarFromPoint
  Functor.mapDerivedCategory

attribute [local instance] DerivedCategory.commShiftTensorRight
attribute [-instance] RationalP1.internalTensorCommShift RationalP1.internalMonoidal
  supportModules_grothendieck hasTensor_cochainComplex monoidalCategoryStruct_cochainComplex
  monoidalCategory_cochainComplex in
section

/-- The recorded positive tensor power, transported back to internal modules.
Source: blueprint `definition-tate-twists`, signed powers
(blueprint: lem-sfb-rational-affine-tensor-calculus). -/
def rationalTatePowerFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ℕ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  rationalTwistFunctor Λ X
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).inverse.obj
        (spSignedTwist X (condensedRingObj Λ X) L (d : ℤ)))

/-- Pullback followed by the specified degree-d tensor power and the shift [2d].
Source: blueprint affine-space induction, twist/shift comparison
(blueprint: lem-sfb-rational-affine-tensor-calculus). -/
def rationalTatePull
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    DerivedCategory (DiagonalCoefficients.Modules (RationalP1.coefficient ℓ c).X Y) ⥤
    DerivedCategory (DiagonalCoefficients.Modules (RationalP1.coefficient ℓ c).X X) :=
  moduleObjectDerivedPullback (RationalP1.coefficient ℓ c).X f ⋙
    rationalTatePowerFunctor (RationalP1.coefficient ℓ c).X X (RationalP1.line ℓ c X) d ⋙
      shiftFunctor (DerivedCategory
        (DiagonalCoefficients.Modules (RationalP1.coefficient ℓ c).X X)) (2 * (d : ℤ))

/-- Degree one is the original internal Tate line. Source: blueprint signed powers
(blueprint: lem-sfb-rational-affine-tensor-calculus).
Proof: apply the unit isomorphism of the internal/sectionwise equivalence, then single
and tensor functoriality. -/
theorem rationalTatePowerOneIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Nonempty (rationalTatePowerFunctor Λ X L 1 ≅ rationalTwistFunctor Λ X L) := by
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  have e : E.inverse.obj (E.functor.obj L) ≅ L := E.unitIso.symm.app L
  exact ⟨(derivedTensor Λ X).flip.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e)⟩

@[irreducible] private def sectionUnitIso
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor.obj (Mod.regular R) ≅ 𝟙_ _ :=
  InternalAbelianSheafModule.comparison_unitIso (Scheme.ProEt.topology X) R

/-- The zeroth power and zero shift are the identity. Source: blueprint signed powers
(blueprint: lem-sfb-rational-affine-tensor-calculus).
Proof: the sectionwise unit comparison identifies the transported power with the internal
unit. Its single complex is the derived tensor unit; apply the right tensor unitor and
zero-shift isomorphism. -/
theorem rationalTatePowerZeroIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Nonempty (rationalTatePowerFunctor Λ X L 0 ⋙
      shiftFunctor _ (2 * ((0 : ℕ) : ℤ)) ≅ 𝟭 _) := by
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  let e₀ := sectionUnitIso X (condensedRingObj Λ X)
  have e : E.inverse.obj (𝟙_ _) ≅ 𝟙_ _ :=
    E.inverse.mapIso e₀.symm ≪≫ E.unitIso.symm.app _
  have de := (DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
    DerivedCategory.singleFunctorObjUnitIso _
  have t : rationalTatePowerFunctor Λ X L 0 ≅ 𝟭 _ :=
    (derivedTensor Λ X).flip.mapIso de ≪≫ MonoidalCategory.rightUnitorNatIso _
  exact ⟨Functor.isoWhiskerRight t _ ≪≫ Functor.leftUnitor _ ≪≫ shiftFunctorZero _ ℤ⟩

private instance tensorLeftColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : DiagonalCoefficients.Modules Λ X) :
    PreservesColimitsOfShape ℤ ((curriedTensor (DiagonalCoefficients.Modules Λ X)).obj M) :=
  inferInstance

private instance tensorRightColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : DiagonalCoefficients.Modules Λ X) :
    PreservesColimitsOfShape ℤ
      ((curriedTensor (DiagonalCoefficients.Modules Λ X)).flip.obj M) := inferInstance

private instance tensorFourExists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (A B C D : GradedObject ℤ (DiagonalCoefficients.Modules Λ X)) :
    GradedObject.HasTensor₄ObjExt A B C D := inferInstance

private instance tensorLeftGood
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (A B C : GradedObject ℤ (DiagonalCoefficients.Modules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := inferInstance

private instance tensorRightGood
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (A B C : GradedObject ℤ (DiagonalCoefficients.Modules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := inferInstance

attribute [local irreducible] rationalTatePowerFunctor rationalTatePull

private def tensorPower {C : Type*} [Category C] [MonoidalCategory C]
    (L : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => tensorPower L n ⊗ L

@[irreducible] private def tensorPowerMapIso {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (L : C) : ∀ n, F.obj (tensorPower L n) ≅ tensorPower (F.obj L) n
  | 0 => (Functor.Monoidal.εIso F).symm
  | n + 1 => (Functor.Monoidal.μIso F _ _).symm ≪≫
      tensorIso (tensorPowerMapIso F L n) (Iso.refl _)

@[irreducible] private def tensorPowerAddIso {C : Type*} [Category C] [MonoidalCategory C]
    (L : C) (d : ℕ) : ∀ e, tensorPower L d ⊗ tensorPower L e ≅ tensorPower L (d + e)
  | 0 => ρ_ _
  | e + 1 => (α_ _ _ _).symm ≪≫
      tensorIso (tensorPowerAddIso L d e) (Iso.refl _)

attribute [local irreducible] spIntegralTwist spRationalTwist spQbarTwist

universe v w

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
  Sheaf.symmetricCategory in
@[irreducible] private def sectionPowerIso
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
    [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasCoequalizers (Sheaf J AddCommGrpCat.{u})]
    [MonoidalClosed (Sheaf J AddCommGrpCat.{u})]
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf J AddCommGrpCat.{u}) R)
    (e₀ : (InternalAbelianSheafModule.sectionModuleFunctor.{u, v, w} J R).obj
      (𝟙_ _) ≅ 𝟙_ _) :
    ∀ n, (InternalAbelianSheafModule.sectionModuleFunctor.{u, v, w} J R).obj
      (tensorPower L n) ≅ SheafOfModules.scalarTensorPower
        (InternalAbelianSheafModule.sectionRingSheaf.{u, v, w} J R)
        ((InternalAbelianSheafModule.sectionModuleFunctor.{u, v, w} J R).obj L) n := by
  let E := InternalAbelianSheafModule.sectionModuleFunctor.{u, v, w} J R
  intro n
  induction n with
  | zero => exact e₀
  | succ n ih =>
    rw [tensorPower]
    cases n with
    | zero => exact E.mapIso (λ_ L)
    | succ n =>
      let T := SheafOfModules.siteSheafTensorRight.{w, v, u, u}
        (A := InternalAbelianSheafModule.sectionRingSheaf.{u, v, w} J R) (E.obj L)
      let t : E.obj (tensorPower L (n + 1) ⊗ L) ≅
          T.obj (E.obj (tensorPower L (n + 1))) :=
        (InternalAbelianSheafModule.sheafTensorIso.{u, v, w}
          J R (tensorPower L (n + 1)) L).symm
      exact t ≪≫ T.mapIso ih

@[irreducible] private def sectionTensorPowerIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ∀ n, (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor.obj (tensorPower L n) ≅
        spSignedTwist X (condensedRingObj Λ X) L (n : ℤ) :=
  sectionPowerIso (Scheme.ProEt.topology X) (condensedRingObj Λ X) L
    (sectionUnitIso X (condensedRingObj Λ X))

@[irreducible] private def internalTensorPowerIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (n : ℕ) :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).inverse.obj
        (spSignedTwist X (condensedRingObj Λ X) L (n : ℤ)) ≅ tensorPower L n :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).inverse.mapIso
    (sectionTensorPowerIso Λ X L n).symm ≪≫
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).unitIso.symm.app _

@[irreducible] private def singleTensorIso
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (M L : C) (hL : ObjectProperty.flat L) :
    (DerivedCategory.singleFunctor C 0).obj M ⊗
      (DerivedCategory.singleFunctor C 0).obj L ≅
        (DerivedCategory.singleFunctor C 0).obj (M ⊗ L) :=
  tensorIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app M)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app L) ≪≫
    DerivedCategory.QObjTensorQObjIsoOfKFlatRight _ _
      ((CochainComplex.kFlat_single_obj_iff_flat L 0).mpr hL) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) L).app _ ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorRight L) (.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app (M ⊗ L)).symm

@[irreducible] private def singleTensorPowerIso
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (L : C) (hL : ObjectProperty.flat L) : ∀ n,
    (DerivedCategory.singleFunctor C 0).obj (tensorPower L n) ≅
      tensorPower ((DerivedCategory.singleFunctor C 0).obj L) n
  | 0 => DerivedCategory.singleFunctorObjUnitIso C
  | n + 1 => (singleTensorIso _ L hL).symm ≪≫
      tensorIso (singleTensorPowerIso L hL n) (Iso.refl _)

private theorem rationalLine_flat
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] :
    ObjectProperty.flat (RationalP1.line ℓ c X) := by
  let E₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  have h : (spSignedTwist X _ (RationalP1.line ℓ c X) 1).IsFiniteLocallyFreeOfRank 1 := by
    cases c with
    | none =>
      simpa only [RationalP1.coefficient, RationalP1.line] using
        (spTwists_locallyFree X ℓ E₀).2.2
    | some E =>
      simpa only [RationalP1.coefficient, RationalP1.line] using
        (spTwists_locallyFree X ℓ E).2.1
  change ((InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj (RationalP1.coefficient ℓ c).X X)).obj
      (RationalP1.line ℓ c X)).IsFiniteLocallyFreeOfRank 1 at h
  let := h
  apply (InternalAbelianSheafModule.flat_iff_sectionModule.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj (RationalP1.coefficient ℓ c).X X)
      (RationalP1.line ℓ c X)).mpr
  exact ⟨(WeilConjectures.coefficientTwistLine_exact X _ 1).2.1,
    (WeilConjectures.coefficientTwistLine_exact X _ 1).2.2⟩

@[irreducible] private def powerFunctorIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hL : ObjectProperty.flat L) (d : ℕ) :
    rationalTatePowerFunctor Λ X L d ≅
      tensorRight (tensorPower ((DerivedCategory.singleFunctor _ 0).obj L) d) := by
  unfold rationalTatePowerFunctor rationalTwistFunctor
  exact (derivedTensor Λ X).flip.mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso (internalTensorPowerIso Λ X L d) ≪≫
      singleTensorPowerIso L hL d)

@[irreducible] private def rationalPowerFunctorIso
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (d : ℕ) :
    rationalTatePowerFunctor (RationalP1.coefficient ℓ c).X X (RationalP1.line ℓ c X) d ≅
      tensorRight (tensorPower
        ((DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c X)) d) :=
  powerFunctorIso _ X _ (rationalLine_flat ℓ c X) d

@[irreducible] private def tensorRightCompIso {C : Type*} [Category C] [MonoidalCategory C]
    (A B : C) : tensorRight A ⋙ tensorRight B ≅ tensorRight (A ⊗ B) :=
  (tensorRightTensor A B).symm

@[irreducible] private def tensorRightPullIso {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (L : C) : tensorRight L ⋙ F ≅ F ⋙ tensorRight (F.obj L) :=
  (Functor.Monoidal.commTensorRight F L).symm

@[irreducible] private def tensorPowerCongrIso {C : Type*} [Category C] [MonoidalCategory C]
    {L M : C} (e : L ≅ M) : ∀ n, tensorPower L n ≅ tensorPower M n
  | 0 => Iso.refl _
  | n + 1 => tensorIso (tensorPowerCongrIso e n) e

@[irreducible] private def shiftedTensorCompIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory D] [MonoidalCategory E] [HasShift D ℤ] [HasShift E ℤ]
    (G : C ⥤ D) (F : D ⥤ E) (H : C ⥤ E) [F.Monoidal] [F.CommShift ℤ]
    (L : D) (M : E) (h : F.obj L ≅ M) (hcomp : G ⋙ F ≅ H)
    (d e : ℕ) [(tensorRight (tensorPower M e)).CommShift ℤ] :
    (G ⋙ tensorRight (tensorPower L d) ⋙ shiftFunctor D (2 * (d : ℤ))) ⋙
      (F ⋙ tensorRight (tensorPower M e) ⋙ shiftFunctor E (2 * (e : ℤ))) ≅
    H ⋙ tensorRight (tensorPower M (d + e)) ⋙
      shiftFunctor E (2 * ((d + e : ℕ) : ℤ)) := by
  let A := tensorPower L d
  let B := tensorPower M e
  let hp : F.obj A ≅ tensorPower M d :=
    tensorPowerMapIso F L d ≪≫ tensorPowerCongrIso h d
  let step₁ := Functor.isoWhiskerLeft (G ⋙ tensorRight A)
    (Functor.isoWhiskerRight ((F ⋙ tensorRight B).commShiftIso (2 * (d : ℤ)))
      (shiftFunctor E (2 * (e : ℤ))))
  let step₂ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft G (tensorRightPullIso F A))
    (tensorRight B ⋙ shiftFunctor E (2 * (d : ℤ)) ⋙
      shiftFunctor E (2 * (e : ℤ)))
  let step₃ := Functor.isoWhiskerLeft (G ⋙ F)
    (Functor.isoWhiskerRight ((curriedTensor E).flip.mapIso hp)
      (tensorRight B ⋙ shiftFunctor E (2 * (d : ℤ)) ⋙
        shiftFunctor E (2 * (e : ℤ))))
  let step₄ := Functor.isoWhiskerLeft (G ⋙ F)
    (Functor.isoWhiskerRight
      (tensorRightCompIso (tensorPower M d) B ≪≫
        (curriedTensor E).flip.mapIso (tensorPowerAddIso M d e))
      (shiftFunctor E (2 * (d : ℤ)) ⋙ shiftFunctor E (2 * (e : ℤ))))
  let step₅ := Functor.isoWhiskerRight hcomp
    (tensorRight (tensorPower M (d + e)) ⋙
      shiftFunctor E (2 * (d : ℤ)) ⋙ shiftFunctor E (2 * (e : ℤ)))
  let step₆ := Functor.isoWhiskerLeft (H ⋙ tensorRight (tensorPower M (d + e)))
    (shiftFunctorAdd' E (2 * (d : ℤ)) (2 * (e : ℤ))
      (2 * ((d + e : ℕ) : ℤ)) (by push_cast; ring)).symm
  exact step₁ ≪≫ step₂ ≪≫ step₃ ≪≫ step₄ ≪≫ step₅ ≪≫ step₆

@[irreducible] private def nativeTensorRightCommShift
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (K : DerivedCategory C) : (tensorRight K).CommShift ℤ :=
  DerivedCategory.commShiftTensorRight C K

@[irreducible] private def pullSingleLineIso
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] :
    (moduleObjectDerivedPullback (RationalP1.coefficient ℓ c).X f).obj
      ((DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c Y)) ≅
        (DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c X) :=
  ((upperStar (RationalP1.coefficient ℓ c).X f).singleFunctorCompLeftDerivedFunctorIso.app _) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (RationalP1.lineComparison ℓ c f)

@[irreducible] private def rationalPullFunctorIso
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)] (d : ℕ) :
    rationalTatePull ℓ c f d ≅
      moduleObjectDerivedPullback (RationalP1.coefficient ℓ c).X f ⋙
      tensorRight (tensorPower
        ((DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c X)) d) ⋙
        shiftFunctor _ (2 * (d : ℤ)) := by
  unfold rationalTatePull
  exact Functor.isoWhiskerLeft (moduleObjectDerivedPullback (RationalP1.coefficient ℓ c).X f)
    (Functor.isoWhiskerRight (rationalPowerFunctorIso ℓ c X d)
      (shiftFunctor _ (2 * (d : ℤ))))

private theorem rationalTatePull_comp
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)]
    [∀ z : Z, Invertible (ℓ : Z.residueField z)] (d e : ℕ) :
    Nonempty (rationalTatePull ℓ c g d ⋙ rationalTatePull ℓ c f e ≅
      rationalTatePull ℓ c (f ≫ g) (d + e)) := by
  let Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
    (RationalP1.coefficient ℓ c).X
  let F : DerivedCategory (DiagonalCoefficients.Modules Λ Y) ⥤
      DerivedCategory (DiagonalCoefficients.Modules Λ X) :=
    moduleObjectDerivedPullback Λ f
  let G : DerivedCategory (DiagonalCoefficients.Modules Λ Z) ⥤
      DerivedCategory (DiagonalCoefficients.Modules Λ Y) :=
    moduleObjectDerivedPullback Λ g
  let H : DerivedCategory (DiagonalCoefficients.Modules Λ Z) ⥤
      DerivedCategory (DiagonalCoefficients.Modules Λ X) :=
    moduleObjectDerivedPullback Λ (f ≫ g)
  let L := (DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c Y)
  let M := (DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c X)
  let : F.CommShift ℤ := unboundedLocalizingPullbackCommShift Λ f
  let : F.Monoidal := monoidal_leftDerivedUpperStar Λ f
  let : (tensorRight (tensorPower M e)).CommShift ℤ :=
    nativeTensorRightCommShift (tensorPower M e)
  let h := pullSingleLineIso ℓ c f
  exact ⟨Functor.isoWhiskerRight (rationalPullFunctorIso ℓ c g d) _ ≪≫
    Functor.isoWhiskerLeft _ (rationalPullFunctorIso ℓ c f e) ≪≫
      shiftedTensorCompIso G F H L M h (leftDerivedUpperStarComp Λ f g).symm d e ≪≫
        (rationalPullFunctorIso ℓ c (f ≫ g) (d + e)).symm⟩

private theorem rationalLine_lisse
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] :
    IsLisseCoefficientModule (X := X) (RationalP1.coefficient ℓ c).X
      (RationalP1.line ℓ c X) := by
  obtain ⟨I, U, v, ζ, e, hc, _, _, _, hE, hΩ⟩ := spTwists_commonCover X ℓ
  apply AlgebraicGeometry.ProEtale.lisse_of_raw_free
  apply IntegralRestriction.locallyFree_of_trivial_cover X _ (RationalP1.line ℓ c X) U v hc
  intro i
  change Nonempty ((spSignedTwist X _ (RationalP1.line ℓ c X) 1).over (U i) ≅
    (spSignedTwist X _ (RationalP1.line ℓ c X) 0).over (U i))
  cases c with
  | none => simpa only [RationalP1.coefficient, RationalP1.line] using hΩ i
  | some E => simpa only [RationalP1.coefficient, RationalP1.line] using (hE E i).2
private theorem unit_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [ObjectProperty.IsClosedUnderIsomorphisms (constantModelBoundedConstructible Λ X)] :
    constantModelBoundedConstructible Λ X (𝟙_ _) := by
  let P := constantModelBoundedConstructible Λ X
  apply P.prop_of_iso (DerivedCategory.singleFunctorObjUnitIso _)
  apply single_constructible
  rw [IsConstantModelConstructible,
    ite_eq_left (show CompactSpace X ∧ QuasiSeparatedSpace X from ⟨inferInstance,
      inferInstance⟩)]
  apply stratified_of_finiteModel Λ X
  apply lisse_finiteModel
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨1, ⟨(Functor.Monoidal.εIso (upperStar Λ (𝟙 X))).symm ≪≫ ?_⟩⟩
  exact (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular _)).symm

private theorem rationalTatePull_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) (d : ℕ)
    (K : DerivedCategory (DiagonalCoefficients.Modules (RationalP1.coefficient ℓ c).X Y))
    (hK : constantModelBoundedConstructible (RationalP1.coefficient ℓ c).X Y K) :
    constantModelBoundedConstructible (RationalP1.coefficient ℓ c).X X
      ((moduleObjectDerivedPullback (RationalP1.coefficient ℓ c).X f).obj K ⊗
        tensorPower ((DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c X)) d) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  let : ∀ x : X, Invertible (ℓ : X.residueField x) :=
    fun x ↦ (RationalP1.residueIsUnit ℓ k (ringChar k) (Fact.out : ringChar k ≠ ℓ)
      X (X ↘ Spec (.of k)) x).invertible
  let Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
    (RationalP1.coefficient ℓ c).X
  let P := constantModelBoundedConstructible Λ X
  have hP : P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated := by
    cases c with
    | none =>
      dsimp only [P, Λ, RationalP1.coefficient]
      exact ⟨(constantModelBoundedConstructible_field_triangulated ℓ X).2.1,
        (constantModelBoundedConstructible_field_triangulated ℓ X).2.2.1⟩
    | some E =>
      dsimp only [P, Λ, RationalP1.coefficient]
      exact ⟨((constantModelBoundedConstructible_field_triangulated ℓ X).1 E).1,
        ((constantModelBoundedConstructible_field_triangulated ℓ X).1 E).2.1⟩
  let := hP.1
  let := hP.2
  have hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    cases c with
    | none => exact Or.inr ⟨eqToIso (by rfl)⟩
    | some E => exact Or.inl ⟨E, ⟨eqToIso (by rfl)⟩⟩
  have ht := (constantModelBoundedConstructible_derivedTensor ℓ (ringChar k)
    (Fact.out : ringChar k ≠ ℓ) (X ↘ Spec (.of k)) Λ hΛ).1
  have hl : P ((DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c X)) :=
    single_constructible Λ X _
      (by
        rw [IsConstantModelConstructible,
          ite_eq_left (show CompactSpace X ∧ QuasiSeparatedSpace X from ⟨inferInstance,
            inferInstance⟩)]
        exact stratified_of_finiteModel Λ X _
          (lisse_finiteModel Λ X _ (rationalLine_lisse ℓ c X)))
  have hu : P (𝟙_ _) := unit_constructible Λ X
  have hp : ∀ n, P (tensorPower
      ((DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c X)) n) := by
    intro n
    induction n with
    | zero => exact hu
    | succ n ih => exact ht _ _ ih hl
  have hk := pullback_bounded_constructible Λ f (pullback_constructible Λ f) K hK
  have htw := ht _ _ hk (hp d)
  exact htw

/-- Positive rational Tate powers preserve bounded constructibility and compose across
inverse image.
These are assertions about ambient tensor functors, with no exceptional inverse image.
Source: blueprint `sk-cor-affine-space-rational-induction.proof.md`, both paragraphs;
expanded node steps 1--3 and 7 (blueprint: lem-sfb-rational-affine-tensor-calculus).

Proof: the common compatible-root cover trivializes the rational and closure lines.
The sectionwise/internal tensor comparison identifies their nonnegative powers with
internal tensor powers, including the unit at zero. Tensor by each power is exact and
preserves coproducts, with inverse tensor by the dual power. On a pulled-back finite
constructible stratification refine the constant-model covers by this root cover;
tensor there is tensor with the unit, so the original finitely presented scalar module
is unchanged. Cohomology commutes with this exact tensor; shifts reindex it. Exact
pullback preserves the same constant models. This proves bounded constructibility.
At degree zero the tensor unit and zero shift leave just pullback. At degree one,
the counit of the sectionwise equivalence and tensor unitor identify the power with
the original line. For composition, use Cartesian Tate-line pullback, the monoidal
inverse-image tensor comparison, associativity of positive powers, and shift addition.
Exact pullbacks commute with shifts and compose via leftDerivedUpperStarComp. All
comparisons arise on complexes and descend naturally, so they apply to unbounded objects.
The empty scheme and zero object use the same unit and shift comparisons. -/
theorem rationalAffineTensorCalculus
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    (∀ (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ),
      ∀ K, constantModelBoundedConstructible (RationalP1.coefficient ℓ c).X Y K →
        constantModelBoundedConstructible (RationalP1.coefficient ℓ c).X X
          ((rationalTatePull ℓ c f d).obj K)) ∧
    (∀ (X Y Z : Scheme.{u}) [X.Over (Spec (.of k))]
      [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
      (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
      (d e : ℕ),
      Nonempty (rationalTatePull ℓ c g d ⋙ rationalTatePull ℓ c f e ≅
        rationalTatePull ℓ c (f ≫ g) (d + e))) := by
  constructor
  · intro X Y _ _ _ _ _ _ _ _ f _ d K hK
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ Spec (.of k))
    let : ∀ x : X, Invertible (ℓ : X.residueField x) :=
      fun x ↦ (RationalP1.residueIsUnit ℓ k (ringChar k) (Fact.out : ringChar k ≠ ℓ)
        X (X ↘ Spec (.of k)) x).invertible
    let P := constantModelBoundedConstructible (RationalP1.coefficient ℓ c).X X
    have hP : P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated := by
      cases c with
      | none => exact ⟨(constantModelBoundedConstructible_field_triangulated ℓ X).2.1,
          (constantModelBoundedConstructible_field_triangulated ℓ X).2.2.1⟩
      | some E => exact ⟨((constantModelBoundedConstructible_field_triangulated ℓ X).1 E).1,
          ((constantModelBoundedConstructible_field_triangulated ℓ X).1 E).2.1⟩
    let := hP.1
    let := hP.2
    unfold rationalTatePull
    apply P.le_shift (2 * (d : ℤ))
    exact P.prop_of_iso ((rationalPowerFunctorIso ℓ c X d).symm.app _)
      (rationalTatePull_constructible ℓ c k X Y f d K hK)
  · intro X Y Z _ _ _ f g _ _ d e
    let : ∀ x : X, Invertible (ℓ : X.residueField x) :=
      fun x ↦ (RationalP1.residueIsUnit ℓ k (ringChar k) (Fact.out : ringChar k ≠ ℓ)
        X (X ↘ Spec (.of k)) x).invertible
    let : ∀ y : Y, Invertible (ℓ : Y.residueField y) :=
      fun y ↦ (RationalP1.residueIsUnit ℓ k (ringChar k) (Fact.out : ringChar k ≠ ℓ)
        Y (Y ↘ Spec (.of k)) y).invertible
    let : ∀ z : Z, Invertible (ℓ : Z.residueField z) :=
      fun z ↦ (RationalP1.residueIsUnit ℓ k (ringChar k) (Fact.out : ringChar k ≠ ℓ)
        Z (Z ↘ Spec (.of k)) z).invertible
    exact rationalTatePull_comp ℓ c f g d e

end

end AlgebraicGeometry.ProEtale.CondensedRing
