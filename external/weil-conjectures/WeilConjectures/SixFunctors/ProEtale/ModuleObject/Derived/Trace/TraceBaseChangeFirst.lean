/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.SixFunctors.Monoidal
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.LeftCoefficientProjectionAction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

/-!
# Trace and base-change rearrangement before the first triangle

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
`sk-thm-int-restriction-line.proof.md`, (1), first triangle
(blueprint: lem-sfb-trace-base-change-first).

All operations below are on the ordinary unbounded derived categories of internal
modules over the pulled-back condensed coefficient ring. The square and tensor
comparisons, projection maps and source identification are specified constructions.
The internal-module tensor helpers are owned by this item; the general ringed-topos
tensor-pullback interface remains publicly imported with its recorded declaration.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward false
attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local irreducible] DerivedCategory.Qh
  CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedTensorComparison CategoryTheory.Functor.leftDerivedFunctorCounit

set_option synthInstance.maxSize 2048

-- Reuse the existing compact structures instead of rebuilding the internal-module tensors.
attribute [local instance 20000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local irreducible] CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monObj_sheafCompose_obj
  AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

section NamedSheafSymmetry
attribute [local instance] Sheaf.monoidalCategory
namespace CategoryTheory
/-- The canonical sheaf symmetry with its canonical braiding named explicitly.
The record update is definitionally equal to the existing symmetric structure;
it prevents comparison of two separately generated braiding structures downstream.
Source: the symmetric monoidal sheafification construction in Mathlib
(blueprint: lem-sfb-trace-base-change-first). -/
@[instance_reducible]
def traceSheafSymmetric
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    (A : Type u₂) [Category.{v₂} A] [MonoidalCategory A] [SymmetricCategory A]
    [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] :
    SymmetricCategory (Sheaf J A) :=
  { Sheaf.symmetricCategory J A with
    toBraidedCategory := Sheaf.braidedCategory J A }
end CategoryTheory
end NamedSheafSymmetry
attribute [local instance 20000] CategoryTheory.traceSheafSymmetric

namespace CategoryTheory
/-- The canonical derived Koszul braiding, assembled while the base category is abstract.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def traceCanonicalDerivedBraiding
    {A : Type u₁} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasDerivedCategory.{u + 1} A]
    [MonoidalCategory A] [MonoidalClosed A] [MonoidalPreadditive A] [BraidedCategory A]
    [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory A) : K ⊗ L ≅ L ⊗ K :=
  (DerivedCategory.braidedCategory' A).braiding K L
end CategoryTheory

attribute [local irreducible] DerivedCategory.braidedCategory'

namespace AlgebraicGeometry.ProEtale.CondensedRing
section ModuleProofCaches
-- These are proofs of existing instance facts. Activate them only in private proof sections.
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

omit [IsCommMonObj Λ] in
private theorem traceModuleGrothendieck :
    IsGrothendieckAbelian.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  inferInstance
private theorem traceModuleFlat :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  inferInstance
private theorem traceTensorLeft
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft A) := inferInstance
private theorem traceTensorRight
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    PreservesColimitsOfSize.{0, 0} (tensorRight A) := inferInstance
attribute [local instance 20000] traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight
private theorem traceGradedTensor
    (A B : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    A.HasTensor B := inferInstance
private theorem traceGradedTensorLeft
    (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    A.HasGoodTensor₁₂Tensor B C := inferInstance
private theorem traceGradedTensorRight
    (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    A.HasGoodTensorTensor₂₃ B C := inferInstance
private theorem traceGradedTensorFour
    (A B C D : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    A.HasTensor₄ObjExt B C D := inferInstance
end ModuleProofCaches
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
section OrdinaryPullbackStructures
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Canonical strong monoidal module inverse image.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first). -/
instance condensedUpperStarMonoidal : (upperStar Λ f).Monoidal :=
  monoidal_upperStar Λ f

/-- Module inverse image preserves flat modules.
Source: Stacks 0G7E (blueprint: lem-sfb-trace-base-change-first).
Proof: pass through the exact internal-to-sectionwise module equivalence. The
normalized tensor comparison is the usual scalar-extension comparison there by its
unit-generator equations. Pullback of a flat sheaf is flat by the local tensor
criterion, so tensoring with the pulled-back module is exact. Transport back through
the exact equivalence. This is flatness in the existing monoidal module category. -/
@[instance] theorem condensedUpperStarPreservesFlat : (upperStar Λ f).PreservesFlat := by
  have hf := inverseImageModule_preservesFlat f (condensedRingObj Λ Y)
    (condensedRingObj Λ X) (asIso (condensedPullbackHom Λ f)).inv
  refine ⟨fun {M} hM ↦ ?_⟩
  exact ObjectProperty.flat.prop_of_iso
    ((Functor.isoWhiskerLeft
      ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).app M).symm
    (hf.flat_obj hM)

end OrdinaryPullbackStructures
end AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] NatTrans.vcomp

section MapTensorHelper

variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  [MonoidalCategory D] [BraidedCategory D] [HasCoequalizers D]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {R : C} [MonObj R] [IsCommMonObj R]

private theorem map_tensor_inverse (M N : Mod C R) :
    F.map (Mod.tensorObjπ M N) ≫ (Functor.OplaxMonoidal.δ (F.mapMod R) M N).hom =
      Functor.OplaxMonoidal.δ F M.X N.X ≫
        Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N) := by
  apply (cancel_mono (F.mapModTensorIso M N).hom.hom).1
  change (F.map (Mod.tensorObjπ M N) ≫ (F.mapModTensorIso M N).inv.hom) ≫ _ = _
  have hi := congrArg Mod.Hom.hom (F.mapModTensorIso M N).inv_hom_id
  simp only [Mod.comp_hom', Mod.id_hom'] at hi
  rw [Category.assoc, hi]
  erw [Category.comp_id]
  erw [Category.assoc, Functor.tensorπ_mapModTensorIso_hom_hom,
    Functor.Monoidal.δ_μ_assoc]

end MapTensorHelper

section ExtensionTensorHelper

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [HasEqualizers C] [MonoidalClosed C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (α : R ⟶ S) [IsMonHom α] [IsIso α]

omit [HasEqualizers C] [MonoidalClosed C] in
private theorem extension_tensor_inverse
    (hunit : ∀ A : Mod C R, Mod.extendUnitHom α A ≫
      ((Mod.extendScalarsIsoComapInv α).hom.app A).hom = 𝟙 _) (M N : Mod C R) :
    Mod.tensorObjπ M N ≫ Mod.extendUnitHom α (M ⊗ N) ≫
        (Functor.OplaxMonoidal.δ (Mod.extendScalars α) M N).hom =
      (Mod.extendUnitHom α M ⊗ₘ Mod.extendUnitHom α N) ≫
        Mod.tensorObjπ ((Mod.extendScalars α).obj M) ((Mod.extendScalars α).obj N) := by
  rw [Functor.Monoidal.transport_δ]
  simp only [Iso.symm_inv, Iso.symm_hom, Mod.comp_hom']
  rw [reassoc_of% (hunit (M ⊗ N))]
  change Mod.tensorObjπ M N ≫ (Mod.comapTensorIso (asIso α).inv M N).inv.hom ≫ _ = _
  have hπ : Mod.tensorObjπ M N ≫ (Mod.comapTensorIso (asIso α).inv M N).inv.hom =
      Mod.tensorObjπ ((Mod.comap (asIso α).inv).obj M)
        ((Mod.comap (asIso α).inv).obj N) := by
    apply (cancel_mono (Mod.comapTensorIso (asIso α).inv M N).hom.hom).1
    have hi := congrArg Mod.Hom.hom (Mod.comapTensorIso (asIso α).inv M N).inv_hom_id
    simp only [Mod.comp_hom', Mod.id_hom'] at hi
    rw [Category.assoc, hi]
    erw [Category.comp_id]
    exact (Mod.tensorπ_comapTensorIso_hom_hom (asIso α).inv M N).symm
  erw [reassoc_of% hπ]
  have h (A : Mod C R) : ((Mod.extendScalarsIsoComapInv α).inv.app A).hom =
      Mod.extendUnitHom α A := by
    apply (cancel_mono ((Mod.extendScalarsIsoComapInv α).hom.app A).hom).1
    have hi := congrArg Mod.Hom.hom ((Mod.extendScalarsIsoComapInv α).inv_hom_id_app A)
    simp only [Mod.comp_hom', Mod.id_hom'] at hi
    exact hi.trans (hunit A).symm
  rw [MonoidalCategory.tensorHom_def]
  simp only [Mod.comp_hom']
  erw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft]
  rw [h, h]
  erw [← tensorHom_def_assoc]

end ExtensionTensorHelper

section OrdinaryBraidingHelpers
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u' v'
section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
  [HasCoequalizers D]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {R : C} [MonObj R] [IsCommMonObj R]
private theorem mapMod_braided (M N : Mod C R) :
    Functor.LaxMonoidal.μ (F.mapMod R) M N ≫ (F.mapMod R).map (β_ M N).hom =
      (β_ ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom ≫
        Functor.LaxMonoidal.μ (F.mapMod R) N M := by
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N))]
  change Mod.tensorObjπ _ _ ≫ (F.mapModTensorIso M N).hom.hom ≫
      F.map (β_ M N).hom.hom =
    Mod.tensorObjπ _ _ ≫ (β_ ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom.hom ≫
      (F.mapModTensorIso N M).hom.hom
  erw [reassoc_of% Functor.tensorπ_mapModTensorIso_hom_hom, ← F.map_comp]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX, F.map_comp]
  rw [Functor.LaxBraided.braided_assoc]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc,
    Functor.tensorπ_mapModTensorIso_hom_hom]
  rfl
end
section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (ψ : S ⟶ R) [IsMonHom ψ] [IsIso ψ]
private theorem comap_braided (M N : Mod C R) :
    Functor.LaxMonoidal.μ (Mod.comap ψ) M N ≫ (Mod.comap ψ).map (β_ M N).hom =
      (β_ ((Mod.comap ψ).obj M) ((Mod.comap ψ).obj N)).hom ≫
        Functor.LaxMonoidal.μ (Mod.comap ψ) N M := by
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.tensorObjπ ((Mod.comap ψ).obj M) ((Mod.comap ψ).obj N))]
  change Mod.tensorObjπ _ _ ≫ (Mod.comapTensorIso ψ M N).hom.hom ≫
      (β_ M N).hom.hom =
    Mod.tensorObjπ _ _ ≫ (β_ ((Mod.comap ψ).obj M) ((Mod.comap ψ).obj N)).hom.hom ≫
      (Mod.comapTensorIso ψ N M).hom.hom
  have ht := Mod.tensorπ_comapTensorIso_hom_hom ψ M N
  rw [← Category.assoc, ht]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc,
    Mod.tensorπ_comapTensorIso_hom_hom]
  rfl
end
section Extend
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C] [HasEqualizers C] [MonoidalClosed C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
@[instance_reducible]
private noncomputable def extend_braided : (Mod.extendScalars φ).LaxBraided := by
  let ψ := (asIso φ).inv
  let : (Mod.comap ψ : Mod C R ⥤ Mod C S).LaxBraided :=
    { braided := comap_braided ψ }
  let i := Mod.extendScalarsIsoComapInv φ
  let : NatTrans.IsMonoidal i.symm.hom := {
    unit := by simp [i, Functor.Monoidal.transport_ε]
    tensor M N := by simp [i, Functor.Monoidal.transport_μ] }
  exact Functor.LaxBraided.ofNatIso i.symm
end Extend

end OrdinaryBraidingHelpers

namespace CategoryTheory.Functor
open Functor.LaxMonoidal Functor.OplaxMonoidal _root_.DerivedCategory
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (hG : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X =
    δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
private local instance : BraidedCategory (DerivedCategory C) := DerivedCategory.braidedCategory' C
private local instance : BraidedCategory (DerivedCategory D) := DerivedCategory.braidedCategory' D
include hG
/-- The generic derived braiding theorem applies to the same tensor comparison. -/
private theorem generic_derived_braid
    (K M : DerivedCategory C) :
    letI := F.residueDerivedMonoidal
    F.leftDerivedFunctor.map (β_ K M).hom ≫ δ F.leftDerivedFunctor M K =
      δ F.leftDerivedFunctor K M ≫
        (β_ (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M)).hom := by
  let := F.residueDerivedMonoidal
  simpa only [Functor.leftDerivedFunctorMonoidal_δ] using
    F.leftDerivedFunctor_map_braiding_hom_δ hG K M

/-- The canonical monoidal structure on the derived functor preserves the
Koszul braiding, by its comparison square on K-flat resolutions. -/
private theorem generic_derived_braid_lax
    (K M : DerivedCategory C) :
    letI := F.residueDerivedMonoidal
    μ F.leftDerivedFunctor K M ≫ F.leftDerivedFunctor.map (β_ K M).hom =
      (β_ (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M)).hom ≫
        μ F.leftDerivedFunctor M K := by
  let := F.residueDerivedMonoidal
  exact Functor.Monoidal.μ_comp_map_braiding_hom_of_δ _ K M
    (generic_derived_braid F hG K M)

end CategoryTheory.Functor

namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
omit [F.PreservesFlat] in
/-- The degree-zero unit comparison, packaged before specialization to sheaf modules.
This is the explicit composite through the exact-functor comparison, the quotient
factorization and the ordinary unit isomorphism; no data is chosen.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def traceDegreeZeroUnitIso : F.leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  F.leftDerivedTensorUnitIso

variable {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [Abelian.HasFunctorialFlatResolution E]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
  (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesFlat] [H.IsLeftAdjoint] [H.Monoidal]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem derived_comp_explicit (τ : H ≅ F ⋙ G) [NatTrans.IsMonoidal τ.hom]
    (M N : DerivedCategory C) :
    (H.leftDerivedFunctorNatIso τ ≪≫ F.leftDerivedFunctorCompIso G).hom.app (M ⊗ N) ≫
        G.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app M).app N) ≫
        (G.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj M)).app
          (F.leftDerivedFunctor.obj N) =
      ((H.leftDerivedTensorComparison.app M).app N) ≫
        ((H.leftDerivedFunctorNatIso τ ≪≫ F.leftDerivedFunctorCompIso G).hom.app M ⊗ₘ
          (H.leftDerivedFunctorNatIso τ ≪≫ F.leftDerivedFunctorCompIso G).hom.app N) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [map_leftDerivedTensorComparison_app_app_comp,
    Iso.hom_inv_id_app_assoc, leftDerivedTensorComparison_naturality_app_assoc]
  simp only [tensorHom_comp_tensorHom]

end CategoryTheory.Functor

attribute [local irreducible] CategoryTheory.Functor.residueDerivedMonoidal

private theorem tensor_square_family
    {C V : Type*} [Category C] [Category V] [MonoidalCategory C] [MonoidalCategory V]
    {I : Type*} (L : I → C ⥤ V)
    (dL : ∀ i, ∀ K M : C, (L i).obj (K ⊗ M) ⟶ (L i).obj K ⊗ (L i).obj M)
    {A B : C ⥤ V}
    (dA : ∀ K M, A.obj (K ⊗ M) ⟶ A.obj K ⊗ A.obj M)
    (dB : ∀ K M, B.obj (K ⊗ M) ⟶ B.obj K ⊗ B.obj M)
    {i j : I} (h : i = j) (a : L i ≅ A) (b : L j ≅ B)
    (ha : ∀ K M, a.hom.app (K ⊗ M) ≫ dA K M =
      dL i K M ≫ (a.hom.app K ⊗ₘ a.hom.app M))
    (hb : ∀ K M, b.hom.app (K ⊗ M) ≫ dB K M =
      dL j K M ≫ (b.hom.app K ⊗ₘ b.hom.app M)) (K M : C) :
    (b.symm ≪≫ eqToIso (congrArg L h.symm) ≪≫ a).hom.app (K ⊗ M) ≫ dA K M =
      dB K M ≫ ((b.symm ≪≫ eqToIso (congrArg L h.symm) ≪≫ a).hom.app K ⊗ₘ
        (b.symm ≪≫ eqToIso (congrArg L h.symm) ≪≫ a).hom.app M) := by
  subst j
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso_refl,
    Iso.refl_hom, Category.id_comp, Category.assoc]
  rw [ha, ← cancel_epi (b.hom.app (K ⊗ M)), Iso.hom_inv_id_app_assoc,
    ← Category.assoc, hb, Category.assoc, tensorHom_comp_tensorHom]
  simp only [Iso.hom_inv_id_app_assoc]

private theorem unit_of_oplax
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (e : F ⟶ G)
    (he : e.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F) :
    Functor.LaxMonoidal.ε F ≫ e.app (𝟙_ C) = Functor.LaxMonoidal.ε G := by
  rw [← cancel_mono (Functor.OplaxMonoidal.η G), Category.assoc, he,
    Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]

private theorem tensorπ_tensorHom
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R : C} [MonObj R] [IsCommMonObj R] {M N M' N' : Mod C R}
    (a : M ⟶ M') (b : N ⟶ N') :
    Mod.tensorObjπ M N ≫ (a ⊗ₘ b).hom =
      (a.hom ⊗ₘ b.hom) ≫ Mod.tensorObjπ M' N' := by
  rw [MonoidalCategory.tensorHom_def, Mod.comp_hom', Mod.tensorObjπ_whiskerRight_assoc,
    Mod.tensorObjπ_whiskerLeft, ← MonoidalCategory.tensorHom_def_assoc]

private theorem conjugate_tensor_only
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    [L₁.OplaxMonoidal] [L₂.OplaxMonoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
    [a₁.IsMonoidal] [a₂.IsMonoidal]
    (e : R₁ ⟶ R₂)
    (he : ∀ X Y, Functor.LaxMonoidal.μ R₁ X Y ≫ e.app (X ⊗ Y) =
      (e.app X ⊗ₘ e.app Y) ≫ Functor.LaxMonoidal.μ R₂ X Y) (X Y : C) :
    ((conjugateEquiv a₁ a₂).symm e).app (X ⊗ Y) ≫
        Functor.OplaxMonoidal.δ L₁ X Y =
      Functor.OplaxMonoidal.δ L₂ X Y ≫
        (((conjugateEquiv a₁ a₂).symm e).app X ⊗ₘ
          ((conjugateEquiv a₁ a₂).symm e).app Y) := by
  apply (a₂.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm, Category.assoc, ← e.naturality,
    Adjunction.unit_app_tensor_comp_map_δ_assoc, he,
    tensorHom_comp_tensorHom_assoc, unit_conjugateEquiv_symm a₁ a₂ e X,
    unit_conjugateEquiv_symm a₁ a₂ e Y, ← tensorHom_comp_tensorHom_assoc,
    Functor.LaxMonoidal.μ_natural, Adjunction.unit_app_tensor_comp_map_δ_assoc]

private theorem tensorEndomorphisms_identity
    {C : Type*} [Category C] [MonoidalCategory C] {X Y Z : C}
    (a : X ⟶ X) (b : Y ⟶ Y) (k : X ⊗ Y ⟶ Z)
    (ha : a = 𝟙 X) (hb : b = 𝟙 Y) : (a ⊗ₘ b) ≫ k = k := by
  rw [ha, hb, tensorHom_id, id_whiskerRight, Category.id_comp]

namespace AlgebraicGeometry.ProEtale.CondensedRing

section TensorPullbackHelpers
attribute [local irreducible] upperStarLowerStarAdjunction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The ordinary comparison sends the tensor of the two universal pullback sections to
its universal tensor section; on the regular module it is the coefficient map alpha.
These are equalities of sheaf maps, so include all local generators, rather than only
sections over schemes in the image of base change.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first). -/
def CondensedTensorNormalization (m : (upperStar Λ f).CoreMonoidal) : Prop :=
  (∀ M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y),
    (Mod.tensorObjπ M N) ≫ ((upperStarLowerStarAdjunction Λ f).unit.app (M ⊗ N)).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map ((m.μIso M N).inv.hom) =
      (((upperStarLowerStarAdjunction Λ f).unit.app M).hom ⊗ₘ
        ((upperStarLowerStarAdjunction Λ f).unit.app N).hom) ≫
      Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f)
        ((upperStar Λ f).obj M).X ((upperStar Λ f).obj N).X ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map
        (Mod.tensorObjπ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N))) ∧
  ((upperStarLowerStarAdjunction Λ f).unit.app (𝟙_ _)).hom ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map m.εIso.inv.hom =
    condensedPushforwardHom Λ f

section TensorNormalizationProofs
attribute [local instance 20000] traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour

private theorem module_unit_hom
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ((upperStarLowerStarAdjunction Λ f).unit.app M).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          (Mod.extendUnitHom (condensedPullbackHom Λ f)
            (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj M)) := by
  have h := upperStarLowerStarAdjunction_homEquiv_hom Λ f M _ (𝟙 _)
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id] at h
  erw [Category.comp_id] at h
  erw [Mod.id_hom', Category.comp_id] at h
  exact h

private theorem canonical_tensor_normalization :
    CondensedTensorNormalization Λ f
      (Functor.CoreMonoidal.ofOplaxMonoidal (upperStar Λ f)) := by
  constructor
  · intro M N
    change Mod.tensorObjπ M N ≫
        ((upperStarLowerStarAdjunction Λ f).unit.app (M ⊗ N)).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          (Functor.OplaxMonoidal.δ (upperStar Λ f) M N).hom = _
    let F := ProEtale.upperStar Ab.{u + 1} f
    let G := ProEtale.lowerStar Ab.{u + 1} f
    let E := Mod.extendScalars (condensedPullbackHom Λ f)
    let A := (F.mapMod (condensedRingObj Λ Y)).obj M
    let B := (F.mapMod (condensedRingObj Λ Y)).obj N
    let d := Functor.OplaxMonoidal.δ (F.mapMod (condensedRingObj Λ Y)) M N
    have hd : Functor.OplaxMonoidal.δ (upperStar Λ f) M N =
        E.map d ≫ Functor.OplaxMonoidal.δ E A B := rfl
    have hn := congrArg Mod.Hom.hom
      ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ f)).unit.naturality d)
    simp only [Functor.id_map, Functor.comp_map, Mod.comp_hom', Mod.comap_map_hom,
      extendRestrictAdjunction_condensedPullbackHom_unit_app_hom] at hn
    rw [module_unit_hom, module_unit_hom, module_unit_hom, hd, Mod.comp_hom']
    have ht := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.naturality
      (Mod.tensorObjπ M N)
    dsimp only [Functor.id_map, Functor.comp_map] at ht
    simp only [Category.assoc]
    rw [reassoc_of% ht]
    rw [← G.map_comp, ← G.map_comp]
    have he : F.map (Mod.tensorObjπ M N) ≫
        (Mod.extendUnitHom (condensedPullbackHom Λ f)
          ((F.mapMod (condensedRingObj Λ Y)).obj (M ⊗ N)) ≫
          ((E.map d).hom ≫ (Functor.OplaxMonoidal.δ E A B).hom)) =
      Functor.OplaxMonoidal.δ F M.X N.X ≫
        (Mod.extendUnitHom (condensedPullbackHom Λ f) A ⊗ₘ
          Mod.extendUnitHom (condensedPullbackHom Λ f) B) ≫
            Mod.tensorObjπ (E.obj A) (E.obj B) := by
      rw [← reassoc_of% hn]
      erw [reassoc_of% (map_tensor_inverse (ProEtale.upperStar Ab.{u + 1} f) M N),
        extension_tensor_inverse (condensedPullbackHom Λ f)
          (extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f) A B]
    rw [he, G.map_comp,
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit_app_tensor_comp_map_δ_assoc]
    rw [G.map_comp, ← Functor.LaxMonoidal.μ_natural_assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    rfl
  · change ((upperStarLowerStarAdjunction Λ f).unit.app (𝟙_ _)).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          (Functor.Monoidal.εIso (upperStar Λ f)).inv.hom = _
    simpa only [Adjunction.homEquiv_unit, Mod.comp_hom', lowerStar,
      Functor.comp_map, Mod.comap_map_hom, Functor.mapMod, Mod.homMk] using
      homEquiv_εIso_inv_hom Λ f

end TensorNormalizationProofs

/-- The specified ordinary strong monoidal structure, selected by its unique equations.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first). -/
def condensedTensorCore : (upperStar Λ f).CoreMonoidal :=
  Functor.CoreMonoidal.ofOplaxMonoidal (upperStar Λ f)

private theorem condensedTensorCore_normalization :
    CondensedTensorNormalization Λ f (condensedTensorCore Λ f) :=
  canonical_tensor_normalization Λ f

private theorem condensedUpperStarMonoidal_eq :
    condensedUpperStarMonoidal Λ f = monoidal_upperStar Λ f := rfl

attribute [local irreducible] condensedTensorCore condensedUpperStarMonoidal
private theorem ordinary_upperStar_braiding
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) :
    Functor.LaxMonoidal.μ (upperStar Λ f) M N ≫ (upperStar Λ f).map (β_ M N).hom =
      (β_ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N)).hom ≫
        Functor.LaxMonoidal.μ (upperStar Λ f) N M := by
  unfold condensedUpperStarMonoidal
  let := monoidal_upperStar Λ f
  let G := ProEtale.upperStar Ab.{u + 1} f
  let : (G.mapMod (condensedRingObj Λ Y)).LaxBraided :=
    { braided := mapMod_braided G }
  let := extend_braided (condensedPullbackHom Λ f)
  exact Functor.LaxBraided.braided (F := G.mapMod (condensedRingObj Λ Y) ⋙
    Mod.extendScalars (condensedPullbackHom Λ f)) M N

end TensorPullbackHelpers

attribute [local irreducible] Mod.monoidalCategoryStruct

section CompositionCoherence
attribute [local instance 20000] traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour
attribute [local irreducible] upperStar
  upperStarComp lowerStarComp
private theorem lower_mu_pi
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    letI := (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
    Mod.tensorObjπ ((lowerStar Λ f).obj M) ((lowerStar Λ f).obj N) ≫
      (Functor.LaxMonoidal.μ (lowerStar Λ f) M N).hom =
    Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) := by
  let := (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
  let a := upperStarLowerStarAdjunction Λ f
  let G := ProEtale.lowerStar Ab.{u + 1} f
  change Mod.tensorObjπ ((lowerStar Λ f).obj M) ((lowerStar Λ f).obj N) ≫
    (a.homEquiv _ _ (Functor.OplaxMonoidal.δ (upperStar Λ f)
      ((lowerStar Λ f).obj M) ((lowerStar Λ f).obj N) ≫
      (a.counit.app M ⊗ₘ a.counit.app N))).hom = _
  rw [Adjunction.homEquiv_unit]
  simp only [Mod.comp_hom', Functor.map_comp, lowerStar_map_hom]
  erw [reassoc_of% ((condensedTensorCore_normalization Λ f).1
    ((lowerStar Λ f).obj M) ((lowerStar Λ f).obj N))]
  erw [← Functor.map_comp]
  rw [MonoidalCategory.tensorHom_def (a.counit.app M) (a.counit.app N)]
  simp only [Mod.comp_hom']
  erw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft]
  rw [← MonoidalCategory.tensorHom_def_assoc]
  rw [G.map_comp]
  erw [← Functor.LaxMonoidal.μ_natural_assoc]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  have hM := congrArg Mod.Hom.hom (a.right_triangle_components M)
  have hN := congrArg Mod.Hom.hom (a.right_triangle_components N)
  simp only [Mod.comp_hom', lowerStar_map_hom, Mod.id_hom'] at hM hN
  exact tensorEndomorphisms_identity _ _ _ hM hN

attribute [local irreducible] Adjunction.rightAdjointLaxMonoidal

private theorem lower_comp_tensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    letI := (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
    letI := (upperStarLowerStarAdjunction Λ g).rightAdjointLaxMonoidal
    letI := (upperStarLowerStarAdjunction Λ (f ≫ g)).rightAdjointLaxMonoidal
    Functor.LaxMonoidal.μ (lowerStar Λ f ⋙ lowerStar Λ g) M N ≫
      (lowerStarComp Λ f g).hom.app (M ⊗ N) =
    ((lowerStarComp Λ f g).hom.app M ⊗ₘ (lowerStarComp Λ f g).hom.app N) ≫
      Functor.LaxMonoidal.μ (lowerStar Λ (f ≫ g)) M N := by
  let := (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
  let := (upperStarLowerStarAdjunction Λ g).rightAdjointLaxMonoidal
  let := (upperStarLowerStarAdjunction Λ (f ≫ g)).rightAdjointLaxMonoidal
  apply Mod.hom_ext
  apply (cancel_epi (Mod.tensorObjπ
    ((lowerStar Λ f ⋙ lowerStar Λ g).obj M)
    ((lowerStar Λ f ⋙ lowerStar Λ g).obj N))).1
  simp only [Functor.LaxMonoidal.comp_μ, Mod.comp_hom', lowerStar_map_hom,
    lowerStarComp_hom_app_hom, Functor.comp_obj, Category.assoc]
  erw [reassoc_of% (lower_mu_pi Λ g ((lowerStar Λ f).obj M)
    ((lowerStar Λ f).obj N))]
  erw [← Functor.map_comp_assoc, lower_mu_pi Λ f M N]
  conv_rhs =>
    erw [reassoc_of% (tensorπ_tensorHom ((lowerStarComp Λ f g).hom.app M)
      ((lowerStarComp Λ f g).hom.app N))]
  erw [lower_mu_pi Λ (f ≫ g) M N]
  simp only [lowerStarComp_hom_app_hom, Functor.map_comp, Category.assoc]
  erw [(ProEtale.lowerStarComp Ab.{u + 1} f g).hom.naturality
    (Mod.tensorObjπ M N)]
  have ht := NatTrans.IsMonoidal.tensor_assoc
    (τ := (ProEtale.lowerStarComp Ab.{u + 1} f g).hom) M.X N.X
    ((ProEtale.lowerStar Ab.{u + 1} (f ≫ g)).map (Mod.tensorObjπ M N))
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj, Category.assoc] at ht
  exact ht

private theorem upper_comp_tensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    Functor.LaxMonoidal.μ (upperStar Λ (f ≫ g)) M N ≫
      (upperStarComp Λ f g).hom.app (M ⊗ N) =
    ((upperStarComp Λ f g).hom.app M ⊗ₘ (upperStarComp Λ f g).hom.app N) ≫
      Functor.LaxMonoidal.μ (upperStar Λ g ⋙ upperStar Λ f) M N := by
  let := (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
  let := (upperStarLowerStarAdjunction Λ g).rightAdjointLaxMonoidal
  let := (upperStarLowerStarAdjunction Λ (f ≫ g)).rightAdjointLaxMonoidal
  have hi : (conjugateEquiv
      ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
      (upperStarLowerStarAdjunction Λ (f ≫ g))).symm
        (lowerStarComp Λ f g).hom = (upperStarComp Λ f g).hom := by
    apply (conjugateEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact (congrArg Iso.hom (conjugateIsoEquiv_upperStarComp Λ f g)).symm
  have ht := conjugate_tensor_only
    ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
    (upperStarLowerStarAdjunction Λ (f ≫ g)) (lowerStarComp Λ f g).hom
    (lower_comp_tensor Λ f g) M N
  rw [hi] at ht
  rw [← cancel_mono (Functor.OplaxMonoidal.δ (upperStar Λ g ⋙ upperStar Λ f) M N),
    Category.assoc, ht, Functor.Monoidal.μ_δ_assoc, Category.assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

private theorem upper_comp_monoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp Λ f g).hom := by
  constructor
  · unfold condensedUpperStarMonoidal
    let := monoidal_upperStar Λ f
    let := monoidal_upperStar Λ g
    let := monoidal_upperStar Λ (f ≫ g)
    refine unit_of_oplax (upperStarComp Λ f g).hom ?_
    simpa only [Functor.OplaxMonoidal.comp_η, Functor.Monoidal.εIso_inv] using
      upperStarComp_hom_app_unit Λ f g
  · exact upper_comp_tensor Λ f g
end CompositionCoherence

attribute [local irreducible] condensedTensorCore condensedUpperStarMonoidal

/-- The adjunction transpose defining projection, expressed over abstract categories.
Source: Stacks 0B56 (blueprint: lem-sfb-trace-base-change-first). -/
def traceProjectionFromComparison
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {P : D ⥤ C} (adj : F ⊣ P)
    (δ : ∀ K M : C, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M) (K : C) (N : D) :
    K ⊗ P.obj N ⟶ P.obj (F.obj K ⊗ N) :=
  adj.homEquiv (K ⊗ P.obj N) (F.obj K ⊗ N)
    (δ K (P.obj N) ≫ (𝟙 (F.obj K) ⊗ₘ adj.counit.app N))

/-- A square mate, with the canonical adjunctions supplied as data.
Source: Stacks 07A7 (blueprint: lem-sfb-trace-base-change-first). -/
def traceAbstractMate
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    {F : C ⥤ D} {P : D ⥤ C} {U₁ U₂ : D ⥤ V} {Q : V ⥤ D}
    (a : F ⊣ P) (b : U₂ ⊣ Q) (s : F ⋙ U₂ ≅ F ⋙ U₁) :
    P ⋙ F ⟶ U₁ ⋙ Q :=
  (mateEquiv a b (TwoSquare.mk _ _ _ _ s.hom))

section Symmetry
variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalCategory D] [SymmetricCategory D]
  {F : C ⥤ D} {P : D ⥤ C} [F.Braided] (a : F ⊣ P)

private theorem fixed_projection_eq (K : C) (N : D) :
    a.homEquiv _ _ (Functor.OplaxMonoidal.δ F K (P.obj N) ≫
      (𝟙 (F.obj K) ⊗ₘ a.counit.app N)) = a.leftCoefficientProjectionMap K N := by
  apply (a.homEquiv _ _).symm.injective
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.id_obj] using
    ((a.leftCoefficientProjectionMap_coherence).2.1 K N).symm

end Symmetry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
private theorem conjugate_transpose
    {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} {R S : B ⥤ A} (adj : F ⊣ R) (adj' : G ⊣ S)
    (theta : G ≅ F) {T : A} {Z : B} (f : T ⟶ S.obj Z) :
    (adj.homEquiv _ _).symm
        (f ≫ (conjugateIsoEquiv adj adj' theta).inv.app Z) =
      theta.inv.app T ≫ (adj'.homEquiv _ _).symm f := by
  change F.map (f ≫ (conjugateEquiv adj' adj theta.inv).app Z) ≫
      adj.counit.app Z = _
  rw [Functor.map_comp, Category.assoc, conjugateEquiv_counit]
  rw [← Category.assoc, theta.inv.naturality f]
  simp only [Category.assoc, Adjunction.homEquiv_counit]

set_option backward.isDefEq.respectTransparency false in
/-- Canonical tensor comparisons for three fixed functors, with their tensor structures
stored once. This bundle prevents repeated proof abstraction inside concrete derived tensors.
Source: Stacks 07A4; derived-completeness implementation notes
(blueprint: lem-sfb-trace-base-change-first). -/
structure TraceComparisonData
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    (F : C ⥤ D) (U₁ U₂ : D ⥤ V) where
  /-- The tensor structure in the source category. -/
  [monoidalC : MonoidalCategory C]
  /-- The tensor structure in the middle category. -/
  [monoidalD : MonoidalCategory D]
  /-- The tensor structure in the final category. -/
  [monoidalV : MonoidalCategory V]
  /-- The specified unit comparison. -/
  unitIso : F.obj (𝟙_ C) ≅ 𝟙_ D
  /-- The tensor comparison for the first functor. -/
  tensorF : ∀ K M : C, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M
  /-- The tensor comparison for the first branch. -/
  tensorOne : ∀ K M : D, U₁.obj (K ⊗ M) ⟶ U₁.obj K ⊗ U₁.obj M
  /-- The tensor comparison for the second branch. -/
  tensorTwo : ∀ K M : D, U₂.obj (K ⊗ M) ⟶ U₂.obj K ⊗ U₂.obj M
  /-- The specified symmetry in the middle category. -/
  symmetryD : ∀ K M : D, K ⊗ M ≅ M ⊗ K
  /-- The specified symmetry in the final category. -/
  symmetryV : ∀ K M : V, K ⊗ M ≅ M ⊗ K

/-- Tensor compatibility expressed using the stored canonical structures. -/
private def traceDataSquare
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (T : TraceComparisonData F U₁ U₂)
    (s : F ⋙ U₂ ≅ F ⋙ U₁) : Prop :=
  letI := T.monoidalC
  letI := T.monoidalD
  letI := T.monoidalV
  ∀ K M : C,
    s.hom.app (K ⊗ M) ≫ U₁.map (T.tensorF K M) ≫
        T.tensorOne (F.obj K) (F.obj M) =
      U₂.map (T.tensorF K M) ≫ T.tensorTwo (F.obj K) (F.obj M) ≫
        (s.hom.app K ⊗ₘ s.hom.app M)


section AbstractTrace
variable {C D V : Type*} [Category C] [Category D] [Category V]
  [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalCategory D] [SymmetricCategory D]
  [MonoidalCategory V] [SymmetricCategory V]
  (LC : ObjectProperty C) (LD : ObjectProperty D) (LV : ObjectProperty V)
  (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q₁ Q₂ : V ⥤ D)
  [F.Braided] [U₁.Braided] [U₂.Braided]
  (a : F ⊣ P) (a₁ : U₁ ⊣ Q₁) (a₂ : U₂ ⊣ Q₂)
  (s : F ⋙ U₂ ≅ F ⋙ U₁) (TY : C)
  (hs : ∀ K L : C, s.hom.app (K ⊗ L) ≫
    U₁.map (Functor.OplaxMonoidal.δ F K L) ≫
      Functor.OplaxMonoidal.δ U₁ (F.obj K) (F.obj L) =
    U₂.map (Functor.OplaxMonoidal.δ F K L) ≫
      Functor.OplaxMonoidal.δ U₂ (F.obj K) (F.obj L) ≫
        (s.hom.app K ⊗ₘ s.hom.app L))

end AbstractTrace


section DerivedTraceAssembly
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [SymmetricCategory D]
  [MonoidalPreadditive D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  {V : Type u₃} [Category.{u + 1} V] [Abelian V]
  [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalPreadditive V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
  (LC : ObjectProperty (DerivedCategory C)) (LD : ObjectProperty (DerivedCategory D))
  (LV : ObjectProperty (DerivedCategory V))
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.IsLeftAdjoint] [F.PreservesFlat] [F.Monoidal]
  (U₁ U₂ : D ⥤ V)
  [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [U₁.IsLeftAdjoint] [U₁.PreservesFlat] [U₁.Monoidal]
  [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [U₂.IsLeftAdjoint] [U₂.PreservesFlat] [U₂.Monoidal]
  (P : DerivedCategory D ⥤ DerivedCategory C)
  (Q₁ Q₂ : DerivedCategory V ⥤ DerivedCategory D)
  (a : F.leftDerivedFunctor ⊣ P)
  (a₁ : U₁.leftDerivedFunctor ⊣ Q₁) (a₂ : U₂.leftDerivedFunctor ⊣ Q₂)
  (s : F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor ≅
    F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor)
  (TY : DerivedCategory C)

/-- The existing total-derived tensor, degree-zero unit and Koszul comparisons,
constructed while the three abelian categories are abstract. No data is chosen.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def derivedTraceComparisonData :
    TraceComparisonData F.leftDerivedFunctor U₁.leftDerivedFunctor U₂.leftDerivedFunctor where
  unitIso := F.traceDegreeZeroUnitIso
  tensorF K M := (F.leftDerivedTensorComparison.app K).app M
  tensorOne K M := (U₁.leftDerivedTensorComparison.app K).app M
  tensorTwo K M := (U₂.leftDerivedTensorComparison.app K).app M
  symmetryD := CategoryTheory.traceCanonicalDerivedBraiding
  symmetryV := CategoryTheory.traceCanonicalDerivedBraiding

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Derive the tensor compatibility of a square before specializing its categories. -/
private theorem derived_square_assembly
    {I : Type*} (L : I → C ⥤ V)
    [∀ i, (L i).Additive] [∀ i, PreservesFiniteLimits (L i)]
    [∀ i, PreservesFiniteColimits (L i)] [∀ i, (L i).IsLeftAdjoint]
    [∀ i, (L i).PreservesFlat] [∀ i, (L i).Monoidal]
    {i j : I} (w : i = j) (e₁ : L i ≅ F ⋙ U₁) (e₂ : L j ≅ F ⋙ U₂)
    [NatTrans.IsMonoidal e₁.hom] [NatTrans.IsMonoidal e₂.hom] :
    traceDataSquare (derivedTraceComparisonData F U₁ U₂)
      (((L j).leftDerivedFunctorNatIso e₂ ≪≫ F.leftDerivedFunctorCompIso U₂).symm ≪≫
        eqToIso (congrArg (fun h ↦ (L h).leftDerivedFunctor) w.symm) ≪≫
          ((L i).leftDerivedFunctorNatIso e₁ ≪≫ F.leftDerivedFunctorCompIso U₁)) := by
  let a : (L i).leftDerivedFunctor ≅ F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor :=
    (L i).leftDerivedFunctorNatIso e₁ ≪≫ F.leftDerivedFunctorCompIso U₁
  let b : (L j).leftDerivedFunctor ≅ F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor :=
    (L j).leftDerivedFunctorNatIso e₂ ≪≫ F.leftDerivedFunctorCompIso U₂
  let e : F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor ≅
      F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor :=
    b.symm ≪≫ eqToIso (congrArg (fun h ↦ (L h).leftDerivedFunctor) w.symm) ≪≫ a
  change ∀ K M : DerivedCategory C,
    e.hom.app (K ⊗ M) ≫
        U₁.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app K).app M) ≫
        (U₁.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj K)).app
          (F.leftDerivedFunctor.obj M) =
      U₂.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app K).app M) ≫
        (U₂.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj K)).app
          (F.leftDerivedFunctor.obj M) ≫ (e.hom.app K ⊗ₘ e.hom.app M)
  intro K M
  simpa only [Category.assoc] using
    (tensor_square_family (C := DerivedCategory C) (V := DerivedCategory V)
      (A := F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor)
      (B := F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor) (i := i) (j := j)
      (fun h ↦ (L h).leftDerivedFunctor)
      (fun h A B ↦ ((L h).leftDerivedTensorComparison.app A).app B)
      (fun A B ↦ U₁.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app A).app B) ≫
        (U₁.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj A)).app
          (F.leftDerivedFunctor.obj B))
      (fun A B ↦ U₂.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app A).app B) ≫
        (U₂.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj A)).app
          (F.leftDerivedFunctor.obj B))
      w a b
      (fun A B ↦ Functor.derived_comp_explicit F U₁ (L i) e₁ A B)
      (fun A B ↦ Functor.derived_comp_explicit F U₂ (L j) e₂ A B) K M)

end DerivedTraceAssembly

section ModuleTraceAssembly
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [SymmetricCategory D]
  [MonoidalPreadditive D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  {V : Type u₃} [Category.{u + 1} V] [Abelian V]
  [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalPreadditive V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
  (RC : C) [MonObj RC] [IsCommMonObj RC]
  (RD : D) [MonObj RD] [IsCommMonObj RD]
  (RV : V) [MonObj RV] [IsCommMonObj RV]
  (LC : ObjectProperty (DerivedCategory (Mod C RC)))
  (LD : ObjectProperty (DerivedCategory (Mod D RD)))
  (LV : ObjectProperty (DerivedCategory (Mod V RV)))
  (F : Mod C RC ⥤ Mod D RD) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.IsLeftAdjoint] [F.PreservesFlat] [F.Monoidal]
  (U₁ U₂ : Mod D RD ⥤ Mod V RV)
  [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [U₁.IsLeftAdjoint] [U₁.PreservesFlat] [U₁.Monoidal]
  [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [U₂.IsLeftAdjoint] [U₂.PreservesFlat] [U₂.Monoidal]
  (P : DerivedCategory (Mod D RD) ⥤ DerivedCategory (Mod C RC))
  (Q₁ Q₂ : DerivedCategory (Mod V RV) ⥤ DerivedCategory (Mod D RD))
  (a : F.leftDerivedFunctor ⊣ P)
  (a₁ : U₁.leftDerivedFunctor ⊣ Q₁) (a₂ : U₂.leftDerivedFunctor ⊣ Q₂)
  (s : F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor ≅
    F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor)
  (TY : DerivedCategory (Mod C RC))

/-- The canonical derived comparisons for internal modules, with ambient categories
still abstract. Its fields are exactly those of `derivedTraceComparisonData`.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def moduleTraceComparisonData :
    TraceComparisonData F.leftDerivedFunctor U₁.leftDerivedFunctor U₂.leftDerivedFunctor :=
  derivedTraceComparisonData F U₁ U₂

end ModuleTraceAssembly

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The recorded ambient unbounded internal-module derived category.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
abbrev TraceD (Z : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))

/-- Alias for the total left derived functor of the full module inverse image.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
def tracePull {Z B : Scheme.{u}} (h : Z ⟶ B) : TraceD Λ B ⥤ TraceD Λ Z :=
  moduleObjectDerivedPullback Λ h

/-- Alias for the total right derived functor of the full module direct image.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
def tracePush {Z B : Scheme.{u}} (h : Z ⟶ B) : TraceD Λ Z ⥤ TraceD Λ B :=
  moduleObjectDerivedPushforward Λ h

/-- The existing canonical adjunction, with its functors named explicitly.
Source: blueprint derived module adjunction (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def traceAdjunction {Z B : Scheme.{u}} (h : Z ⟶ B) :
    tracePull Λ h ⊣ tracePush Λ h :=
  derivedUpperStarLowerStarAdjunction Λ h

variable {X Y W : Scheme.{u}} (f : X ⟶ Y) (p q : W ⟶ X)

/-- The canonical pullback composition with named functor endpoints.
Source: Stacks 0D6D (blueprint: lem-sfb-trace-base-change-first). -/
def tracePullComp {Z B C : Scheme.{u}} (a : Z ⟶ B) (b : B ⟶ C) :
    tracePull Λ (a ≫ b) ≅ tracePull Λ b ⋙ tracePull Λ a :=
  leftDerivedUpperStarComp Λ a b

/-- The canonical inverse-image square comparison, from the recorded composition maps.
Source: Stacks 07A7 (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def tracePullSquare (w : p ≫ f = q ≫ f) :
    tracePull Λ f ⋙ tracePull Λ q ≅ tracePull Λ f ⋙ tracePull Λ p :=
  (tracePullComp Λ q f).symm ≪≫
    eqToIso (congrArg (fun h : W ⟶ Y => tracePull Λ h) w.symm) ≪≫
      tracePullComp Λ p f

/-- The recorded canonical comparisons for the three pullbacks, stored in one bundle.
Its fields are the existing derived tensor, degree-zero unit and Koszul symmetry maps.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def traceNativeComparisonData :
    TraceComparisonData (tracePull Λ f) (tracePull Λ p) (tracePull Λ q) :=
  moduleTraceComparisonData
    (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
    (upperStar Λ f) (upperStar Λ p) (upperStar Λ q)

section SquareCoherence
attribute [local instance 20000] traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour
attribute [local irreducible] upperStar lowerStar
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
private theorem trace_square_tensor (w : p ≫ f = q ≫ f) :
    traceDataSquare (traceNativeComparisonData Λ f p q) (tracePullSquare Λ f p q w) := by
  let := upper_comp_monoidal Λ p f
  let := upper_comp_monoidal Λ q f
  unfold tracePullSquare
  exact derived_square_assembly
    (upperStar Λ f) (upperStar Λ p) (upperStar Λ q)
    (fun h : W ⟶ Y ↦ upperStar Λ h) w
    (upperStarComp Λ p f) (upperStarComp Λ q f)
end SquareCoherence

/-- The base twist R_Y(1)[2], its recorded integral line placed in degree zero.
Source: definition-tate-twists (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def traceTate (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Z : Scheme.{u}) : TraceD (Profinite.padicIntegersRingObj ℓ E.1) Z :=
  ((DerivedCategory.singleFunctor _ 0).obj (spIntegralTwist Z ℓ E)) ⟦(2 : ℤ)⟧

section ConcreteTrace
attribute [local instance 20000] traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour
attribute [local irreducible] upperStar lowerStar
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
end ConcreteTrace

end AlgebraicGeometry.ProEtale.CondensedRing
