/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses
import all WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
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
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! # The ordinary scalar tensor square

The internal scalar coequalizer and the tensor coequalizer reduce the square
to normalized balanced generators. No complex or derived-category assertion is used.
(blueprint: lem-sfb-coefficient-scalar-tensor-ordinary)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  internalScalarExtension
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor
  Localization.Monoidal.tensorBifunctor
  ModuleRingedComparison.ordinaryTensorComparison coefficientSectionScalarPure
  Mod.extendRestrictAdjunction

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

private theorem scalar_tensor_ext (Z : Scheme.{u})
    (M N : ModuleRingedComparison.internalModules R Z)
    (W : ModuleRingedComparison.modules S Z)
    (f g : (ModuleRingedComparison.equivalence S Z).functor.obj
      ((Mod.extendScalars (coefficientMap a Z)).obj (M ⊗ N)) ⟶ W)
    (h : ∀ (V : Z.ProEtᵒᵖ) (s : (ModuleRingedComparison.ring S Z).obj.obj V)
      (x : M.X.obj.obj V) (y : N.X.obj.obj V),
      f.val.app V (InternalAbelianSheafModule.internalScalarGenerator
        (Scheme.ProEt.topology Z) (coefficientMap a Z) (M ⊗ N) V s
          (ModuleRingedComparison.internalPureTensor R Z M N V x y)) =
      g.val.app V (InternalAbelianSheafModule.internalScalarGenerator
        (Scheme.ProEt.topology Z) (coefficientMap a Z) (M ⊗ N) V s
          (ModuleRingedComparison.internalPureTensor R Z M N V x y))) : f = g := by
  let J := Scheme.ProEt.topology Z
  let ES := sheafToPresheaf J Ab.{u + 1}
  apply (SheafOfModules.toSheaf _).map_injective
  apply (cancel_epi (Mod.extendπ (coefficientMap a Z) (M ⊗ N))).mp
  apply (cancel_epi ((condensedRingObj S Z) ◁ Mod.tensorObjπ M N)).mp
  apply Sheaf.tensor_hom_ext
  apply ((J.W.whiskerLeft_mem (condensedRingObj S Z).obj _
    (InternalAbelianSheafModule.comparison_sheafTensor_mem J M.X N.X))
    (SheafOfModules.toSheaf _ |>.obj W).obj
    (SheafOfModules.toSheaf _ |>.obj W).property).injective
  simp only [Functor.map_comp]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.LaxMonoidal.μ_natural_right_assoc]
  ext V t
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul s t =>
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul x y => exact h V s x y

private theorem internal_delta_unit (Z : Scheme.{u})
    (M N : ModuleRingedComparison.internalModules R Z)
    (V : Z.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V) :
    let := internalScalarMonoidal a Z
    (((ModuleRingedComparison.equivalence S Z).functor.map
      (Functor.OplaxMonoidal.δ (Mod.extendScalars (coefficientMap a Z)) M N)).val.app V)
      ((Mod.extendUnitHom (coefficientMap a Z) (M ⊗ N)).hom.app V
        (ModuleRingedComparison.internalPureTensor R Z M N V x y)) =
    ModuleRingedComparison.internalPureTensor S Z _ _ V
      ((Mod.extendUnitHom (coefficientMap a Z) M).hom.app V x)
      ((Mod.extendUnitHom (coefficientMap a Z) N).hom.app V y) := by
  let := internalScalarMonoidal a Z
  have hn := (internalScalarMonoidalNormalized_existsUnique a Z).exists.choose_spec M N
  let F := sheafToPresheaf (Scheme.ProEt.topology Z) Ab.{u + 1}
  have hh := congrArg (fun k ↦ Functor.LaxMonoidal.μ F M.X N.X ≫ F.map k) hn
  simp only [Functor.map_comp] at hh
  rw [← Functor.LaxMonoidal.μ_natural_assoc] at hh
  exact congrArg (fun k ↦ (k.app V) (x ⊗ₜ[ℤ] y)) hh

open PresheafOfModules in
omit [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))] in
private theorem coefficient_pure_eq (Z : Scheme.{u})
    (b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z))
    (M : ModuleRingedComparison.modules R Z) (V : Z.ProEtᵒᵖ)
    (s : (ModuleRingedComparison.ring S Z).obj.obj V) (x : M.val.obj V) :
    coefficientSectionScalarPure a Z b M V s x =
      (eqToHom (b.extension_obj M).symm).val.app V
        (SheafOfModules.scalarExtensionConstraintTmul
          (coefficientSectionScalarMap a Z) M V x s) := by
  unfold coefficientSectionScalarPure
  apply congrArg ((eqToHom (b.extension_obj M).symm).val.app V)
  symm
  unfold SheafOfModules.scalarExtensionConstraintTmul
  let RS : Sheaf (Scheme.ProEt.topology Z) RingCat.{u + 1} :=
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (ModuleRingedComparison.ring S Z)
  have hs := toPresheaf_map_sheafificationAdjunction_unit_app.{u + 1, u, u + 1, u + 1}
    (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := RS) (𝟙 RS.obj)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (coefficientSectionScalarMap a Z) M)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hs V) _

private theorem coefficient_pure_natural (Z : Scheme.{u})
    (b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z))
    {M N : ModuleRingedComparison.modules R Z} (f : M ⟶ N) (V : Z.ProEtᵒᵖ)
    (s : (ModuleRingedComparison.ring S Z).obj.obj V) (x : M.val.obj V) :
    (b.extension.map f).val.app V (coefficientSectionScalarPure a Z b M V s x) =
      coefficientSectionScalarPure a Z b N V s (f.val.app V x) := by
  rw [coefficient_pure_eq, coefficient_pure_eq, b.extension_map]
  have he := congrArg (fun k ↦ k.val.app V
    (SheafOfModules.scalarExtensionConstraintTmul (coefficientSectionScalarMap a Z) M V x s))
      ((eqToIso (b.extension_obj M)).inv_hom_id)
  change (eqToHom (b.extension_obj M)).val.app V
    ((eqToHom (b.extension_obj M).symm).val.app V _) = _ at he
  change (eqToHom (b.extension_obj N).symm).val.app V
    ((SheafOfModules.changeOfRingsHom (coefficientSectionScalarMap a Z) M f).val.app V
      ((eqToHom (b.extension_obj M)).val.app V
        ((eqToHom (b.extension_obj M).symm).val.app V _))) = _
  rw [he]
  change (eqToHom (b.extension_obj N).symm).val.app V
    ((SheafOfModules.changeOfRingsHom (coefficientSectionScalarMap a Z) M f).val.app V
      (SheafOfModules.scalarExtensionConstraintTmul (coefficientSectionScalarMap a Z) M V x s))
    = _
  exact congrArg ((eqToHom (b.extension_obj N).symm).val.app V)
    (SheafOfModules.extension_map_tmul (coefficientSectionScalarMap a Z) f V x s)

private theorem coefficient_pure_smul_unit (Z : Scheme.{u})
    (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    (h : CoefficientScalarTensorRepresentativeHypotheses a Z d)
    (M : ModuleRingedComparison.internalModules R Z) (V : Z.ProEtᵒᵖ)
    (s : (ModuleRingedComparison.ring S Z).obj.obj V) (x : M.X.obj.obj V) :
    s • (d.o.hom.app M).val.app V
        ((Mod.extendUnitHom (coefficientMap a Z) M).hom.app V x) =
      coefficientSectionScalarPure a Z d.b
        ((ModuleRingedComparison.equivalence R Z).functor.obj M) V s x := by
  have hh := h.hgenerator M V s x
  simp only [InternalAbelianSheafModule.internalScalarGenerator_eq_smul,
    Mod.extendRestrictAdjunction_unit_app_hom, map_smul] at hh
  exact hh

/-- The ordinary scalar tensor square under the section equivalence.
Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL.
Precompose with the scalar coequalizer and the internal tensor coequalizer.
On a generator s tensor (x tensor y), scalar linearity reduces the internal
normalization to its scalar-unit equation. Apply the two supplied generator
formulas and naturality of pure tensor pairing. The maps agree on generators,
so sheafification and the two coequalizer universal properties give equality.
(blueprint: lem-sfb-coefficient-scalar-tensor-ordinary). -/
theorem coefficientScalarTensor_ordinary (Z : Scheme.{u})
    (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    (h : CoefficientScalarTensorRepresentativeHypotheses a Z d)
    (M N : ModuleRingedComparison.internalModules R Z) :
    let := internalScalarMonoidal a Z
    (ModuleRingedComparison.equivalence S Z).functor.map
        (Functor.OplaxMonoidal.δ (Mod.extendScalars (coefficientMap a Z)) M N) ≫
      (ModuleRingedComparison.ordinaryTensorComparison S Z _ _).hom ≫
      (d.o.hom.app M ⊗ₘ d.o.hom.app N) =
    d.o.hom.app (M ⊗ N) ≫
      d.b.extension.map (ModuleRingedComparison.ordinaryTensorComparison R Z M N).hom ≫
      d.m.toOplaxMonoidal.δ
        ((ModuleRingedComparison.equivalence R Z).functor.obj M)
        ((ModuleRingedComparison.equivalence R Z).functor.obj N) := by
  let := internalScalarMonoidal a Z
  apply scalar_tensor_ext a Z M N
  intro V s x y
  let A := coefficientMap a Z
  let F := Mod.extendScalars A
  let ER := (ModuleRingedComparison.equivalence R Z).functor
  let ES := (ModuleRingedComparison.equivalence S Z).functor
  let δ := Functor.OplaxMonoidal.δ F M N
  let eR := ModuleRingedComparison.ordinaryTensorComparison R Z M N
  let eS := ModuleRingedComparison.ordinaryTensorComparison S Z (F.obj M) (F.obj N)
  -- Both sides are linear, so compare them on the scalar-unit generators.
  simp only [InternalAbelianSheafModule.internalScalarGenerator_eq_smul,
    map_smul, Mod.extendRestrictAdjunction_unit_app_hom]
  change s • (d.o.hom.app M ⊗ₘ d.o.hom.app N).val.app V
      (eS.hom.val.app V ((ES.map δ).val.app V
        ((Mod.extendUnitHom A (M ⊗ N)).hom.app V
          (ModuleRingedComparison.internalPureTensor R Z M N V x y)))) =
    s • (d.m.toOplaxMonoidal.δ (ER.obj M) (ER.obj N)).val.app V
      ((d.b.extension.map eR.hom).val.app V
        ((d.o.hom.app (M ⊗ N)).val.app V
          ((Mod.extendUnitHom A (M ⊗ N)).hom.app V
            (ModuleRingedComparison.internalPureTensor R Z M N V x y))))
  apply congrArg (fun z ↦ s • z)
  have hu (P : ModuleRingedComparison.internalModules R Z) (z : P.X.obj.obj V) :
      (d.o.hom.app P).val.app V ((Mod.extendUnitHom A P).hom.app V z) =
        coefficientSectionScalarPure a Z d.b (ER.obj P) V 1 z := by
    simpa only [one_smul] using coefficient_pure_smul_unit a Z d h P V
      (1 : (ModuleRingedComparison.ring S Z).obj.obj V) z
  let ux := (Mod.extendUnitHom A M).hom.app V x
  let uy := (Mod.extendUnitHom A N).hom.app V y
  let O := (d.o.hom.app M ⊗ₘ d.o.hom.app N).val.app V
  trans O (eS.hom.val.app V
    (ModuleRingedComparison.internalPureTensor S Z (F.obj M) (F.obj N) V ux uy))
  · exact congrArg (fun z ↦ O (eS.hom.val.app V z)) (internal_delta_unit a Z M N V x y)
  trans O (ModuleRingedComparison.sectionPureTensor S Z (ES.obj (F.obj M))
    (ES.obj (F.obj N)) V ux uy)
  · exact congrArg O (ModuleRingedComparison.pullTensor_tensorComparison_apply S Z
      (F.obj M) (F.obj N) V ux uy)
  trans ModuleRingedComparison.sectionPureTensor S Z
    (d.b.extension.obj (ER.obj M)) (d.b.extension.obj (ER.obj N)) V
    ((d.o.hom.app M).val.app V ux) ((d.o.hom.app N).val.app V uy)
  · exact ModuleRingedComparison.pullTensor_sectionTensor_natural S Z
      (d.o.hom.app M) (d.o.hom.app N) V ux uy
  trans ModuleRingedComparison.sectionPureTensor S Z
    (d.b.extension.obj (ER.obj M)) (d.b.extension.obj (ER.obj N)) V
    (coefficientSectionScalarPure a Z d.b (ER.obj M) V 1 x)
    (coefficientSectionScalarPure a Z d.b (ER.obj N) V 1 y)
  · exact congrArg₂ (ModuleRingedComparison.sectionPureTensor S Z
      (d.b.extension.obj (ER.obj M)) (d.b.extension.obj (ER.obj N)) V) (hu M x) (hu N y)
  symm
  let D := (d.m.toOplaxMonoidal.δ (ER.obj M) (ER.obj N)).val.app V
  trans D ((d.b.extension.map eR.hom).val.app V
    (coefficientSectionScalarPure a Z d.b (ER.obj (M ⊗ N)) V 1
      (ModuleRingedComparison.internalPureTensor R Z M N V x y)))
  · exact congrArg (fun z ↦ D ((d.b.extension.map eR.hom).val.app V z))
      (hu (M ⊗ N) (ModuleRingedComparison.internalPureTensor R Z M N V x y))
  trans D (coefficientSectionScalarPure a Z d.b (ER.obj M ⊗ ER.obj N) V 1
    (eR.hom.val.app V (ModuleRingedComparison.internalPureTensor R Z M N V x y)))
  · exact congrArg D (coefficient_pure_natural a Z d.b eR.hom V 1
      (ModuleRingedComparison.internalPureTensor R Z M N V x y))
  trans D (coefficientSectionScalarPure a Z d.b (ER.obj M ⊗ ER.obj N) V 1
    (ModuleRingedComparison.sectionPureTensor R Z (ER.obj M) (ER.obj N) V x y))
  · exact congrArg (fun z ↦ D
      (coefficientSectionScalarPure a Z d.b (ER.obj M ⊗ ER.obj N) V 1 z))
      (ModuleRingedComparison.pullTensor_tensorComparison_apply R Z M N V x y)
  exact h.hmonoidal (ER.obj M) (ER.obj N) V 1 x y

end AlgebraicGeometry.ProEtale.CondensedRing
