/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension

/-! # Constant finite free presentations after scalar extension

Source: Stacks Project, Modules on Sites, Tags 03EI, 03DA, 03ER(3), Section 03EK;
blueprint main-20261015, ctf-equals-bc, Local models
(blueprint: lem-sfb-constant-finite-free-presentation-extension).
-/

@[expose] public noncomputable section
-- This module only keeps private proof helpers.
set_option linter.privateModule false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ConstantFiniteFreePresentationExtension

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R]

variable (B : Sheaf J CommRingCat.{max u v})
  (σ : (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R) ⟶ B)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev homCommRing :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev homRing :=
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
    (homCommRing J R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def homRingUnit :
    (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ (homRing J R).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)) ≫
    (constantModuleHomRingIso J R).hom.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def homUnitLinear (M : ModuleCat.{max u v} R) :
    (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J R)).obj
        ((constantModuleHomFunctor J R).obj M).val :=
  PresheafOfModules.homMk (constantModuleHomUnit J R M) (fun U r x ↦ by
    have hi := congrArg
      (fun f ↦ f.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U r))
      (constantModuleHomRingIso J R).hom_inv_id
    change (constantModuleHomRingIso J R).inv.hom.app U
      ((constantModuleHomRingIso J R).hom.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U r)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U r at hi
    change (constantModuleHomUnit J R M).app U (r • x) =
      (constantModuleHomRingIso J R).inv.hom.app U
        ((constantModuleHomRingIso J R).hom.hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U r)) •
        (show ((siteConstantModuleFunctorGeneral J R).obj M).val.obj U from
          (constantModuleHomUnit J R M).app U x)
    rw [hi]
    exact (((PresheafOfModules.sheafificationAdjunction
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).unit.app
        ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app U).hom.map_smul r x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private local instance unitLinear_surjective (M : ModuleCat.{max u v} R) :
    PresheafOfModules.IsLocallySurjective J (homUnitLinear J R M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private local instance unitLinear_injective (M : ModuleCat.{max u v} R) :
    PresheafOfModules.IsLocallyInjective J (homUnitLinear J R M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private local instance ringUnit_surjective : Presheaf.IsLocallySurjective J (homRingUnit J R) := by
  unfold homRingUnit
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def constantLift (M : ModuleCat.{max u v} R)
    (N : SheafOfModules.{max u v} (homRing J R))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J R)).obj N.val) :
    (constantModuleHomFunctor J R).obj M ⟶ N :=
  ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (homRingUnit J R) N.isSheaf).symm
    ((PresheafOfModules.homEquivOfIsLocallyBijective
      (homUnitLinear J R M) N.isSheaf).symm f)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma constantLift_unit (M : ModuleCat.{max u v} R)
    (N : SheafOfModules.{max u v} (homRing J R))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J R)).obj N.val)
    (U : Cᵒᵖ) (x : M) :
    (constantLift J R M N f).val.app U ((constantModuleHomUnit J R M).app U x) =
      f.app U x := by
  have h := (PresheafOfModules.homEquivOfIsLocallyBijective
    (homUnitLinear J R M) N.isSheaf).apply_symm_apply f
  exact congrArg (fun t ↦ t.app U x) h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma constant_hom_ext (M : ModuleCat.{max u v} R)
    (N : SheafOfModules.{max u v} (homRing J R))
    (a b : (constantModuleHomFunctor J R).obj M ⟶ N)
    (h : ∀ (U : Cᵒᵖ) (x : M),
      a.val.app U ((constantModuleHomUnit J R M).app U x) =
        b.val.app U ((constantModuleHomUnit J R M).app U x)) : a = b := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply sheafify_hom_ext J _ _ N.isSheaf
  ext U x
  exact h U x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def constantOne : ((constantModuleHomFunctor J R).obj (ModuleCat.of R R)).sections :=
  ⟨fun U ↦ (constantModuleHomUnit J R (ModuleCat.of R R)).app U (1 : R),
    fun {_ _} f ↦ (NatTrans.naturality_apply
      (constantModuleHomUnit J R (ModuleCat.of R R)) f (1 : R)).symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def regularMap :
    (siteConstantModulePresheafGeneral (C := C) R).obj (ModuleCat.of R R) ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J R)).obj
        (SheafOfModules.unit (homRing J R)).val where
  app U := ModuleCat.ofHom
    (X := ((siteConstantModulePresheafGeneral (C := C) R).obj (ModuleCat.of R R)).obj U)
    (Y := ((PresheafOfModules.restrictScalars (homRingUnit J R)).obj
      (SheafOfModules.unit (homRing J R)).val).obj U)
    { toFun := fun x ↦ (homRingUnit J R).app U x
      map_add' := ((homRingUnit J R).app U).hom.map_add
      map_smul' := fun r x ↦ ((homRingUnit J R).app U).hom.map_mul r x }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact NatTrans.naturality_apply (homRingUnit J R) f x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def regularHom : (constantModuleHomFunctor J R).obj (ModuleCat.of R R) ⟶
    SheafOfModules.unit (homRing J R) :=
  constantLift J R _ _ (regularMap J R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma regularHom_unit (U : Cᵒᵖ) (x : R) :
    (regularHom J R).val.app U
      ((constantModuleHomUnit J R (ModuleCat.of R R)).app U x) =
      (homRingUnit J R).app U x :=
  constantLift_unit J R _ _ (regularMap J R) U x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def regularInv : SheafOfModules.unit (homRing J R) ⟶
    (constantModuleHomFunctor J R).obj (ModuleCat.of R R) :=
  (SheafOfModules.unitHomEquiv _).symm (constantOne J R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma regularInv_apply (U : Cᵒᵖ) (x : (homRing J R).obj.obj U) :
    (regularInv J R).val.app U x =
      x • (constantModuleHomUnit J R (ModuleCat.of R R)).app U (1 : R) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def regularIso : (constantModuleHomFunctor J R).obj (ModuleCat.of R R) ≅
    SheafOfModules.unit (homRing J R) where
  hom := regularHom J R
  inv := regularInv J R
  hom_inv_id := by
    apply constant_hom_ext J R
    intro U x
    change (regularInv J R).val.app U
      ((regularHom J R).val.app U
        ((constantModuleHomUnit J R (ModuleCat.of R R)).app U x)) = _
    rw [regularHom_unit, regularInv_apply]
    change _ = (constantModuleHomUnit J R (ModuleCat.of R R)).app U x
    have h := ((homUnitLinear J R (ModuleCat.of R R)).app U).hom.map_smul x (1 : R)
    change (constantModuleHomUnit J R (ModuleCat.of R R)).app U (x * 1) =
      (homRingUnit J R).app U x •
        (constantModuleHomUnit J R (ModuleCat.of R R)).app U (1 : R) at h
    simpa only [mul_one] using h.symm
  inv_hom_id := by
    apply (SheafOfModules.unitHomEquiv _).injective
    ext U
    change (regularHom J R).val.app U
      ((regularInv J R).val.app U (1 : (homRing J R).obj.obj U)) =
        (1 : (homRing J R).obj.obj U)
    rw [regularInv_apply, one_smul, regularHom_unit, map_one]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantHom_limits : PreservesFiniteLimits (constantModuleHomFunctor J R) := by
  let G := SheafOfModules.toSheaf (homRing J R)
  have : PreservesFiniteLimits (constantModuleHomFunctor J R ⋙ G) := by
    change PreservesFiniteLimits
      (forget₂ (ModuleCat R) AddCommGrpCat ⋙ constantSheaf J AddCommGrpCat)
    have : PreservesFiniteLimits (constantSheaf J AddCommGrpCat.{max u v}) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (constantSheaf J AddCommGrpCat.{max u v})
  exact preservesFiniteLimits_of_reflects_of_preserves _ G

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def alpha (s : ℕ) :
    (constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R)) ≅
      power J (homRing J R) s := by
  have := constantHom_limits J R
  exact (constantModuleHomFunctor J R).mapIso
      (ModuleCat.piIsoPi (fun _ : Fin s ↦ ModuleCat.of R R)).symm ≪≫
    PreservesProduct.iso (constantModuleHomFunctor J R) (fun _ : Fin s ↦ ModuleCat.of R R) ≪≫
    Pi.mapIso (fun _ : Fin s ↦ regularIso J R)

end CategoryTheory.ConstantFiniteFreePresentationExtension
