/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingShiftDerivedModel
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Localization descent for the derived signed shift square

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: lem-pod-reindexing-signed-shifts).

The representative equation is extended from K-injective localized objects to
all objects of the derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev fixedHom (W : Scheme.{u}) (s : Option ℕ)
    (M : podReindexingDerived l E W s) :=
  (Functor.curry.obj (podReindexingDerivedHom l E W s)).obj (op M)

private def signedShiftNat (W : Scheme.{u}) (s : Option ℕ)
    (M : podReindexingDerived l E W s) (a b : ℤ) :
    shiftFunctor _ b ⋙ fixedHom l E W s (M⟦a⟧) ≅
      fixedHom l E W s M ⋙ shiftFunctor _ (b-a) := by
  letI := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E W s)
  exact Functor.isoWhiskerLeft (shiftFunctor _ b)
      (CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
        (ProEt.topology W) (podReindexingRing l E W s) M a).symm ≪≫
    Functor.isoWhiskerRight
      ((CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
        (ProEt.topology W) (podReindexingRing l E W s) M).commShiftIso b)
      (shiftFunctor _ (-a)) ≪≫
    Functor.isoWhiskerLeft (fixedHom l E W s M)
      (shiftFunctorAdd' _ b (-a) (b-a) (sub_eq_add_neg b a).symm).symm

private lemma signedShiftNat_hom_app (W : Scheme.{u}) (s : Option ℕ)
    (M N : podReindexingDerived l E W s) (a b : ℤ) :
    (signedShiftNat l E W s M a b).hom.app N = (signedShift l E W s M N a b).hom :=
  rfl

private def comparisonAt {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (M : podReindexingDerived l E Y s) :
    fixedHom l E Y s M ⋙ podReindexingDerivedFunctor l E g s ≅
      podReindexingDerivedFunctor l E g s ⋙
        fixedHom l E X s ((podReindexingDerivedFunctor l E g s).obj M) :=
  NatIso.ofComponents (fun N ↦ c.derived.app (op M, N)) (by
    intro N N' f
    have h := c.derived.hom.naturality (Prod.mkHom (𝟙 (op M)) f)
    change (podReindexingDerivedFunctor l E g s).map
        ((podReindexingDerivedHom l E Y s).map (Prod.mkHom (𝟙 (op M)) f)) ≫
          c.derived.hom.app (op M, N') =
      c.derived.hom.app (op M, N) ≫ (podReindexingDerivedHom l E X s).map
        (Prod.mkHom ((podReindexingDerivedFunctor l E g s).map (𝟙 M)).op
          ((podReindexingDerivedFunctor l E g s).map f)) at h
    have hid : ((podReindexingDerivedFunctor l E g s).map (𝟙 M)).op =
        𝟙 (op ((podReindexingDerivedFunctor l E g s).obj M)) :=
      congrArg Quiver.Hom.op ((podReindexingDerivedFunctor l E g s).map_id M)
    rw [hid] at h
    exact h)

-- Keep the original unused proof-binder name in the representative hypothesis.
set_option linter.unusedVariables false in
open SheafOfModules in
/-- Descent of the representative signed-shift equation through localization.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
Proof: resolve the target object by a K-injective complex and represent the
source by a localized complex.  Apply naturality of the comparison and the
K-injective factorization in `Comparison.derived_model`; the representative
hypothesis supplies the signed square on the resulting pair.  Cancel the
isomorphisms from the chosen resolutions and use essential surjectivity of the
localization to obtain the equation for arbitrary derived objects. -/
theorem derived_shift_descent {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (hmodel : ∀ (P I : K l E Y s) (hI : I.IsKInjective) (a b : ℤ),
      derivedShiftEquation l E g s SX SY TX TY c
        ((podReindexingQ l E Y s).obj P)
        ((podReindexingQ l E Y s).obj I) a b) :
    ∀ (M N : podReindexingDerived l E Y s) (a b : ℤ),
      derivedShiftEquation l E g s SX SY TX TY c M N a b := by
  intro M N a b
  let W := HomologicalComplex.quasiIso (podReindexingModules l E Y s) (.up ℤ)
  obtain ⟨P, rfl⟩ := (Localization.Construction.objEquiv W).surjective M
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    (ProEt.topology Y) (podReindexingRing l E Y s)).1
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  let F := podReindexingDerivedFunctor l E g s
  let M := (podReindexingQ l E Y s).obj P
  let H := fixedHom l E X s ((F.obj M)⟦a⟧)
  let lhs := Functor.whiskerLeft (shiftFunctor _ b)
      (comparisonAt l E g s SX SY TX TY c (M⟦a⟧)).hom ≫
    Functor.whiskerLeft (shiftFunctor _ b ⋙ F)
      ((Functor.curry.obj (podReindexingDerivedHom l E X s)).map
        (((F.commShiftIso a).inv.app M).op)) ≫
    Functor.whiskerRight (F.commShiftIso b).hom H ≫
    Functor.whiskerLeft F (signedShiftNat l E X s (F.obj M) a b).hom
  let rhs := Functor.whiskerRight (signedShiftNat l E Y s M a b).hom F ≫
    Functor.whiskerLeft (fixedHom l E Y s M) (F.commShiftIso (b-a)).hom ≫
    Functor.whiskerRight (comparisonAt l E g s SX SY TX TY c M).hom
      (shiftFunctor _ (b-a))
  have component (N : podReindexingDerived l E Y s) :
      lhs.app N = rhs.app N ↔ derivedShiftEquation l E g s SX SY TX TY c M N a b := by
    simp only [derivedShiftEquation, lhs, rhs, comparisonAt,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatIso.ofComponents_hom_app, Iso.app_hom, signedShiftNat_hom_app,
      H, fixedHom, Functor.curry_obj_map_app, Functor.curry_obj_obj_map,
      ← Functor.map_comp_assoc, prod_comp, Category.id_comp]
    erw [Category.comp_id]
    rfl
  have hrep : lhs.app ((podReindexingQ l E Y s).obj I) =
      rhs.app ((podReindexingQ l E Y s).obj I) :=
    (component _).mpr (hmodel P I hI a b)
  have heq : lhs.app N = rhs.app N := by
    have hl := lhs.naturality e.hom
    have hr := rhs.naturality e.hom
    rw [hrep] at hl
    exact (cancel_mono _).mp (hl.symm.trans hr)
  exact (component N).mp heq

end WeilConjectures.PodReindexingCoherence
