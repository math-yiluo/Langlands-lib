/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
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

/-! # Naturality descent of the source-shift square

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.
A representative square descends through localization and K-injective resolutions.
(blueprint: lem-pod-reindexing-source-shift-descent)
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

set_option linter.unusedVariables false in
open SheafOfModules in
/-- Localization descent for the normalized source-shift square.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
Proof: represent the source by a localized complex and the target by a
K-injective resolution.  Naturality of `c.derived` transports the square to
the chosen representatives; cancel the resolution and localization
isomorphisms, then use essential surjectivity of the localization.  The
premise is the representative theorem, so this statement is strictly weaker
than proving the representative calculation itself.
(blueprint: lem-pod-reindexing-source-shift-descent) -/
theorem derived_source_shift_descent
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (hmodel : ∀ (P I : K l E Y s) (hI : I.IsKInjective) (a : ℤ),
      c.derived.hom.app
          (op (((podReindexingQ l E Y s).obj P)⟦a⟧),
            (podReindexingQ l E Y s).obj I) ≫
        (podReindexingDerivedHom l E X s).map
          (Prod.mkHom
            (((podReindexingDerivedFunctor l E g s).commShiftIso a).inv.app
              ((podReindexingQ l E Y s).obj P)).op
            (𝟙 ((podReindexingDerivedFunctor l E g s).obj
              ((podReindexingQ l E Y s).obj I)))) ≫
        (CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
          (ProEt.topology X) (podReindexingRing l E X s)
          ((podReindexingDerivedFunctor l E g s).obj
            ((podReindexingQ l E Y s).obj P)) a).inv.app
              ((podReindexingDerivedFunctor l E g s).obj
                ((podReindexingQ l E Y s).obj I)) =
      (podReindexingDerivedFunctor l E g s).map
        ((CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
          (ProEt.topology Y) (podReindexingRing l E Y s)
          ((podReindexingQ l E Y s).obj P) a).inv.app
            ((podReindexingQ l E Y s).obj I)) ≫
        ((podReindexingDerivedFunctor l E g s).commShiftIso (-a)).hom.app
          ((podReindexingDerivedHom l E Y s).obj
            (op ((podReindexingQ l E Y s).obj P), (podReindexingQ l E Y s).obj I)) ≫
        (c.derived.hom.app
          (op ((podReindexingQ l E Y s).obj P), (podReindexingQ l E Y s).obj I))⟦-a⟧') :
    ∀ (M N : podReindexingDerived l E Y s) (a : ℤ),
      c.derived.hom.app (op (M⟦a⟧), N) ≫
        (podReindexingDerivedHom l E X s).map
          (Prod.mkHom (((podReindexingDerivedFunctor l E g s).commShiftIso a).inv.app M).op
            (𝟙 ((podReindexingDerivedFunctor l E g s).obj N))) ≫
        (CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
          (ProEt.topology X) (podReindexingRing l E X s)
          ((podReindexingDerivedFunctor l E g s).obj M) a).inv.app
            ((podReindexingDerivedFunctor l E g s).obj N) =
      (podReindexingDerivedFunctor l E g s).map
        ((CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
          (ProEt.topology Y) (podReindexingRing l E Y s) M a).inv.app N) ≫
        ((podReindexingDerivedFunctor l E g s).commShiftIso (-a)).hom.app
          ((podReindexingDerivedHom l E Y s).obj (op M, N)) ≫
        (c.derived.hom.app (op M, N))⟦-a⟧'  := by
  intro M N a
  let W := HomologicalComplex.quasiIso (podReindexingModules l E Y s) (.up ℤ)
  obtain ⟨P, rfl⟩ := (Localization.Construction.objEquiv W).surjective M
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    (ProEt.topology Y) (podReindexingRing l E Y s)).1
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  let F := podReindexingDerivedFunctor l E g s
  let M := (podReindexingQ l E Y s).obj P
  let sx := CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
    (ProEt.topology X) (podReindexingRing l E X s) (F.obj M) a
  let sy := CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
    (ProEt.topology Y) (podReindexingRing l E Y s) M a
  let lhs := (comparisonAt l E g s SX SY TX TY c (M⟦a⟧)).hom ≫
    Functor.whiskerLeft F
      ((Functor.curry.obj (podReindexingDerivedHom l E X s)).map
        (((F.commShiftIso a).inv.app M).op)) ≫
    Functor.whiskerLeft F sx.inv
  let rhs := Functor.whiskerRight sy.inv F ≫
    Functor.whiskerLeft (fixedHom l E Y s M) (F.commShiftIso (-a)).hom ≫
    Functor.whiskerRight (comparisonAt l E g s SX SY TX TY c M).hom
      (shiftFunctor _ (-a))
  have hrep : lhs.app ((podReindexingQ l E Y s).obj I) =
      rhs.app ((podReindexingQ l E Y s).obj I) := by
    simpa only [lhs, rhs, comparisonAt, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_hom_app,
      Iso.app_hom, fixedHom, Functor.curry_obj_map_app, Functor.curry_obj_obj_obj,
      sx, sy, F, M] using hmodel P I hI a
  have heq : lhs.app N = rhs.app N := by
    have hl := lhs.naturality e.hom
    have hr := rhs.naturality e.hom
    rw [hrep] at hl
    exact (cancel_mono _).mp (hl.symm.trans hr)
  have hQ : (Localization.Construction.objEquiv W) P =
      (podReindexingQ l E Y s).obj P := by rfl
  rw [hQ]
  simpa only [lhs, rhs, comparisonAt, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_hom_app,
    Iso.app_hom, fixedHom, Functor.curry_obj_map_app, Functor.curry_obj_obj_obj,
    sx, sy, F, M] using heq

end WeilConjectures.PodReindexingCoherence
