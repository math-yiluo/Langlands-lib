/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
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
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-! # K-injective resolutions for completed towers

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0D6E.
(blueprint: lem-pur-completed-coefficient-tower-limit-acyclic-resolution).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance completedPushAdditiveAux {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X)) : (push f c).Additive where
  map_add := by intros; rfl

local instance {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X)) :
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)).PreservesZeroMorphisms :=
  inferInstance

/-- A K-injective resolution exists for every completed tower complex used here.
This is the Grothendieck-module resolution step in the proof of Stacks Tags 0A07
and 0D6E.
(blueprint: lem-pur-completed-coefficient-tower-limit-acyclic-resolution)
-/
theorem completedTower_exists_isKInjective {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (I : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ) :
    ∃ (T : CochainComplex (ℕᵒᵖ ⥤ Mod Y (R l E Y)) ℤ)
      (j : ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)).mapHomologicalComplex
        (.up ℤ)).obj I) ⟶ T), T.IsKInjective ∧ QuasiIso j := by
  classical
  let B := Mod Y (R l E Y)
  have : IsGrothendieckAbelian.{max u (t + 1)} B :=
    SheafOfModules.isGrothendieckAbelianOfUniverses (ProEt.topology Y) (R l E Y)
  let G := separator B
  have hG := isSeparator_separator B
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun n : ℕᵒᵖ ↦ (evaluationLeftAdjoint B n).obj G) := by
    intro F F' a b hab
    apply NatTrans.ext
    funext n
    apply hG.def
    intro x
    let adj := evaluationAdjunctionRight B n
    apply (adj.homEquiv G F').symm.injective
    have h := hab _ (ObjectProperty.ofObj_apply _ n) ((adj.homEquiv G F).symm x)
    exact (adj.homEquiv_naturality_right_symm x a).trans
      (h.trans (adj.homEquiv_naturality_right_symm x b).symm)
  have : HasSeparator (ℕᵒᵖ ⥤ B) := ⟨_, hS.isSeparator_coproduct⟩
  have : HasFilteredColimitsOfSize.{max u (t + 1), max u (t + 1)} (ℕᵒᵖ ⥤ B) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{max u (t + 1), max u (t + 1)} (ℕᵒᵖ ⥤ B) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : IsGrothendieckAbelian.{max u (t + 1)} (ℕᵒᵖ ⥤ B) := {}
  obtain ⟨T, hT, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)).mapHomologicalComplex
      (.up ℤ)).obj I)
  exact ⟨T, j, hT, hj⟩

end WeilConjectures.CompletedCoefficientPushforward
