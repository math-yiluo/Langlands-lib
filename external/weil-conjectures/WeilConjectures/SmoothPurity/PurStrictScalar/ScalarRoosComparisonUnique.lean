/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitFoundations
import all WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
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
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence

/-! # Uniqueness of the unit-normalized scalar Roos comparison

This is the unchanged comparison-existence proof extracted from the scalar-limit
reduction module. Source: Stacks 0941
(blueprint: lem-pur-scalar-roos-comparison-unique).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme hiding Modules
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived

/-- The shifted-cone/total-limit identification is uniquely fixed by the actual
ordinary-limit inclusion and the universal derived unit on every tower complex.
Source: Stacks 0941 (blueprint: lem-pur-scalar-roos-comparison-unique).
Proof: exact countable products make the Roos functor invert quasi-isomorphisms.
For an injective tower, 1-shift is split epic degreewise; its kernel inclusion
(0,x) is a quasi-isomorphism. Apply strictRoosComparison with the universal
right-derived unit. Its normalization on all resolutions proves uniqueness. -/
theorem scalarRoosComparison_existsUnique (W : Scheme.{u}) :
    ∃! κ : roosF (A := Modules
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ⋙
          DerivedCategory.Q ≅ DerivedCategory.Q ⋙ scalarLimit l E W,
      ∀ K : CochainComplex (Towers
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ,
        DerivedCategory.Q.map (roosι K) ≫ κ.hom.app K =
          DerivedCategory.Q.map
            (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval K.asFunctor,
              HomologicalComplex.isLimitConeOfHasLimitEval K.asFunctor⟩).hom ≫
            derivedUnit
              (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤ _)
              K := by
  let A := Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W
  let H : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let Q := DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)
  let V := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)
  have : Q.IsLocalization V := by
    dsimp only [Q, V]
    infer_instance
  let c := Functor.isoWhiskerRight (CategoryTheory.strictTowerLimitIso (A := A))
    DerivedCategory.Q
  let η := c.hom ≫ CategoryTheory.ExactDerivedSquare.canonicalUnit H
  have hη : H.rightDerivedFunctor.IsRightDerivedFunctor η V := by
    apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).2
    apply (Functor.isLeftKanExtension_iff_of_iso₂ η
      (CategoryTheory.ExactDerivedSquare.canonicalUnit H) c
      (Iso.refl H.rightDerivedFunctor) (by simp [η])).2
    exact (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).1
      (CategoryTheory.ExactDerivedSquare.canonicalUnit_derived H)
  have : HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{u + 1} ((adicLisseForget W).obj ((constants l E).ring W))) :=
    scalarRoos_exactProducts l E W
  obtain ⟨CF, κ, hCF, _⟩ := strictRoosDerivation.{u + 1, u, 0, u + 2}
    (ProEt.topology W)
    ((adicLisseForget W).obj ((constants l E).ring W))
    (fun U a b ↦ @mul_comm (((constants l E).ring W).obj.obj U) _ a b)
  have := hη
  have : CF.IsRightDerivedFunctor (roosDerivedUnit κ) V := hCF
  let ρ := Functor.rightDerivedUnique CF H.rightDerivedFunctor (roosDerivedUnit κ) η V
  let θ := κ ≪≫ Functor.isoWhiskerLeft Q ρ
  have hθ (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      DerivedCategory.Q.map (roosι K) ≫ θ.hom.app K = η.app K := by
    have h := Functor.rightDerivedNatTrans_app CF H.rightDerivedFunctor
      (roosDerivedUnit κ) η V (𝟙 _) K
    simpa only [θ, ρ, Q, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Functor.isoWhiskerLeft_hom, Iso.refl_hom,
      roosDerivedUnit, roosInclusion, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, NatTrans.comp_app, Iso.trans_hom, Category.assoc,
      NatTrans.id_app, Category.id_comp] using h
  refine ⟨θ, ?_, ?_⟩
  · intro K
    exact hθ K
  · intro θ' hθ'
    let liftCF : Localization.Lifting Q V (Q ⋙ CF) CF :=
      Localization.Lifting.compLeft Q V CF
    let liftH : Localization.Lifting Q V (Q ⋙ H.rightDerivedFunctor) H.rightDerivedFunctor :=
      Localization.Lifting.compLeft Q V H.rightDerivedFunctor
    let δ := Localization.liftNatIso Q V (Q ⋙ CF) (Q ⋙ H.rightDerivedFunctor)
      CF H.rightDerivedFunctor (κ.symm ≪≫ θ')
    have hδ (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
        δ.hom.app (Q.obj K) = κ.inv.app K ≫ θ'.hom.app K := by
      simp only [δ, liftCF, liftH, Localization.liftNatIso_hom,
        Localization.liftNatTrans_app,
        Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
        Category.id_comp, Category.comp_id, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app]
    have hd : δ.hom = ρ.hom := by
      apply Functor.rightDerived_ext CF (roosDerivedUnit κ) V H.rightDerivedFunctor
      apply NatTrans.ext
      funext K
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, roosDerivedUnit,
        Functor.whiskerRight_app, roosInclusion, Category.assoc]
      change DerivedCategory.Q.map (roosι K) ≫ κ.hom.app K ≫ δ.hom.app (Q.obj K) =
        DerivedCategory.Q.map (roosι K) ≫ κ.hom.app K ≫ ρ.hom.app (Q.obj K)
      rw [hδ]
      simpa only [θ, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
        Iso.trans_hom, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
        using (hθ' K).trans (hθ K).symm
    apply Iso.ext
    apply NatTrans.ext
    funext K
    have hh := congrArg (fun t ↦ κ.hom.app K ≫ t.app (Q.obj K)) hd
    simpa only [hδ, θ, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, NatTrans.comp_app, ← Category.assoc,
      Iso.hom_inv_id_app, Category.id_comp] using hh

end WeilConjectures.PurStrictScalar
