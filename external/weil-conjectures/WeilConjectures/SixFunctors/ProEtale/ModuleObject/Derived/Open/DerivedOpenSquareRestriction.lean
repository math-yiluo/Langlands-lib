/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenSquareScalarComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift

set_option linter.privateModule false

/-! # Unbounded open restriction of condensed-module direct image

Source: blueprint main-20261015, chap-Construction-of-f,
sk-thm-sf-comp-composition/det-sf-comp-composition-interchange.proof.md, Proof (2)
(blueprint: lem-sfb-derived-open-square-restriction).

The helpers spell out the canonical inverse-image comparison, its open mate, exact
termwise derivation, and the five Hom bijections. All categories are the ordinary
unbounded derived categories of internal modules over the pulled-back condensed ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {W Y Ybar : Scheme.{u}} (r : W ⟶ Ybar) (i : Y ⟶ Ybar) [IsOpenImmersion i]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem conjugate_hom
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁)
    (T : C) (B : D) (f : T ⟶ R₁.obj B) :
    f ≫ ((conjugateIsoEquiv a₁ a₂ e).hom.app B) =
      a₂.homEquiv T B (e.hom.app T ≫ (a₁.homEquiv T B).symm f) := by
  apply (a₂.homEquiv T B).symm.injective
  simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc]
  rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_counit]
  rw [← e.hom.naturality_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
