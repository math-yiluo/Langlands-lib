/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtaleDerived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-!
# The projection formula for the extension by zero along a weakly étale morphism

For a weakly étale `g : V ⟶ U`, the extension by zero `g_!` on pro-étale sheaves
(`AlgebraicGeometry.ProEtale.weaklyEtaleLowerShriek`, the left Kan extension along the
localization functor `V_proét ⥤ U_proét` followed by sheafification) is an exact left adjoint of
the pullback `g^*` (`AlgebraicGeometry.ProEtale.weaklyEtaleLowerShriekAdjunction` and the
exactness instances of `WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtaleDerived`).

This file shows that for abelian sheaves the adjunction `g_! ⊣ g^*` satisfies the projection
formula: the canonical map `g_!(g^* L ⊗ M) ⟶ L ⊗ g_! M` is an isomorphism
(`AlgebraicGeometry.ProEtale.hasProjectionFormula_weaklyEtaleLowerShriekAdjunction`). It is
conjugate to the internal-hom comparison `g^* [L, N] ⟶ [g^* L, g^* N]`, which is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_ihomComparison_upperStar`). This is the input needed to lift
`g_!` to module objects, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.WeaklyEtale`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {V U : Scheme.{u}} (g : V ⟶ U) [WeaklyEtale g]

/-- The projection map `g_!(g^* L ⊗ M) ⟶ L ⊗ g_! M` of the adjunction `g_! ⊣ g^*` for a weakly
étale `g` on abelian pro-étale sheaves is an isomorphism: it is conjugate to the internal-hom
comparison of `g^*`. -/
theorem isIso_projectionMap_weaklyEtaleLowerShriek
    (L : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
    IsIso (Functor.Monoidal.projectionMap (weaklyEtaleLowerShriekAdjunction Ab.{u + 1} g) L) := by
  have := isIso_ihomComparison_upperStar Ab.{u + 1} g L
  exact Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison _ L

/-- **The projection formula for the extension by zero along a weakly étale morphism**: the
canonical map `g_!(g^* L ⊗ M) ⟶ L ⊗ g_! M` is an isomorphism for abelian pro-étale sheaves. -/
instance hasProjectionFormula_weaklyEtaleLowerShriekAdjunction :
    (weaklyEtaleLowerShriekAdjunction Ab.{u + 1} g).HasProjectionFormula := by
  refine ⟨fun L M ↦ ?_⟩
  have := isIso_projectionMap_weaklyEtaleLowerShriek g L
  have h := NatIso.isIso_app_of_isIso
    (Functor.Monoidal.projectionMap (weaklyEtaleLowerShriekAdjunction Ab.{u + 1} g) L) M
  rw [Adjunction.projectionFormulaMap, Adjunction.homEquiv_counit]
  exact h

end AlgebraicGeometry.ProEtale
