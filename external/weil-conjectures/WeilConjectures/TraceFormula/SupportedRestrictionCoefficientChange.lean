/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestriction
public import WeilConjectures.TraceFormula.SupportedRestriction

/-!

# The supported restriction under a change of coefficients

The supported restriction `ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P` of a fixed square
(`ProEtale.CondensedRing.Correspondence.FixedLocus.supportedRestriction`, blueprint
`lemma-local-term-restriction-map--1`) is a formal consequence of the adjunctions `c_! ⊣ c^!`,
`d_! ⊣ d^!` and of compact-support base change `σ : c_! ⋙ Δ^* ≅ ι^* ⋙ d_!`: it is the mate
`c^! ⋙ ι^* ⟶ Δ^* ⋙ d^!` of `σ⁻¹` (`FixedLocus.supportedRestriction_eq_mateEquiv`). This file
proves that such a mate commutes with any change of coefficients `T` which commutes with `c_!`,
`d_!`, `ι^*` and `Δ^*` compatibly with base change
(`CategoryTheory.Adjunction.map_mateEquiv_app_comp`): the image under `T` of the supported
restriction, followed by the exchange `T ⋙ Rd^! ⟶ Rd'^! ⋙ T` (the mate of the lower-shriek
comparison), is the exchange for `c^!` followed by the supported restriction for the new
coefficients. This is the coefficient compatibility of `ρ` used to transport the vanishing of the
supported restriction between coefficient rings (blueprint `lemma-vanishing-local-term-zero-stalk`,
last step); the inputs are the coefficient comparisons of blueprint
`proposition-six-operations-change-coefficients` and the compatibility of base change with them
(blueprint `sk-thm-sf-compatibility`, (7)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj


namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K}

/-- The supported restriction is the mate `Rc^! ⋙ Lι^* ⟶ LΔ^* ⋙ Rd^!` of the inverse of
compact-support base change in the fixed square. -/
lemma Correspondence.FixedLocus.supportedRestriction_eq_mateEquiv (F : c.FixedLocus)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    F.supportedRestriction P =
      (CategoryTheory.mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ c.support)
        (boundedConstructibleUpperShriekAdjunction ℓ F.d)
        (TwoSquare.mk _ _ _ _ F.lowerShriekBaseChangeIso.inv)).app P := by
  rw [Adjunction.mateEquiv_app_eq_homEquiv, ← F.homEquiv_symm_supportedRestriction]
  exact (Equiv.apply_symm_apply _ _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
