/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentExchangeFactor
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent
public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnComponentBdc
public import WeilConjectures.TraceFormula.Specialization.SupportExchangeOnComponent

/-!

# The exchange `ν_c` of the support on pushforwards from a component, without hypothesis

The ambient hypothesis `hC` of `supportCompactSupportExchange_app_lowerStar` is an instance of
`NearbyCyclesModel.Hom.compactSupportExchange_comp_app`
(`Correspondence.IsContractingAt.supportCompactSupportExchange_app_lowerStar_ambient`), after the
`Precoherent Profinite` proofs inside the `MonObj` instances of the goal are identified by the
tactic `normalize_precoherent` (the normalizer of `PointExchangeOnComponentBdc`, as a tactic).
This gives `supportCompactSupportExchange_app_lowerStar_eq`, input `hF1` of
`CategoryTheory.supportIdentity_aux`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [Algebra k k']
  {F : c.FixedLocus} {B : Over (Spec (.of k))} (j : B ⟶ F.F) {b : RationalPoint B}
  (hb : b ≫ j ≫ F.ι = y)
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k']
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [IsProper (supportClosureSpaceMap c y)]

/-- **The ambient identity `hC` of `supportCompactSupportExchange_app_lowerStar`**: an instance of
`NearbyCyclesModel.Hom.compactSupportExchange_comp_app`, once the `Precoherent Profinite` proofs
in the `MonObj` instances of `ℚ̄_ℓ` are identified. -/
theorem supportCompactSupportExchange_app_lowerStar_ambient
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    HypothesisOf (supportCompactSupportExchange_app_lowerStar hc k' j hb N) := by
  normalize_precoherent
  intro χ₀ hχ₀
  exact NearbyCyclesModel.Hom.compactSupportExchange_comp_app _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    rfl rfl _ _ _ χ₀ hχ₀

/-- **The exchange `ν_c` of the support on pushforwards from a component**, without hypothesis:
`supportCompactSupportExchange_app_lowerStar` for its ambient identity
`supportCompactSupportExchange_app_lowerStar_ambient`. -/
theorem supportCompactSupportExchange_app_lowerStar_eq
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    type_of% (supportCompactSupportExchange_app_lowerStar hc k' j hb N
      (supportCompactSupportExchange_app_lowerStar_ambient hc k' j hb N)) :=
  supportCompactSupportExchange_app_lowerStar hc k' j hb N
    (supportCompactSupportExchange_app_lowerStar_ambient hc k' j hb N)

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
