/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRestrictionComplete
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCompletedObjectComplete

/-! # Completeness after rational scalar restriction

The finite coefficient square identifies the PBC restriction with the recorded
completed restriction. The PBC completeness theorem and normalized coefficient
transport then give the SF completeness predicate. The statement is separated
from finite reduction constructibility because it requires no geometric
hypothesis on the scheme.
(blueprint: lem-sf-rational-scalar-restriction-complete)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})

/-- The normalized integral transport is derived restriction along the CommRing lift
`purCoefficientIso` of the coefficient comparison.
Source: Stacks 03DA, 099N (auxiliary; not a blueprint node). -/
private noncomputable def integralDetailedTransportIsoPbcDerivedRestrict :
    AlgebraicGeometry.Scheme.integralDetailedTransport W l E ≅
      AlgebraicGeometry.Scheme.pbcDerivedRestrict (purCoefficientIso l E W).hom :=
  letI := (AlgebraicGeometry.Scheme.integralDetailedCoefficientRestriction_exact W l E).1
  letI := (AlgebraicGeometry.Scheme.integralDetailedCoefficientRestriction_exact W l E).2
  letI := AlgebraicGeometry.Scheme.pbcRestrict_limits (purCoefficientIso l E W).hom
  letI := AlgebraicGeometry.Scheme.pbcRestrict_colimits (purCoefficientIso l E W).hom
  Functor.mapDerivedCategoryNatIso (eqToIso (congrArg
    (fun a ↦ SheafOfModules.restrictScalars.{u + 1} a)
    (congrArg Iso.hom (purCoefficientIso_existsUnique l E W).exists.choose_spec).symm))

/-- Completeness is preserved by the specified completed rational restriction.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15.
Proof: transport the object to the normalized PBC coefficient presentation using
`integralDetailedTransport`. The finite quotient projection square identifies the
transport of the completed restriction with PBC restriction. Apply
`pbcScalarRestrictionComplete`, then use `purCoefficientModel_predicates` and
transport back through the derived equivalence. The construction is independent
of Noetherian or dimension assumptions on `W`.
(blueprint: lem-sf-rational-scalar-restriction-complete) -/
theorem rationalScalarDerivedRestriction_complete
    (K : sfIntegralConstructibleCategory l F W) :
    IsSfDerivedComplete l E W
      ((rationalScalarDerivedRestriction l E F ι W).obj K.obj) := by
  let eE := purCoefficientIso l E W
  let eF := purCoefficientIso l F W
  let s := AlgebraicGeometry.Scheme.pbcScalarCoefficientMap l E F ι W
  have hmap : integralCompletedScalarMap l E F ι W =
      completedCoefficientMap l E F ι W := by
    apply (completedCoefficientMap_existsUnique l E F ι W).unique
    · exact (integralCompletedScalarMap_existsUnique l E F ι W).exists.choose_spec
    · exact (completedCoefficientMap_existsUnique l E F ι W).exists.choose_spec
  have hsq : eE.hom ≫ completedCoefficientMap l E F ι W = s ≫ eF.hom := by
    rw [← hmap]
    exact AlgebraicGeometry.Scheme.scalarComplete_coefficientScalar_square l E F ι W
  have hF : AlgebraicGeometry.Scheme.PbcIsIntrinsicallyComplete W
      (AlgebraicGeometry.Scheme.pbcIntegralDatum l F)
      ((AlgebraicGeometry.Scheme.integralDetailedTransport W l F).obj K.obj) :=
    (purDetailedTransport_complete_iff l F W K.obj).mp K.property.1
  have hE := AlgebraicGeometry.Scheme.pbcScalarRestrictionComplete l E F ι W _ hF
  have := AlgebraicGeometry.Scheme.pbcComplete_iso W
    (AlgebraicGeometry.Scheme.pbcIntegralDatum l E)
  let e₁ := (AlgebraicGeometry.Scheme.pbcDerivedRestrictComp eE.hom
    (completedCoefficientMap l E F ι W) _ hsq).app K.obj
  let e₂ := (AlgebraicGeometry.Scheme.pbcDerivedRestrictComp s eF.hom _ rfl).app K.obj
  let tE := integralDetailedTransportIsoPbcDerivedRestrict l E W
  let tF := integralDetailedTransportIsoPbcDerivedRestrict l F W
  apply (purDetailedTransport_complete_iff l E W _).mpr
  exact ObjectProperty.prop_of_iso _
    ((AlgebraicGeometry.Scheme.pbcDerivedRestrict s).mapIso (tF.app K.obj) ≪≫ e₂ ≪≫
      e₁.symm ≪≫ (tE.app _).symm) hE

/-- Completeness is preserved by the specified completed rational restriction, for every
derived complete object (not necessarily constructible).
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15.
Proof: as for `rationalScalarDerivedRestriction_complete`, which only uses completeness.
(blueprint: lem-sf-rational-scalar-restriction-complete) -/
theorem rationalScalarDerivedRestriction_isSfDerivedComplete
    (K : DerivedCategory (scalarReductionSource l F W)) (hK : IsSfDerivedComplete l F W K) :
    IsSfDerivedComplete l E W ((rationalScalarDerivedRestriction l E F ι W).obj K) := by
  let eE := purCoefficientIso l E W
  let eF := purCoefficientIso l F W
  let s := AlgebraicGeometry.Scheme.pbcScalarCoefficientMap l E F ι W
  have hmap : integralCompletedScalarMap l E F ι W =
      completedCoefficientMap l E F ι W := by
    apply (completedCoefficientMap_existsUnique l E F ι W).unique
    · exact (integralCompletedScalarMap_existsUnique l E F ι W).exists.choose_spec
    · exact (completedCoefficientMap_existsUnique l E F ι W).exists.choose_spec
  have hsq : eE.hom ≫ completedCoefficientMap l E F ι W = s ≫ eF.hom := by
    rw [← hmap]
    exact AlgebraicGeometry.Scheme.scalarComplete_coefficientScalar_square l E F ι W
  have hF : AlgebraicGeometry.Scheme.PbcIsIntrinsicallyComplete W
      (AlgebraicGeometry.Scheme.pbcIntegralDatum l F)
      ((AlgebraicGeometry.Scheme.integralDetailedTransport W l F).obj K) :=
    (purDetailedTransport_complete_iff l F W K).mp hK
  have hE := AlgebraicGeometry.Scheme.pbcScalarRestrictionComplete l E F ι W _ hF
  have := AlgebraicGeometry.Scheme.pbcComplete_iso W
    (AlgebraicGeometry.Scheme.pbcIntegralDatum l E)
  let e₁ := (AlgebraicGeometry.Scheme.pbcDerivedRestrictComp eE.hom
    (completedCoefficientMap l E F ι W) _ hsq).app K
  let e₂ := (AlgebraicGeometry.Scheme.pbcDerivedRestrictComp s eF.hom _ rfl).app K
  let tE := integralDetailedTransportIsoPbcDerivedRestrict l E W
  let tF := integralDetailedTransportIsoPbcDerivedRestrict l F W
  apply (purDetailedTransport_complete_iff l E W _).mpr
  exact ObjectProperty.prop_of_iso _
    ((AlgebraicGeometry.Scheme.pbcDerivedRestrict s).mapIso (tF.app K) ≪≫ e₂ ≪≫
      e₁.symm ≪≫ (tE.app _).symm) hE

end WeilConjectures
