/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Comparing finite quotients of the two integer-ring presentations

Source: latest blueprint, coefficient biduality proof, paragraph (i).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Comparing the chosen DVR presentations requires unfolding the spectral norm data.
/-- The embedded uniformizer quotient agrees with the finite coefficient ring
used by the ordinary etale comparison, independently of the uniformizer generator.

Source: latest blueprint, det-pd-biduality-coefficients.proof.md, paragraph (i),
and the coefficient normalization of lem-integral-coefficient-ext-comparison.
(blueprint: lem-sf-condensed-verdier-coefficient-comparison).

Proof: the spectral norm on the lifted finite extension is its embedded norm,
so integerLiftEquiv explicitly identifies the two integer rings. A local ring
isomorphism carries the maximal ideal onto the maximal ideal. Both uniformizers
generate those ideals, so it identifies their nth powers. The induced quotient
ring equivalence is the required one. This includes n=0 and the zero quotient. -/
theorem condensedVerdier_quotient_ringEquiv
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ) :
    Nonempty ((PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ n) ≃+*
      Padic.coefficientExtensionRing ℓ (ULift.{u} E.1) n) := by
  have : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.1) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.1)).symm.finiteDimensional
  let S := Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.1)
  let g := integerLiftEquiv ℓ E
  have hdata := (Padic.coefficientExtensionIntegers_dvr ℓ (ULift.{u} E.1)).choose_spec
  have : IsLocalRing S := hdata.2.2.2.1
  have hmax : Padic.coefficientExtensionMaximalIdeal ℓ (ULift.{u} E.1) =
      IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal hdata.2.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer ℓ (ULift.{u} E.1)} =
      Padic.coefficientExtensionMaximalIdeal ℓ (ULift.{u} E.1) :=
    hdata.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmap : Padic.coefficientExtensionIdeal ℓ (ULift.{u} E.1) n =
      ((Ideal.span {π}) ^ n).map g := by
    change Ideal.span {Padic.coefficientExtensionUniformizer ℓ (ULift.{u} E.1)} ^ n = _
    rw [Ideal.map_pow, hπ, IsLocalRing.map_ringEquiv_maximalIdeal, hgen, hmax]
  exact ⟨Ideal.quotientEquiv _ _ g hmap⟩

end AlgebraicGeometry.ProEtale.CondensedRing
