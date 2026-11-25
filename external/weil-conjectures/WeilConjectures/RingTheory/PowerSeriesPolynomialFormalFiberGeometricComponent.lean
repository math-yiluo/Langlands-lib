/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.FieldTheory.PurelyInseparableDegreePIntermediate
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.HypersurfaceDerivationRegular
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.PowerSeriesPolynomialFormalFiberDegreePPresentation
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
Geometric-regularity component for the characteristic-p formal fibre theorem.
Source: Stacks Project, More on Algebra, Lemma 07PR.
(blueprint: new-lem-weil-pbc-helper-g-ring-char-p-geometric-component)
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- The generic fibre is a localization of a regular completion (Stacks Tag 07PR). -/
private theorem generic_fiber_regular
    (k : Type u) [Field k] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime] :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    IsRegularRing ((⊥ : Ideal A).Fiber C) := by
  let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
  let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q)
  have hps := power_series_field_cohen_regular_complete (Λ := k) n
    (Or.inl (Field.toIsField k))
  have hreg : IsRegularLocalRing (MvPowerSeries (Fin n) k) := by
    rcases hps with ⟨_, _, _, _, _, e, _, _, hr, _⟩ | ⟨p, hp, _⟩
    · exact hr
    · rcases hp with ⟨_, hd, hv, _⟩
      let := hd
      let := hv
      exact False.elim (IsDiscreteValuationRing.not_isField k (Field.toIsField k))
  let := hreg
  have : IsRegularRing (MvPowerSeries (Fin n) k) :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) k))).2
  have : IsRegularRing A := inferInstance
  have : IsRegularLocalRing C := (AdicCompletion.isRegularLocalRing_iff _).mp inferInstance
  have : IsRegularRing C :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal C)).2
  let T := Algebra.algebraMapSubmonoid C (⊥ : Ideal A).primeCompl
  have : IsRegularRing (Localization T) := inferInstance
  let : Algebra C ((⊥ : Ideal A).Fiber C) := Algebra.TensorProduct.rightAlgebra
  let e := (Ideal.Fiber.algEquivAux₁ (S := C) (⊥ : Ideal A)).toRingEquiv
  have : IsRegularRing
      (Localization T ⧸ ((⊥ : Ideal A).map (algebraMap A C)).map
        (algebraMap C (Localization T))) := by
    rw [Ideal.map_bot, Ideal.map_bot]
    exact IsRegularRing.of_ringEquiv (RingEquiv.quotientBot (Localization T)).symm
  exact IsRegularRing.of_ringEquiv e.symm

/-- Extend the coefficient derivation to the binomial equation (Stacks Tag 07PG). -/
private theorem regular_binomial_quotient
    (R : Type u) [CommRing R] [IsRegularRing R]
    (f : R) (D : Derivation ℤ R R) (hD : IsUnit (D f)) (p : ℕ) :
    IsRegularRing (Polynomial R ⧸
      Ideal.span ({Polynomial.X ^ p - Polynomial.C f} : Set (Polynomial R))) := by
  let E : Derivation ℤ (Polynomial R) (Polynomial R) :=
    PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs
  have hX : E Polynomial.X = 0 := by
    simp [E]
  have hC : E (Polynomial.C f) = Polynomial.C (D f) := by
    simp [E]
  have hEq : E (Polynomial.X ^ p - Polynomial.C f) = -Polynomial.C (D f) := by
    rw [map_sub, E.leibniz_pow, hX, smul_zero, smul_zero, hC, zero_sub]
  have hunit : IsUnit (Ideal.Quotient.mk
      (Ideal.span ({Polynomial.X ^ p - Polynomial.C f} : Set (Polynomial R)))
      (E (Polynomial.X ^ p - Polynomial.C f))) := by
    rw [hEq]
    exact ((hD.map Polynomial.C).neg).map _
  exact IsRegularRing.quotient_span_singleton_of_isUnit_derivation
    (Polynomial R) _ E hunit

/-- Regularity of the generic formal fibre after each finite purely inseparable base change.
Source: Stacks Project, More on Algebra, Lemma Tag 07PR, proof.
(blueprint: new-lem-weil-pbc-helper-g-ring-char-p-geometric-component)

Proof (the five steps of the node):
1. The power series ring is regular local (power-series-field-cohen-regular-complete).
   Polynomial extension is smooth (polynomial-ring-smooth), so A is regular by
   regular-ring-smooth-ascent. Prime localization and completion preserve regularity
   (regular-local-localization and completion-regular-local). The generic formal fibre
   is a localization of this completion, hence regular and Noetherian
   (adic-completion-noetherian). This is the degree-one base case.
2. Induct on the degree of a finite purely inseparable extension L/K. By
   finite-purely-inseparable-degree-p-intermediate choose K ⊆ M ⊆ L with L = M(z),
   z^p = f and [L:M] = p; f is not a p-th power in M. Apply induction to M.
3. By finite-subalgebra-fraction-field choose a finite A-subalgebra B of M with fraction
   field M. Write f = b/s and replace z by sz and f by s^p f = s^(p-1)b. The field L,
   degree p and failure to be a p-th power are unchanged, and now f belongs to B.
   Set C = B[z]/(z^p-f), finite free over B, a domain with fraction field L, since
   z has minimal polynomial of degree p. B is Noetherian (finite-algebra-noetherian).
   A is normal by regular-ring-normal and normal-domain-of-local-normal. By
   purely-inseparable-integral-prime-unique there is a unique prime r of B over q;
   radicial-prime-unique-degree-p gives a unique prime t of C over r. Since c^p is in B
   for every c in C, C tensor B_r is local and equals C_t. By completion-finite-quotient
   its completion is the polynomial quotient of the completion of B_r. Applying
   completion-finite-extension (07N9) to both B and C, and tensoring with their fraction
   fields, identifies the fibre over M with R = completion(B_r) tensor_B M and the fibre
   over L with R[z]/(z^p-f).
4. B is finite type over the complete Noetherian power series local ring. By
   derivation-nonzero-on-non-pth-power choose D:B → B with D(f) nonzero. Extend it to
   B_r, its completion and R by derivation-extends. The image of D(f) is a unit in R.
   By induction R is regular. Its polynomial ring is regular by polynomial-ring-smooth
   and regular-ring-smooth-ascent. Extend D coefficientwise, with D(z) = 0. It sends
   z^p-f to the unit -D(f), so hypersurface-derivation-regular gives regularity of
   R[z]/(z^p-f), and hence the fibre over L.
5. All finite purely inseparable base changes are regular. By
theorem-finite-etale-covers-proper-henselian--2 this
   proves geometric regularity; Noetherianity was obtained in step 1.

The base-change tensor product is the source's completion tensor_A L, by tensor
associativity and exchange of factors. This theorem supplies only the regularity
condition; Noetherianity of the original fibre is established independently. -/
theorem formalFiber_polynomial_geometricComponent
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime] :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    ∀ (k' : Type u) [Field k'] [Algebra ((⊥ : Ideal A).ResidueField) k']
      [Module.Finite ((⊥ : Ideal A).ResidueField) k']
      [IsPurelyInseparable ((⊥ : Ideal A).ResidueField) k'],
      IsRegularRing (TensorProduct ((⊥ : Ideal A).ResidueField) k'
        ((⊥ : Ideal A).Fiber C)) := by
  set_option backward.isDefEq.respectTransparency false in
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let K := (⊥ : Ideal A).ResidueField
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let F := (⊥ : Ideal A).Fiber C
    have : IsDomain A := NoZeroDivisors.to_isDomain A
    have : CharP (MvPowerSeries (Fin n) k) p :=
      charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := Fin n)) p
    have : CharP A p := charP_of_injective_ringHom (MvPolynomial.C_injective (Fin m) _) p
    have : CharP K p := IsFractionRing.charP_of_isFractionRing A p
    have hbase : IsRegularRing F := generic_fiber_regular k n m q
    have hdegree (d : ℕ) :
        ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
          [IsPurelyInseparable K L], Module.finrank K L = d →
          IsRegularRing (TensorProduct K L F) := by
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro L _ _ _ _ hd
        by_cases h1 : Module.finrank K L = 1
        · obtain ⟨e⟩ := Module.nonempty_algEquiv_iff_finrank_eq_one.mpr h1
          let eF := (Algebra.TensorProduct.congr e (AlgEquiv.refl : F ≃ₐ[K] F)).symm.trans
            (Algebra.TensorProduct.lid K F)
          exact IsRegularRing.of_ringEquiv eF.symm.toRingEquiv
        · have hgt : 1 < Module.finrank K L :=
            lt_of_le_of_ne Module.finrank_pos (Ne.symm h1)
          obtain ⟨M, z, hfin, hpure, hlt, hz, hpow, hdeg⟩ :=
            IsPurelyInseparable.exists_degree_p_intermediate K L p
              (Fact.out : p.Prime).pos hgt
          let := hfin
          let := hpure
          have hM : IsRegularRing (TensorProduct K M F) :=
            ih (Module.finrank K M) (hd ▸ hlt) M rfl
          let := hM
          obtain ⟨f, D, hunit, ⟨e⟩⟩ :=
            formalFiber_polynomial_degreePPresentation k p n m q L M z hz hpow hdeg
          have := regular_binomial_quotient (TensorProduct K M F) f D hunit p
          exact IsRegularRing.of_ringEquiv
            (R := Polynomial (TensorProduct K M F) ⧸
              Ideal.span ({Polynomial.X ^ p - Polynomial.C f} : Set _)) e
    change ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
      [IsPurelyInseparable K L], IsRegularRing (TensorProduct K L F)
    intro L _ _ _ _
    exact hdegree (Module.finrank K L) L rfl

end MvPowerSeries
