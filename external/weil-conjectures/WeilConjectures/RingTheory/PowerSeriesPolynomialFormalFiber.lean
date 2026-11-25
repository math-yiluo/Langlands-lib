/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Polynomial.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.PowerSeriesPolynomialFormalFiberGeometricComponent

/-!
# Generic formal fibres of polynomial rings over power series fields

Source: Stacks Project, More on Algebra, Lemma 07PR
(blueprint: lem-weil-pbc-helper-g-ring-char-p).
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- In positive characteristic the generic formal fibre of a polynomial ring over a finite
variable power series field is Noetherian and geometrically regular.
Source: Stacks Project, More on Algebra, Lemma 07PR
(blueprint: lem-weil-pbc-helper-g-ring-char-p).

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

`(⊥ : Ideal A).ResidueField` is κ(0), the fraction field of the domain A.
`Ideal.Fiber` places κ(0) first in the tensor product, canonically exchanging the factors
of the displayed completion tensor_A K in the source. -/
theorem formalFiber_polynomial_isGeometricallyRegular
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime] :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    IsNoetherianRing ((⊥ : Ideal A).Fiber C) ∧
      Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField ((⊥ : Ideal A).Fiber C) := by
  dsimp
  let R := Localization.AtPrime q
  let I := IsLocalRing.maximalIdeal R
  let C := AdicCompletion I R
  let : IsNoetherianRing R := inferInstance
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing I
  have hnoeth := Ideal.isNoetherianRing_fiber (B := C)
    (⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
  exact ⟨hnoeth, hnoeth, formalFiber_polynomial_geometricComponent k p n m q⟩

end MvPowerSeries
