/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension
import WeilConjectures.RingTheory.IsN2OfFiniteExtension
import WeilConjectures.RingTheory.PolynomialPurelyInseparableIntegralClosureFinite
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import WeilConjectures.RingTheory.N2CharPPurelyInseparableCriterion

/-!
# Polynomial rings over Noetherian Japanese domains

Source: Stacks Project, Algebra, Lemma 10.161.13 (Tag 032O), second assertion
(blueprint: lem-weil-pbc-polynomial-ring-n2).
-/

@[expose] public section

universe u

set_option autoImplicit false

private theorem finite_polynomial_extension (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] :
    letI : Algebra (Polynomial R) (Polynomial A) := Polynomial.algebra R A
    Module.Finite (Polynomial R) (Polynomial A) := by
  let : Algebra (Polynomial R) (Polynomial A) := Polynomial.algebra R A
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := A)
  let T := Submodule.span (Polynomial R) (Polynomial.C '' (s : Set A))
  have hC (a : A) : Polynomial.C a ∈ T := by
    have ha : a ∈ Submodule.span R (s : Set A) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩
    | zero => simp [T]
    | add a b ha hb ha' hb' => simpa using T.add_mem ha' hb'
    | smul r a ha ha' =>
      simpa [Algebra.smul_def, Polynomial.algebraMap_def] using
        T.smul_mem (Polynomial.C r) ha'
  have hmem (p : Polynomial A) : p ∈ T := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact T.add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_comm]
      convert T.smul_mem (Polynomial.X ^ n) (hC a) using 1
      simp only [Algebra.smul_def, Polynomial.algebraMap_def,
        Polynomial.coe_mapRingHom, Polynomial.map_pow, Polynomial.map_X]
  have hT : T = ⊤ := top_unique (fun p _ ↦ hmem p)
  exact ⟨⟨s.image Polynomial.C, by simpa [T] using hT⟩⟩

private theorem isN2_polynomial_normal (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (hR : IsN2 R (FractionRing R)) :
    IsN2 (Polynomial R) (FractionRing (Polynomial R)) := by
  rcases CharP.exists' (FractionRing (Polynomial R)) with hzero | ⟨p, hp, hchar⟩
  · let := hzero
    intro L _ _ _ _ _
    exact IsIntegralClosure.finite (Polynomial R) (FractionRing (Polynomial R)) L
      (integralClosure (Polynomial R) L)
  · let := hp
    let := hchar
    apply isN2_of_finite_purelyInseparable_integralClosure
      (Polynomial R) (FractionRing (Polynomial R)) p
    intro L _ _ _ _ _ _
    exact finite_polynomial_purelyInseparable_integralClosure R hR p L

/-- The polynomial ring in one variable over a Noetherian N-2 domain is N-2.
Source: Stacks Project, Algebra, Lemma 10.161.13 (Tag 032O), second assertion
(blueprint: lem-weil-pbc-polynomial-ring-n2).

Proof (the eight steps of the node).
1. Let `K` be the fraction field of `R` and `R'` its normalization in `K`.
   The N-2 hypothesis makes `R'` finite over `R`. It is a Noetherian normal domain by
   `lem-weil-pbc-integral-closure-finite-extension-normal` and
   `lem-weil-pbc-finite-algebra-noetherian`. Transitivity of integrality
   (`lem-weil-pbc-integral-transitive`) identifies the integral closures of `R` and `R'`
   in every finite extension of `K`, so `R'` is N-2. Coefficientwise generators make
   `R'[X]` finite over `R[X]`; their fraction fields agree. The same transitivity and
   `lem-weil-pbc-finite-module-over-finite-algebra` reduce the assertion to `R'`.
   Here finiteness implies integrality by `lem-weil-pbc-finite-algebra-is-integral`.
2. We may thus assume `R` normal. Its polynomial ring is a Noetherian normal domain by
   `lem-weil-pbc-finite-type-algebra-noetherian`, `lem-weil-pbc-polynomial-ring-domain`,
   and `lem-weil-pbc-polynomial-ring-normal-domain`. Clearing coefficient denominators
   identifies its fraction field with `K(x)` (`def-weil-rational-function-field`).
3. In characteristic zero every finite extension of `K(x)` is separable by
   `lem-weil-pbc-char-zero-field-extension-separable`; its transcendence basis is empty.
   Apply `lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`.
4. In characteristic `p > 0`, `lem-weil-pbc-n2-char-p-purely-inseparable-criterion`
   reduces the assertion to finite purely inseparable extensions `L/K(x)`.
5. Choose a basis of `L/K(x)` and a common power `q = p^e` carrying its elements into
   `K(x)`. In an algebraic closure, adjoin to `K` the `q`-th roots of the coefficients
   of their rational-function numerators and denominators, obtaining `L'`. The monomials
   in these roots with exponents below `q` span a finite-dimensional domain, hence a
   field. This is a finite purely inseparable extension of `K`. Choose `t` with `t^q = x`.
   Injectivity of the iterated Frobenius (`def-weil-ring-frobenius`) shows that the
   basis elements lie in `L'(t)`. The tower law
   (`lem-weil-pbc-field-degree-multiplicativity`) makes `L'(t)/K(x)` finite.
6. The closure in `L` is the intersection with `L` of the closure `C` in `L'(t)`.
   By `lem-weil-pbc-noetherian-submodule-finite`, it suffices to show `C` finite.
7. Let `A` be the integral closure of `R` in `L'`. The element `t` is transcendental over
   `L'`, since otherwise `x = t^q` would be algebraic over `K`. The ring `A` is normal
   with fraction field `L'` by `lem-weil-pbc-integral-closure-finite-extension-normal`.
   Thus `A[t]` is normal with fraction field `L'(t)` by
   `lem-weil-pbc-polynomial-ring-normal-domain`. Its generators are integral over `R[x]`,
   so `A[t]` lies in `C`; normality gives the reverse inclusion.
8. The N-2 hypothesis makes `A` finite over `R`. If `a_j` generate `A`, the elements
   `a_j t^r` for `0 ≤ r < q` generate `A[t]` over `R[x]`, by division of exponents by
   `q` and `t^q = x`. Steps 6 and 4 finish positive characteristic, and steps 1 and 3
   finish the assertion. All closures and finiteness conditions use
   `def-weil-pbc-integral-closure` and `def-weil-finitely-generated-module`. -/
theorem isN2_polynomial (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : IsN2 R (FractionRing R)) :
    IsN2 (Polynomial R) (FractionRing (Polynomial R)) := by
  let A := integralClosure R (FractionRing R)
  let : Algebra (Polynomial R) (Polynomial A) := Polynomial.algebra R A
  let : Module.Finite R A := hR (FractionRing R)
  let : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  let : IsIntegrallyClosed A :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  have hinj : Function.Injective (algebraMap R A) := by
    intro r s hrs
    apply IsFractionRing.injective R (FractionRing R)
    exact congrArg (fun a : A ↦ (a : FractionRing R)) hrs
  have hA : IsN2 A (FractionRing A) :=
    isN2_of_finite_domain_extension R A (FractionRing R) (FractionRing A) hinj hR
  let : Module.Finite (Polynomial R) (Polynomial A) := finite_polynomial_extension R A
  apply isN2_of_finite_extension (Polynomial R) (Polynomial A)
    (FractionRing (Polynomial R)) (FractionRing (Polynomial A))
  · exact Polynomial.map_injective (algebraMap R A) hinj
  · exact isN2_polynomial_normal A hA
