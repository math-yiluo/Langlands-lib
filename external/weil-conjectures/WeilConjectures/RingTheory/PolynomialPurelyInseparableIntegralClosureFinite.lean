/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs

import WeilConjectures.RingTheory.PurelyInseparablePolynomialCover
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Purely inseparable integral closures over polynomial rings

Source: Stacks Project, Algebra, Lemma 10.161.13 (Tag 032O), positive-characteristic
part of the second assertion.
(blueprint: lem-weil-pbc-polynomial-purely-inseparable-closure-finite).
-/

@[expose] public section

universe u

set_option autoImplicit false

private theorem finite_adjoin_coefficients_and_integral
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    [IsNoetherianRing S] [Module.Finite R A]
    (g : A →ₐ[R] B) (t : B) (ht : IsIntegral S t) :
    Module.Finite S (Algebra.adjoin S (Set.range g ∪ {t})) := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R A).out
  let T := Algebra.adjoin S (g '' (s : Set A) ∪ {t})
  have hT : Module.Finite S T := Algebra.finite_adjoin_of_finite_of_isIntegral
    ((s.finite_toSet.image g).union (Set.finite_singleton t)) (by
      intro b hb
      rcases hb with ⟨a, _, rfl⟩ | hb
      · exact ((IsIntegral.of_finite R a).map g).tower_top
      · rcases Set.mem_singleton_iff.mp hb with rfl
        exact ht)
  have hrange : Set.range g ⊆ T := by
    rintro b ⟨a, rfl⟩
    have hle : Algebra.adjoin R (g '' (s : Set A)) ≤ T.restrictScalars R := by
      apply Algebra.adjoin_le
      intro y hy
      change y ∈ Algebra.adjoin S (g '' (s : Set A) ∪ {t})
      exact Algebra.subset_adjoin (Set.mem_union_left _ hy)
    apply hle
    rw [← AlgHom.map_adjoin, hs]
    exact ⟨a, trivial, rfl⟩
  have hle : Algebra.adjoin S (Set.range g ∪ {t}) ≤ T :=
    Algebra.adjoin_le (by
      intro b hb
      rcases hb with hb | hb
      · exact hrange hb
      · exact Algebra.subset_adjoin (Set.mem_union_right _ hb))
  exact Module.Finite.of_injective (Subalgebra.inclusion hle).toLinearMap
    (Subalgebra.inclusion_injective hle)

/-- For a Noetherian normal Japanese domain, the integral closure of its polynomial
ring in a finite purely inseparable extension of its fraction field is finite.
Source: Stacks Project, Algebra, Lemma 10.161.13 (Tag 032O), proof of the second assertion.
(blueprint: lem-weil-pbc-polynomial-purely-inseparable-closure-finite).

Proof: Write K = Frac(R) and x for the polynomial variable. Clearing coefficient
denominators identifies Frac(R[x]) with K(x): multiply a polynomial in K[x] by the
product of denominators of its finitely many coefficients to put it in R[x]. The
inclusion K → K(x) makes K have characteristic p as well. In an algebraic closure of
L choose a common q = p^e such that the q-th powers of a K(x)-basis of L lie in K(x).
Write those powers as quotients of polynomials. Adjoin to K the q-th roots of all
coefficients in these finitely many numerators and denominators, obtaining K'. The
monomials in these roots with exponents below q span K' over K: the corresponding
finite-dimensional subalgebra is a domain and thus a field: multiplication by a nonzero
element is an injective endomorphism of a finite-dimensional K-vector space, hence
surjective and takes some element to 1. Choose t with t^q = x.
The injectivity of the iterated Frobenius shows that every basis element lies in K'(t),
so L embeds in K'(t) over K(x). This last extension is finite by the tower law.
Let A be the integral closure of R in K'. It is finite over R by the Japanese hypothesis,
and is normal with fraction field K'. The element t is transcendental over K', since
otherwise x would be algebraic over K. Hence A[t] is a normal polynomial ring with
fraction field K'(t). The elements of A and t are integral over R[x], so A[t] is contained
in the integral closure C of R[x] in K'(t). Conversely each element of C is integral over
A[t], and normality forces it into A[t]. Thus C = A[t]. If a_j generate A over R, then
a_j t^r, for 0 ≤ r < q, generate C over R[x], by writing each exponent as qs+r and using
t^q = x. Finally the integral closure in L embeds as an R[x]-submodule of C; R[x] is
Noetherian, so that submodule is finite. This includes q = 1 and the trivial extension. -/
theorem finite_polynomial_purelyInseparable_integralClosure
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hR : IsN2 R (FractionRing R)) (p : ℕ) [Fact p.Prime]
    [CharP (FractionRing (Polynomial R)) p]
    (L : Type u) [Field L] [Algebra (FractionRing (Polynomial R)) L]
    [Algebra (Polynomial R) L] [IsScalarTower (Polynomial R) (FractionRing (Polynomial R)) L]
    [FiniteDimensional (FractionRing (Polynomial R)) L]
    [IsPurelyInseparable (FractionRing (Polynomial R)) L] :
    Module.Finite (Polynomial R) (integralClosure (Polynomial R) L) := by
  obtain ⟨E, hE, aKE, aRE, towerRE, finE, q, hq, f, hf⟩ :=
    exists_purelyInseparable_polynomial_cover R p L
  let A := integralClosure R E
  let B := Polynomial A
  let K := FractionRing B
  let φ : Polynomial R →+* B := Polynomial.eval₂RingHom
    (Polynomial.C.comp (algebraMap R A)) (Polynomial.X ^ q)
  let : Algebra (Polynomial R) B := φ.toAlgebra
  have towerPBK : IsScalarTower (Polynomial R) B K := inferInstance
  have towerRPB : IsScalarTower R (Polynomial R) B := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change Polynomial.C (algebraMap R A r) = φ (Polynomial.C r)
    simp [φ]
    rfl
  have finA : Module.Finite R A := hR E
  have normalA : IsIntegrallyClosed A :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  have normalB : IsIntegrallyClosed B := inferInstance
  have hφX : φ Polynomial.X = (Polynomial.X : B) ^ q := by simp [φ]
  have ht : IsIntegral (Polynomial R) (Polynomial.X : B) :=
    IsIntegral.of_pow hq (by
      rw [← hφX]
      exact isIntegral_algebraMap)
  let g : A →ₐ[R] B := IsScalarTower.toAlgHom R A B
  let T := Algebra.adjoin (Polynomial R) (Set.range g ∪ {Polynomial.X})
  have finT : Module.Finite (Polynomial R) T :=
    finite_adjoin_coefficients_and_integral g Polynomial.X ht
  have hT : T = ⊤ := by
    apply top_unique
    intro b hb
    clear hb
    induction b using Polynomial.induction_on' with
    | add b c hb hc => exact T.add_mem hb hc
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      apply T.mul_mem
      · exact Algebra.subset_adjoin (Set.mem_union_left _ ⟨a, rfl⟩)
      · exact T.pow_mem (Algebra.subset_adjoin (Set.mem_union_right _ rfl)) n
  have finB : Module.Finite (Polynomial R) B :=
    Module.Finite.of_surjective T.val.toLinearMap (by
      intro b
      exact ⟨⟨b, hT ▸ trivial⟩, rfl⟩)
  have finC : Module.Finite B (integralClosure B K) :=
    Module.Finite.equiv (IsIntegralClosure.equiv B B K (integralClosure B K)).toLinearEquiv
  have finPC : Module.Finite (Polynomial R) (integralClosure B K) :=
    Module.Finite.trans B (integralClosure B K)
  let f' : L →ₐ[Polynomial R] K :=
    { f with commutes' := hf }
  let j : integralClosure (Polynomial R) L →ₐ[Polynomial R]
      ((integralClosure B K).restrictScalars (Polynomial R)) :=
    (f'.comp (integralClosure (Polynomial R) L).val).codRestrict _ (by
      intro z
      exact ((z.property).map f').tower_top)
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    apply f.injective
    exact congrArg (fun z : integralClosure B K ↦ (z : K)) hab
  have finRestricted : Module.Finite (Polynomial R)
      ((integralClosure B K).restrictScalars (Polynomial R)) := finPC
  exact Module.Finite.of_injective j.toLinearMap hj
