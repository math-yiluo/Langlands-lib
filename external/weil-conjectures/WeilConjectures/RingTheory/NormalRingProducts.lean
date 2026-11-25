/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Normal rings, finite products and total rings of fractions

A commutative ring `R` is *normal* if `R_p` is an integrally closed domain for every prime `p`
(Stacks, Tag 037B); we express this with `IsDomain` and `IsIntegrallyClosed` of
`Localization.AtPrime p`. The total ring of fractions of `R` is `FractionRing R`.

## Main statements

- `Pi.isDomain_and_isIntegrallyClosed_localization`: a finite product of normal rings is
  normal (Stacks, Tag 0CYA).
- `Pi.isIntegral_iff`, `integralClosure_pi`: integral closure commutes with finite products
  (Stacks, Tags 0CY8, 0CY9).
- `exists_algebraMap_eq_of_isIntegral_of_normal`: a normal ring is integrally closed in its
  total ring of fractions (Stacks, Tag 034M).
- `IsIntegral.exists_mul_eq_algebraMap_of_atPrime`: integral total fractions have local
  denominators at primes with normal localization (Stacks, Tag 031S).
- `exists_ringEquiv_pi_isDomain_of_isIntegrallyClosedIn`: a reduced ring with finitely many
  minimal primes which is integrally closed in its total ring of fractions is a finite product
  of domains (Stacks, Tag 030C).
-/

@[expose] public section

universe w u v

namespace Pi

/-- A finite product of normal rings is normal: if every localization of every `R i` at a prime
is an integrally closed domain, then so is every localization of `Π i, R i` at a prime.
(blueprint: `lem-weil-pbc-finite-product-normal`) -/
theorem isDomain_and_isIntegrallyClosed_localization {I : Type u} [Finite I] (R : I → Type v)
    [∀ i : I, CommRing (R i)]
    (hR : ∀ (i : I) (p : Ideal (R i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (p : Ideal (∀ i : I, R i)) [hp : p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  obtain ⟨i, q, hq⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq (⟨p, hp⟩ : PrimeSpectrum (∀ i, R i))
  have hpq : q.asIdeal.comap (Pi.evalRingHom R i) = p :=
    congrArg PrimeSpectrum.asIdeal hq
  subst p
  obtain ⟨hd, hc⟩ := hR i q.asIdeal
  let e := RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
    (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
  exact ⟨e.toMulEquiv.isDomain_iff.mpr hd, IsIntegrallyClosed.of_equiv e.symm⟩

/-- An element of a finite product of algebras is integral if and only if all its coordinates
are (Stacks, Tag 0CY8). -/
theorem isIntegral_iff {I : Type w} [Finite I] {R : I → Type u} {S : I → Type v}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)] (x : ∀ i, S i) :
    IsIntegral (∀ i, R i) x ↔ ∀ i, IsIntegral (R i) (x i) := by
  classical
  constructor
  · intro hx i
    exact hx.map_of_comp_eq (Pi.evalRingHom R i) (Pi.evalRingHom S i) rfl
  · intro hx
    let _ : Fintype I := Fintype.ofFinite I
    choose p hp he using hx
    let D := Finset.univ.sup fun i ↦ (p i).natDegree
    have hd (i : I) : (p i).natDegree ≤ D := Finset.le_sup (f := fun i ↦ (p i).natDegree)
      (Finset.mem_univ i)
    let q (i : I) := Polynomial.X ^ (D - (p i).natDegree) * p i
    have hqdeg (i : I) : (q i).natDegree ≤ D := by
      calc
        (q i).natDegree ≤ (D - (p i).natDegree) + (p i).natDegree :=
          (Polynomial.natDegree_mul_le).trans
            (Nat.add_le_add_right (Polynomial.natDegree_X_pow_le _) _)
        _ = D := Nat.sub_add_cancel (hd i)
    have hqcoeff (i : I) : (q i).coeff D = 1 := by
      simp only [q, Polynomial.coeff_X_pow_mul']
      rw [ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self (hd i)]
      exact (hp i).coeff_natDegree
    let Q := (Polynomial.piEquiv R).symm q
    have hmap (i : I) : Q.map (Pi.evalRingHom R i) = q i :=
      congrFun ((Polynomial.piEquiv R).apply_symm_apply q) i
    have hc (n : ℕ) (i : I) : Q.coeff n i = (q i).coeff n := by
      simpa using congrArg (fun t ↦ t.coeff n) (hmap i)
    refine ⟨Q, ?_, ?_⟩
    · apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one D
      · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro n hn
        funext i
        rw [hc, Polynomial.coeff_eq_zero_of_natDegree_lt ((hqdeg i).trans_lt hn)]
        rfl
      · funext i
        exact (hc D i).trans (hqcoeff i)
    · funext i
      have hev : (q i).eval₂ (algebraMap (R i) (S i)) (x i) = 0 := by
        simp [q, Polynomial.eval₂_mul, he i]
      change (Pi.evalRingHom S i) (Q.eval₂ (algebraMap (∀ i, R i) (∀ i, S i)) x) = 0
      rw [Polynomial.hom_eval₂]
      have hcmap : (Pi.evalRingHom S i).comp (algebraMap (∀ i, R i) (∀ i, S i)) =
          (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i) := rfl
      rw [hcmap, ← Polynomial.eval₂_map, hmap]
      exact hev

end Pi

/-- **Integral closure commutes with finite products.** For ring maps `φ i : R i →+* S i`, the
integral closure of `Π R i` in `Π S i` is the product of the integral closures of `R i` in
`S i`; if all `φ i` are injective, `Π R i` is integrally closed in `Π S i` if and only if every
`R i` is integrally closed in `S i`.
(blueprint: `lem-weil-pbc-finite-product-integral-closure`) -/
theorem integralClosure_pi {I : Type w} [Finite I]
    (R : I → Type u) (S : I → Type v) [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (φ : ∀ i, R i →+* S i) :
    letI : ∀ i, Algebra (R i) (S i) := fun i ↦ (φ i).toAlgebra
    (integralClosure (∀ i, R i) (∀ i, S i)).toSubring =
        ⨅ i, (integralClosure (R i) (S i)).toSubring.comap (Pi.evalRingHom S i) ∧
      ((∀ i, Function.Injective (φ i)) →
        (IsIntegrallyClosedIn (∀ i, R i) (∀ i, S i) ↔
          ∀ i, IsIntegrallyClosedIn (R i) (S i))) := by
  classical
  let : ∀ i, Algebra (R i) (S i) := fun i ↦ (φ i).toAlgebra
  have hint (x : ∀ i, S i) := Pi.isIntegral_iff (R := R) (S := S) x
  constructor
  · ext x
    simpa only [Subring.mem_iInf, Subring.mem_comap, Subalgebra.mem_toSubring,
      mem_integralClosure_iff, Pi.evalRingHom_apply] using hint x
  · intro hinj
    rw [isIntegrallyClosedIn_iff]
    constructor
    · rintro ⟨_, hcl⟩ i
      rw [isIntegrallyClosedIn_iff]
      refine ⟨hinj i, ?_⟩
      intro x hx
      let y : ∀ j, S j := Pi.single i x
      have hy : IsIntegral (∀ j, R j) y := by
        apply (hint y).mpr
        intro j
        by_cases h : j = i
        · subst j
          simpa [y] using hx
        · simpa [y, Pi.single_eq_of_ne h] using (isIntegral_zero : IsIntegral (R j) (0 : S j))
      obtain ⟨r, hr⟩ := hcl hy
      refine ⟨r i, ?_⟩
      have hri : algebraMap (R i) (S i) (r i) = y i := congrFun hr i
      simpa [y] using hri
    · intro hcl
      refine ⟨?_, ?_⟩
      · intro a b hab
        funext i
        exact hinj i (congrFun hab i)
      · intro x hx
        have hc (i : I) : ∃ r : R i, algebraMap (R i) (S i) r = x i :=
          ((isIntegrallyClosedIn_iff.mp (hcl i)).2 ((hint x).mp hx i))
        choose r hr using hc
        exact ⟨r, funext hr⟩

/-- **A normal ring is integrally closed in its total ring of fractions.** If every localization
of `R` at a prime is an integrally closed domain, then every element of `FractionRing R` which is
integral over `R` comes from `R`.
(blueprint: `lem-weil-pbc-normal-ring-integrally-closed-total`) -/
theorem exists_algebraMap_eq_of_isIntegral_of_normal (R : Type u) [CommRing R]
    (hnormal : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (x : FractionRing R) (hx : IsIntegral R x) :
    ∃ r : R, algebraMap R (FractionRing R) r = x := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  have ha : a ∈ Ideal.span ({(s : R)} : Set R) := by
    apply Ideal.mem_of_localization_maximal
    intro p hp
    let : p.IsMaximal := hp
    let A := Localization.AtPrime p
    let K := FractionRing A
    let : IsDomain A := (hnormal p).1
    let : IsIntegrallyClosed A := (hnormal p).2
    let g : R →ₐ[R] K := Algebra.ofId R K
    have hu : ∀ t : nonZeroDivisors R, IsUnit (g t) := by
      intro t
      have ht : algebraMap R A t ∈ nonZeroDivisors A :=
        IsLocalization.nonZeroDivisors_le_comap p.primeCompl A t.2
      simpa only [g, Algebra.ofId_apply, IsScalarTower.algebraMap_apply R A K] using
        IsLocalization.map_units K (⟨algebraMap R A t, ht⟩ : nonZeroDivisors A)
    let f : FractionRing R →ₐ[R] K := IsLocalization.liftAlgHom hu
    have hi : IsIntegral A (f (IsLocalization.mk' (FractionRing R) a s)) :=
      (hx.map f).tower_top
    obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff K).mp inferInstance hi
    have he : algebraMap R A a = b * algebraMap R A s := by
      apply IsFractionRing.injective A K
      have hs := congrArg f (IsLocalization.mk'_spec (FractionRing R) a s)
      simpa only [map_mul, AlgHom.commutes, ← hb, g,
        IsScalarTower.algebraMap_apply R A K, map_mul] using hs.symm
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨b, he.trans (mul_comm _ _)⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨r, IsLocalization.eq_mk'_of_mul_eq ?_⟩
  exact (mul_comm _ _).trans hr.symm

/-- **Local denominators of integral total fractions.** If `x` in the total ring of fractions of
`R` is integral over `R` and `p` is a prime with `R_p` an integrally closed domain, then
`s * x = a` for some `s ∉ p` and `a ∈ R`.
(blueprint: `lem-weil-pbc-integral-total-fraction-local-denominator`) -/
theorem IsIntegral.exists_mul_eq_algebraMap_of_atPrime
    {R : Type u} [CommRing R] {x : FractionRing R} (hx : IsIntegral R x)
    (p : Ideal R) [p.IsPrime] [IsDomain (Localization.AtPrime p)]
    [IsIntegrallyClosed (Localization.AtPrime p)] :
    ∃ s : R, s ∉ p ∧ ∃ a : R,
      algebraMap R (FractionRing R) s * x = algebraMap R (FractionRing R) a := by
  let A := Localization.AtPrime p
  let K := FractionRing A
  have hnz (b : nonZeroDivisors R) : algebraMap R A b ≠ 0 := by
    intro hb
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl A b).mp hb
    have hsz : (s : R) = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff b.prop).mp hs
    exact s.prop (hsz ▸ p.zero_mem)
  have hunits (b : nonZeroDivisors R) : IsUnit (algebraMap R K b) := by
    apply isUnit_iff_ne_zero.mpr
    rw [IsScalarTower.algebraMap_apply R A K]
    exact (map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr (hnz b)
  let f : FractionRing R →ₐ[R] K :=
    IsLocalization.liftAlgHom (M := nonZeroDivisors R) (f := Algebra.ofId R K) hunits
  have hint : IsIntegral A (f x) := (hx.map f).tower_top
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff K).mp inferInstance hint
  obtain ⟨c, t, ht⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
  have hzt : z * algebraMap R A t = algebraMap R A c := by
    rw [← ht]
    exact IsLocalization.mk'_spec A c t
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have heq : algebraMap R A ((t : R) * a) = algebraMap R A ((b : R) * c) := by
    apply IsFractionRing.injective A K
    simp only [map_mul, ← IsScalarTower.algebraMap_apply R A K]
    have hab' := congrArg f hab
    simp only [map_mul, AlgHom.commutes] at hab'
    have hzt' := congrArg (algebraMap A K) hzt
    simp only [map_mul, ← IsScalarTower.algebraMap_apply R A K, hz] at hzt'
    calc
      algebraMap R K t * algebraMap R K a =
          algebraMap R K t * (f x * algebraMap R K b) := by rw [hab']
      _ = algebraMap R K b * (f x * algebraMap R K t) := by ring
      _ = algebraMap R K b * algebraMap R K c := by rw [hzt']
  obtain ⟨u, hu⟩ := IsLocalization.exists_of_eq (M := p.primeCompl) heq
  refine ⟨(u : R) * t, p.primeCompl.mul_mem u.prop t.prop, (u : R) * c, ?_⟩
  apply (IsLocalization.map_units (FractionRing R) b).mul_left_cancel
  simp only [map_mul]
  calc
    algebraMap R (FractionRing R) b *
        (algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) t * x) =
        algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) t *
          (x * algebraMap R (FractionRing R) b) := by ring
    _ = algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) t *
        algebraMap R (FractionRing R) a := by rw [hab]
    _ = algebraMap R (FractionRing R) (u * (t * a)) := by simp [map_mul, mul_assoc]
    _ = algebraMap R (FractionRing R) (u * (b * c)) := by rw [hu]
    _ = algebraMap R (FractionRing R) b *
        (algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) c) := by
          simp only [map_mul]
          ring


private theorem isCoprime_of_mem_minimalPrimes_of_isIntegrallyClosedIn
    (R : Type u) [CommRing R] [IsReduced R]
    (hfinite : (minimalPrimes R).Finite)
    (hclosed : IsIntegrallyClosedIn R (FractionRing R))
    (p q : Ideal R) (hp : p ∈ minimalPrimes R) (hq : q ∈ minimalPrimes R)
    (hpq : p ≠ q) : IsCoprime p q := by
  classical
  let S : Finset (Ideal R) := hfinite.toFinset.erase p
  have hS (r : Ideal R) : r ∈ S ↔ r ∈ minimalPrimes R ∧ r ≠ p := by
    simp only [S, Finset.mem_erase, Set.Finite.mem_toFinset, ne_eq]
    tauto
  have hnot (r : Ideal R) (hr : r ∈ S) : ¬p ≤ r := by
    intro hpr
    have heq : p = r := le_antisymm hpr (((hS r).mp hr).1.2 ⟨hp.isPrime, bot_le⟩ hpr)
    exact ((hS r).mp hr).2 heq.symm
  have havoid : ¬(p : Set R) ⊆ ⋃ r ∈ (S : Set (Ideal R)), (r : Set R) := by
    intro h
    obtain ⟨r, hr, hpr⟩ := (Ideal.subset_union_prime p p
      (fun r hr _ _ ↦ ((hS r).mp hr).1.isPrime)).mp h
    exact hnot r hr hpr
  obtain ⟨b, hbp, hb⟩ := Set.not_subset.mp havoid
  have hbnot (r : Ideal R) (hr : r ∈ S) : b ∉ r := by
    intro hbr
    exact hb (Set.mem_iUnion₂.mpr ⟨r, hr, hbr⟩)
  have hpn : ¬(S.inf id) ≤ p := by
    intro h
    obtain ⟨r, hr, hrp⟩ := hp.isPrime.inf_le'.mp h
    have heq : r = p := le_antisymm hrp (hp.2
      ⟨((hS r).mp hr).1.isPrime, bot_le⟩ hrp)
    exact ((hS r).mp hr).2 heq
  obtain ⟨a, ha, hap⟩ := Set.not_subset.mp hpn
  have hamem (r : Ideal R) (hr : r ∈ S) : a ∈ r := (show S.inf id ≤ r from Finset.inf_le hr) ha
  have hab : a * b = 0 := by
    have hz : a * b ∈ sInf (minimalPrimes R) := by
      rw [Ideal.mem_sInf]
      intro r hr
      by_cases hrp : r = p
      · subst r
        exact p.mul_mem_left a hbp
      · exact r.mul_mem_right b (hamem r ((hS r).mpr ⟨hr, hrp⟩))
    simpa only [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced,
      Ideal.mem_bot] using hz
  have hs : a + b ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    by_contra hc0
    have hcunion : a + b ∈ ⋃ r ∈ minimalPrimes R, (r : Set R) := by
      rw [Ideal.iUnion_minimalPrimes, Ideal.radical_bot_of_isReduced]
      exact ⟨c, hc0, by simpa [mul_comm] using hc⟩
    obtain ⟨r, hr, hsr⟩ := Set.mem_iUnion₂.mp hcunion
    by_cases hrp : r = p
    · subst r
      exact hap (p.add_mem_iff_left hbp |>.mp hsr)
    · exact hbnot r ((hS r).mpr ⟨hr, hrp⟩)
        (r.add_mem_iff_right (hamem r ((hS r).mpr ⟨hr, hrp⟩)) |>.mp hsr)
  let s : nonZeroDivisors R := ⟨a + b, hs⟩
  let x : FractionRing R := IsLocalization.mk' (FractionRing R) a s
  have hxs : x * algebraMap R (FractionRing R) (a + b) =
      algebraMap R (FractionRing R) a := IsLocalization.mk'_spec _ a s
  have hidem : x * x = x := by
    apply (IsLocalization.map_units (FractionRing R) s).mul_left_inj.mp
    apply (IsLocalization.map_units (FractionRing R) s).mul_left_inj.mp
    calc
      (x * x * algebraMap R (FractionRing R) (a + b)) *
          algebraMap R (FractionRing R) (a + b) =
          (x * algebraMap R (FractionRing R) (a + b)) ^ 2 := by ring
      _ = algebraMap R (FractionRing R) (a * a) := by rw [hxs, pow_two, map_mul]
      _ = algebraMap R (FractionRing R) (a * (a + b)) := by
        congr 1
        rw [mul_add, hab, add_zero]
      _ = (x * algebraMap R (FractionRing R) (a + b)) *
          algebraMap R (FractionRing R) (a + b) := by rw [hxs, map_mul]
  have hxint : IsIntegral R x := by
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C (1 : R)),
      Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      map_one, mul_sub, mul_one, hidem, sub_self]
  obtain ⟨e, he⟩ := (isIntegrallyClosedIn_iff.mp hclosed).2 hxint
  have hes : e * (a + b) = a := by
    apply IsFractionRing.injective R (FractionRing R)
    simpa only [map_mul, he] using hxs
  have heother : (1 - e) * (a + b) = b := by
    calc
      (1 - e) * (a + b) = (a + b) - e * (a + b) := by ring
      _ = b := by rw [hes]; ring
  have heq : e ∈ q := by
    have hqs : a + b ∉ q := by
      intro h
      exact hbnot q ((hS q).mpr ⟨hq, hpq.symm⟩)
        (q.add_mem_iff_right (hamem q ((hS q).mpr ⟨hq, hpq.symm⟩)) |>.mp h)
    have hm : e * (a + b) ∈ q := hes.symm ▸ hamem q ((hS q).mpr ⟨hq, hpq.symm⟩)
    exact (hq.isPrime.mem_or_mem hm).resolve_right hqs
  have hep : 1 - e ∈ p := by
    have hps : a + b ∉ p := by
      intro h
      exact hap (p.add_mem_iff_left hbp |>.mp h)
    have hm : (1 - e) * (a + b) ∈ p := heother.symm ▸ hbp
    exact (hp.isPrime.mem_or_mem hm).resolve_right hps
  exact Ideal.isCoprime_iff_exists.mpr ⟨1 - e, hep, e, heq, by ring⟩

/-- **Domain decomposition.** A reduced ring with finitely many minimal primes which is integrally
closed in its total ring of fractions is isomorphic to a finite product of domains.
(blueprint: `lem-weil-pbc-integrally-closed-reduced-finite-domain-decomposition`) -/
theorem exists_ringEquiv_pi_isDomain_of_isIntegrallyClosedIn
    (R : Type u) [CommRing R] [IsReduced R]
    (hfinite : (minimalPrimes R).Finite)
    (hclosed : IsIntegrallyClosedIn R (FractionRing R)) :
    ∃ (n : ℕ) (A : Fin n → CommRingCat.{u}),
      (∀ i : Fin n, IsDomain (A i)) ∧ Nonempty (R ≃+* (∀ i : Fin n, A i)) := by
  classical
  let := hfinite.fintype
  let n := Fintype.card (minimalPrimes R)
  let e : Fin n ≃ minimalPrimes R := (Fintype.equivFin (minimalPrimes R)).symm
  let P : Fin n → Ideal R := fun i ↦ (e i).val
  have hp (i : Fin n) : (P i).IsPrime := (e i).property.isPrime
  have hzero : (⨅ i, P i) = ⊥ := by
    have heq : (⨅ i, P i) = sInf (minimalPrimes R) := by
      apply le_antisymm
      · apply le_sInf
        intro p hpm
        obtain ⟨i, hi⟩ := e.surjective ⟨p, hpm⟩
        exact (iInf_le P i).trans_eq (congrArg Subtype.val hi)
      · apply le_iInf
        intro i
        exact sInf_le (e i).property
    rw [heq, Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced]
  have hcop : Pairwise (fun i j ↦ IsCoprime (P i) (P j)) := by
    intro i j hij
    apply isCoprime_of_mem_minimalPrimes_of_isIntegrallyClosedIn R hfinite hclosed (P i) (P j)
      (e i).property (e j).property
    intro h
    exact hij (e.injective (Subtype.ext h))
  let A : Fin n → CommRingCat.{u} := fun i ↦ CommRingCat.of (R ⧸ P i)
  refine ⟨n, A, ?_, ?_⟩
  · intro i
    let : (P i).IsPrime := hp i
    exact inferInstanceAs (IsDomain (R ⧸ P i))
  · exact ⟨(RingEquiv.quotientBot R).symm.trans
      ((Ideal.quotEquivOfEq hzero.symm).trans
        (Ideal.quotientInfRingEquivPiQuotient P hcop))⟩
