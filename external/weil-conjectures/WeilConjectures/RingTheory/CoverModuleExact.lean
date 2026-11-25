/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Exactness of the Cech sequence for a module localization cover

Source: Stacks Project, Algebra, Lemma 00EK (label `lemma-cover-module`)
(blueprint: lem-weil-pbc-cover-module-exact).
-/

@[expose] public section

universe u v

namespace RingTheory

/-- Powers of a divisor of `h` act invertibly on `M_h`. This is the invertibility
needed in the notation step of Stacks Project, Algebra, Lemma 00EK, using the universal
property in Lemma 07K0 (blueprint: lem-weil-pbc-cover-module-exact).

Proof: write `h = a * b`. Multiplication by `h` is a unit endomorphism of `M_h`, by
`IsLocalizedModule.map_units`. The commuting endomorphisms given by `a` and `b` therefore
are units individually. Every element of `Submonoid.powers a` is a power of `a`, so its
endomorphism is a unit as well. No map or localization is defined anew here. -/
theorem localizationAway_map_units_of_dvd {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (a h : R) (ha : a ∣ h) :
    ∀ x : Submonoid.powers a,
      IsUnit (algebraMap R (Module.End R (LocalizedModule.Away h M)) (x : R)) := by
  obtain ⟨b, rfl⟩ := ha
  have hh := IsLocalizedModule.map_units
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M)
    (⟨a * b, Submonoid.mem_powers _⟩ : Submonoid.powers (a * b))
  rw [map_mul] at hh
  have hab : Commute
      (algebraMap R (Module.End R (LocalizedModule.Away (a * b) M)) a)
      (algebraMap R (Module.End R (LocalizedModule.Away (a * b) M)) b) :=
    (Commute.all a b).map _
  have hu := (hab.isUnit_mul_iff.mp hh).1
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := hx
  simpa only [map_pow] using hu.pow k

/-- The Cech equalizer statement for a finite principal-open cover of a module.
Source: Stacks Project, Algebra, Lemma 00EK (label `lemma-cover-module`)
(blueprint: lem-weil-pbc-cover-module-exact).

The local abbreviation `ρ` is Mathlib's `IsLocalizedModule.lift` of the localization map
`m ↦ m/1`; Lemma 07K0 characterizes it uniquely by sending `m/1` to `m/1`. For `h = a*b`,
it sends `m/a^e` to `b^e*m/(a*b)^e`. Finite products are the finite direct sums in the source.

Proof (the node's direct partition-of-unity proof, rather than the source's reduction
at maximal ideals):
1. The two canonical lifts send `m/1` to `m/1`, so `β α = 0`. Fraction representations,
   equality after multiplying by a power, and cancellation use
   `def-weil-pbc-module-localization-away`.
2. If every localization of `m` vanishes, `lem-weil-pbc-localized-span-eq-zero` gives
   `m = 0`. Equivalently choose a common annihilating exponent and express 1 as a linear
   combination of the powers using `lem-weil-pbc-span-pow-eq-top`.
3. Write the compatible sections as `s_i = x_i/f_i^e_i`; choose a common exponent `N`
   and replace each numerator by `m_i = f_i^(N-e_i)*x_i`.
4. Equality on each overlap gives an exponent `k_ij` annihilating
   `f_j^N*m_i - f_i^N*m_j` after multiplication by `(f_i*f_j)^k_ij`. A common exponent
   `K` gives `f_i^K*f_j^(N+K)*m_i = f_i^(N+K)*f_j^K*m_j` for every pair.
5. By `lem-weil-pbc-span-pow-eq-top`, choose coefficients `a_i` with
   `sum a_i*f_i^(N+K) = 1`. Set `m = sum a_i*f_i^K*m_i`. Step 4 gives
   `f_j^(N+K)*m = f_j^K*m_j`, so in `M_(f_j)` one has `m/1 = m_j/f_j^N = s_j`.
6. Two glued elements have difference zero in every localization, hence are equal by
   step 2. If the cover is empty, its span hypothesis forces the zero ring and therefore
   the zero module; both clauses still hold without taking a maximum of an empty set. -/
theorem coverModuleExact {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
    [Module R M] (n : ℕ) (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = ⊤) :
    let ρ := fun (a h : R) (ha : a ∣ h) =>
      IsLocalizedModule.lift (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
        (localizationAway_map_units_of_dvd (M := M) a h ha)
    (∀ m : M, (∀ i : Fin n,
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m = 0) → m = 0) ∧
    (∀ (s : ∀ i : Fin n, LocalizedModule.Away (f i) M),
      (∀ i j : Fin n,
        ρ (f i) (f i * f j) (dvd_mul_right (f i) (f j)) (s i) =
          ρ (f j) (f i * f j) (dvd_mul_left (f j) (f i)) (s j)) →
      ∃! m : M, ∀ i : Fin n,
        LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m = s i) := by
  classical
  dsimp only
  let loc (a : R) := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  let ρ := fun (a h : R) (ha : a ∣ h) ↦
    IsLocalizedModule.lift (Submonoid.powers a) (loc a) (loc h)
      (localizationAway_map_units_of_dvd (M := M) a h ha)
  have hinj (x y : M) (heq : ∀ i, loc (f i) x = loc (f i) y) : x = y := by
    apply Module.eq_of_isLocalized_span (Set.range f) hspan
      (fun r ↦ LocalizedModule.Away r.1 M) (fun r ↦ loc r.1) x y
    rintro ⟨r, ⟨i, rfl⟩⟩
    exact heq i
  refine ⟨fun m hm ↦ hinj m 0 (by simpa [loc] using hm), ?_⟩
  intro s hs
  change ∀ i j, ρ (f i) (f i * f j) (dvd_mul_right (f i) (f j)) (s i) =
    ρ (f j) (f i * f j) (dvd_mul_left (f j) (f i)) (s j) at hs
  have hrep (i : Fin n) : ∃ e : ℕ, ∃ m : M, (f i)^e • s i = loc (f i) m := by
    obtain ⟨⟨m, t⟩, ht⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (loc (f i)) (s i)
    obtain ⟨e, he⟩ := t.2
    exact ⟨e, m, by simpa only [← he, Submonoid.smul_def] using ht⟩
  choose e x hx using hrep
  let N := Finset.univ.sup e
  let m (i : Fin n) := (f i)^(N - e i) • x i
  have hm (i : Fin n) : (f i)^N • s i = loc (f i) (m i) := by
    dsimp only [m]
    rw [map_smul, ← hx, smul_smul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ i))]
  have heq (i j : Fin n) : ∃ k : ℕ,
      (f i * f j)^k • ((f j)^N • m i) =
        (f i * f j)^k • ((f i)^N • m j) := by
    have hloc : loc (f i * f j) ((f j)^N • m i) =
        loc (f i * f j) ((f i)^N • m j) := by
      rw [(loc (f i * f j)).map_smul ((f j)^N) (m i),
        (loc (f i * f j)).map_smul ((f i)^N) (m j)]
      rw [← IsLocalizedModule.lift_apply (Submonoid.powers (f i)) (loc (f i))
        (loc (f i * f j)) (localizationAway_map_units_of_dvd (M := M) _ _
          (dvd_mul_right (f i) (f j))) (m i)]
      rw [← IsLocalizedModule.lift_apply (Submonoid.powers (f j)) (loc (f j))
        (loc (f i * f j)) (localizationAway_map_units_of_dvd (M := M) _ _
          (dvd_mul_left (f j) (f i))) (m j)]
      change (f j)^N • ρ (f i) (f i * f j) (dvd_mul_right (f i) (f j)) (loc (f i) (m i)) =
        (f i)^N • ρ (f j) (f i * f j) (dvd_mul_left (f j) (f i)) (loc (f j) (m j))
      rw [← hm, ← hm, map_smul, map_smul, hs, smul_comm]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (f i * f j))
      (loc (f i * f j))).mp hloc
    obtain ⟨k, hk⟩ := t.2
    exact ⟨k, by simpa only [← hk, Submonoid.smul_def] using ht⟩
  choose k hk using heq
  let K := Finset.univ.sup fun p : Fin n × Fin n ↦ k p.1 p.2
  have hK (i j : Fin n) :
      (f i * f j)^K • ((f j)^N • m i) =
        (f i * f j)^K • ((f i)^N • m j) := by
    have hle : k i j ≤ K := Finset.le_sup
      (f := fun p : Fin n × Fin n ↦ k p.1 p.2) (Finset.mem_univ (i, j))
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, mul_smul, hk]
  let L := K + N
  let y (i : Fin n) := (f i)^K • m i
  have hy (i : Fin n) : (f i)^L • s i = loc (f i) (y i) := by
    dsimp only [L, y]
    rw [pow_add, mul_smul, hm]
    exact ((loc (f i)).map_smul ((f i)^K) (m i)).symm
  have hxy (i j : Fin n) : (f j)^L • y i = (f i)^L • y j := by
    dsimp only [L, y]
    have h := hK i j
    simp only [smul_smul] at h ⊢
    calc
      _ = ((f i * f j)^K * (f j)^N) • m i := by congr 1; rw [mul_pow, pow_add]; ring
      _ = ((f i * f j)^K * (f i)^N) • m j := h
      _ = _ := by congr 1; rw [mul_pow, pow_add]; ring
  have hpow : Ideal.span (Set.range (fun i ↦ (f i)^L)) = ⊤ := by
    have h := Ideal.span_pow_eq_top (Set.range f) hspan L
    rw [← Set.range_comp] at h
    exact h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    ((Ideal.eq_top_iff_one _).mp hpow)
  have hglue : ∀ j, loc (f j) (∑ i, c i • y i) = s j := by
    intro j
    apply IsLocalizedModule.smul_injective (loc (f j))
      (⟨(f j)^L, ⟨L, rfl⟩⟩ : Submonoid.powers (f j))
    change (f j)^L • loc (f j) (∑ i, c i • y i) = (f j)^L • s j
    rw [← map_smul, Finset.smul_sum, hy]
    congr 1
    calc
      _ = ∑ i, (c i * (f i)^L) • y j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_comm ((f j)^L) (c i), hxy i j, smul_smul]
      _ = y j := by
        rw [← Finset.sum_smul]
        have hc' : ∑ i, c i * (f i)^L = 1 := by
          simpa only [smul_eq_mul] using hc
        rw [hc', one_smul]
  exact ⟨∑ i, c i • y i, hglue, fun z hz ↦
    hinj z _ (fun i ↦ (hz i).trans (hglue i).symm)⟩

end RingTheory
