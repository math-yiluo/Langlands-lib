/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Data.Finset.Union

import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import WeilConjectures.RingTheory.PowerSeriesSubringFiniteBasis
import WeilConjectures.RingTheory.PowerSeriesSubringIntersection

/-!
# Subfields of the fraction field of a power-series polynomial ring

Source: Stacks Project, More on Algebra, Lemmas 07P5 and 07P4
(blueprint: lem-weil-pbc-power-series-ring-subfields).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

attribute [local instance] ZMod.algebra

namespace RingTheory

open Classical in
/-- The subfields cut out by a p-basis in a power-series polynomial ring.
Source: Stacks Project, More on Algebra, Lemmas 07P5 and 07P4
(blueprint: lem-weil-pbc-power-series-ring-subfields).

The ring A is written out as `MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)`.
The families `kJ`, `AJ`, and `KJ` are specified by exact defining conditions:
field generation, coefficients supported on p-divisible exponents, and quotients.
No finiteness or intersection conclusion is assumed.

Proof (the eight steps of the node):
1. A is a domain by `lem-weil-pbc-power-series-domain` and
   `lem-weil-pbc-polynomial-ring-domain`. Its fraction map is injective. Quotients
   of elements of a subring form a subfield, since nonzero denominators multiply.
2. Expand h in polynomial y-monomials with power-series coefficients. Addition
   is coefficientwise and multiplication is convolution. The coefficient condition
   defining AJ contains 1 and is closed under addition, negatives and multiplication:
   sums of p-divisible exponents remain p-divisible and kJ is a subfield.
3. The p-basis monomials off J span kJ over k^p: this span is a ring, and each
   element lies in a finite-dimensional subring, where multiplication by a nonzero
   element is bijective, giving its inverse. Splitting monomial supports into J
   and its complement gives a kJ-basis of k indexed by bounded monomials on J.
   Uniqueness of p-basis coordinates gives intersection_J kJ = k^p. Enlarging J
   removes generators, so kJ is decreasing.
4. Divide every x- and y-exponent by p with remainder. Group the coefficients
   using the kJ-basis from step 3. This gives the finite AJ-basis t^E x^e y^g,
   with E supported on J and all exponents below p. Coefficient comparison proves
   independence. Thus A is finite over AJ (`def-weil-finitely-generated-module`).
5. By `lem-weil-pbc-power-series-frobenius-coefficientwise`, Frobenius raises
   coefficients to p-th powers and multiplies exponents by p. Conversely, taking
   coefficient roots gives a p-th root of every element supported on p-divisible
   exponents with coefficients in k^p. Hence a^p and b^p lie in every AJ, giving
   (a/b)^p in every KJ.
6. If h in A maps into KJ, clear its denominator to get c*h=a for a,c in AJ,
   c nonzero. Apply the AJ-linear basis coordinate at the basis vector 1.
   It gives c*coordinate(h)=a; cancelling c proves h=coordinate(h) in AJ.
   Thus A intersect KJ = AJ.
7. Write z in every KJ as f/b^p, with f in A and b nonzero. Since b^p lies in
   every AJ, step 6 puts f in every AJ. Step 3 puts its coefficients in k^p,
   and step 5 gives f = h^p. Thus z = (h/b)^p, proving the intersection equality.
8. The generators of kJ for J union J' lie in both smaller fields. The coefficient
   conditions imply the same inclusions for AJ, and taking quotients gives the
   required inclusion for KJ. -/
theorem iInter_frobenius_subfields_mvPolynomial_mvPowerSeries
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k)
    (hpb : ∃ b : Module.Basis
      {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k => x ^ p))) k,
      ∀ E, b E = (E : I →₀ ℕ).prod (fun i e => t i ^ e))
    (n m : ℕ)
    (K : Type v) [Field K]
    [Algebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    [IsFractionRing (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    (kJ : Finset I → Subfield k)
    (hkJ : ∀ J, kJ J = Subfield.closure
      (Set.range (fun x : k => x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x}))
    (AJ : Finset I → Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hAJ : ∀ J f, f ∈ AJ J ↔
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ∈ kJ J ∧
        (MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j)))
    (KJ : Finset I → Subfield K)
    (hKJ : ∀ J z, z ∈ KJ J ↔
      ∃ a b : AJ J, (b : MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) ≠ 0 ∧
        z = algebraMap (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K a /
          algebraMap (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K b) :
    (∀ J : Finset I,
      Module.Finite (AJ J) (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) ∧
      (∀ J : Finset I, Set.range (fun x : K => x ^ p) ⊆ (KJ J : Set K)) ∧
      (Set.range (fun x : K => x ^ p) = ⋂ J : Finset I, (KJ J : Set K)) ∧
      (∀ J J' : Finset I, KJ (J ∪ J') ≤ KJ J ⊓ KJ J') := by
  classical
  let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
  have hroot := powerSeriesSubringIntersection p k I t hpb n m kJ hkJ AJ hAJ
  have hpower (a : A) (J : Finset I) : a ^ p ∈ AJ J :=
    (hroot (a ^ p)).mpr ⟨a, rfl⟩ J
  have hbasis (J : Finset I) :=
    powerSeriesSubringFiniteBasis p k I t hpb n m J (kJ J) (hkJ J) (AJ J) (hAJ J)
  have hfinite : ∀ J : Finset I, Module.Finite (AJ J) A := by
    intro J
    obtain ⟨d, b, i, hi⟩ := hbasis J
    exact Module.Finite.of_basis b
  have hinj := IsFractionRing.injective A K
  have hmap (J : Finset I) (a : A) (ha : a ∈ AJ J) :
      algebraMap A K a ∈ KJ J := by
    apply (hKJ J _).mpr
    refine ⟨⟨a, ha⟩, 1, one_ne_zero, ?_⟩
    change algebraMap A K a = algebraMap A K a / algebraMap A K (1 : A)
    rw [map_one, div_one]
  have hpow : ∀ J : Finset I, Set.range (fun x : K => x ^ p) ⊆ (KJ J : Set K) := by
    rintro J _ ⟨z, rfl⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A z
    change (algebraMap A K a / algebraMap A K b) ^ p ∈ KJ J
    rw [div_pow, ← map_pow, ← map_pow]
    exact (KJ J).div_mem (hmap J _ (hpower a J)) (hmap J _ (hpower b J))
  have hsaturated (J : Finset I) (f : A) (hf : algebraMap A K f ∈ KJ J) :
      f ∈ AJ J := by
    obtain ⟨a, c, hc, heq⟩ := (hKJ J _).mp hf
    have hcn : algebraMap A K (c : A) ≠ 0 := fun h => hc (hinj (by simpa using h))
    have hmul : (c : A) * f = (a : A) := by
      apply hinj
      simpa only [map_mul, mul_comm] using (eq_div_iff hcn).mp heq
    obtain ⟨d, b, i, hi⟩ := hbasis J
    have hrepr_one : b.repr (1 : A) i = 1 := by
      rw [← hi, b.repr_self]
      simp
    have hrepr : c * b.repr f i = a := by
      have hh := congrArg (fun x : A => b.repr x i) hmul
      have ha : (a : A) = a • (1 : A) := by
        change (a : A) = (a : A) * 1
        exact (mul_one _).symm
      rw [ha] at hh
      change b.repr (c • f) i = b.repr (a • (1 : A)) i at hh
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, hrepr_one, mul_one] using hh
    have heq' : (c : A) * (b.repr f i : A) = (a : A) := by
      exact congrArg (fun x : AJ J => (x : A)) hrepr
    have : f = (b.repr f i : A) := mul_left_cancel₀ hc (hmul.trans heq'.symm)
    rw [this]
    exact (b.repr f i).property
  have hinter : Set.range (fun x : K => x ^ p) = ⋂ J : Finset I, (KJ J : Set K) := by
    apply Set.Subset.antisymm
    · intro z hz
      exact Set.mem_iInter.mpr (fun J => hpow J hz)
    · intro z hz
      obtain ⟨a, c, hc, hfrac⟩ := IsFractionRing.div_surjective A z
      let f : A := a * c ^ (p - 1)
      have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
      have hcn : algebraMap A K c ≠ 0 := fun h =>
        (nonZeroDivisors.ne_zero hc) (hinj (by simpa using h))
      have heq : algebraMap A K f = z * algebraMap A K (c ^ p) := by
        rw [← hfrac]
        simp only [f, map_mul, map_pow]
        have hpc : algebraMap A K c ^ p =
            algebraMap A K c ^ (p - 1) * algebraMap A K c := by
          rw [← pow_succ, Nat.sub_add_cancel hp]
        rw [hpc]
        rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hcn]
      have hall : ∀ J, f ∈ AJ J := by
        intro J
        apply hsaturated J
        rw [heq]
        exact (KJ J).mul_mem (Set.mem_iInter.mp hz J) (hmap J _ (hpower c J))
      obtain ⟨h, hh⟩ := (hroot f).mp hall
      refine ⟨algebraMap A K h / algebraMap A K c, ?_⟩
      change (algebraMap A K h / algebraMap A K c) ^ p = z
      rw [div_pow, ← map_pow, hh]
      rw [heq, map_pow]
      exact mul_div_cancel_right₀ z (pow_ne_zero p hcn)
  have hmono : ∀ J J' : Finset I, KJ (J ∪ J') ≤ KJ J ⊓ KJ J' := by
    have hkmono (J L : Finset I) (hJL : J ⊆ L) : kJ L ≤ kJ J := by
      rw [hkJ L, hkJ J]
      apply Subfield.closure_mono
      rintro x (hx | ⟨i, hi, rfl⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨i, fun h => hi (hJL h), rfl⟩
    have hAmono (J L : Finset I) (hJL : J ⊆ L) : AJ L ≤ AJ J := by
      intro f hf
      apply (hAJ J f).mpr
      intro a g
      obtain ⟨hc, hd⟩ := (hAJ L f).mp hf a g
      exact ⟨hkmono J L hJL hc, hd⟩
    have hKmono (J L : Finset I) (hJL : J ⊆ L) : KJ L ≤ KJ J := by
      intro z hz
      obtain ⟨a, b, hb, heq⟩ := (hKJ L z).mp hz
      exact (hKJ J z).mpr
        ⟨⟨a, hAmono J L hJL a.property⟩, ⟨b, hAmono J L hJL b.property⟩, hb, heq⟩
    intro J J' z hz
    exact ⟨hKmono J (J ∪ J') Finset.subset_union_left hz,
      hKmono J' (J ∪ J') Finset.subset_union_right hz⟩
  exact ⟨hfinite, hpow, hinter, hmono⟩

end RingTheory
