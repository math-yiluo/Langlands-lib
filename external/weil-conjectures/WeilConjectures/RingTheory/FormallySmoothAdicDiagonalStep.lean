/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Tactic.LinearCombination

/-!
# One diagonal step in the adic quotient grid

Source: Stacks Project, More on Algebra, proof of Lemma Tag 07NJ
(blueprint: lem-weil-pbc-fs-adic-diagonal-step).
-/

@[expose] public section

universe u v w

namespace Algebra

private theorem lift_surjective
    {R : Type u} {S : Type v} {D : Type w} {B : Type w}
    [CommRing R] [CommRing S] [CommRing D] [CommRing B]
    [Algebra R S] [Algebra R D] [Algebra R B]
    (n : Ideal S) (hS : FormallySmoothAdic R S n)
    (π : D →ₐ[R] B) (hπ : Function.Surjective π)
    (hker : (RingHom.ker π.toRingHom) ^ 2 = ⊥) (g : S →ₐ[R] B)
    (hg : ∃ e : ℕ, 1 ≤ e ∧ ∀ x ∈ n ^ e, g x = 0) :
    ∃ f : S →ₐ[R] D, π.comp f = g := by
  classical
  choose σ hσ using fun s : S ↦ hπ (g s)
  let C := Algebra.adjoin R (Set.range σ)
  have hσC (s : S) : σ s ∈ C := Algebra.subset_adjoin ⟨s, rfl⟩
  let E := Shrink.{max u v} C
  let e : E ≃ C := (equivShrink C).symm
  let : CommRing E := e.commRing
  let : Algebra R E := Equiv.algebra R e
  let eₐ : E ≃ₐ[R] C := Equiv.algEquiv R e
  let inc : E →ₐ[R] D := C.val.comp eₐ.toAlgHom
  let p : E →ₐ[R] B := π.comp inc
  have hgp (s : S) : g s ∈ p.range := by
    refine ⟨eₐ.symm ⟨σ s, hσC s⟩, ?_⟩
    change π (eₐ (eₐ.symm ⟨σ s, hσC s⟩)) = g s
    rw [eₐ.apply_symm_apply]
    exact hσ s
  let g' : S →ₐ[R] p.range := g.codRestrict p.range hgp
  let ep := Ideal.quotientKerAlgEquivOfSurjective p.rangeRestrict_surjective
  let qg := ep.symm.toAlgHom.comp g'
  have hk : (RingHom.ker p.rangeRestrict.toRingHom) ^ 2 = ⊥ := by
    rw [show RingHom.ker p.rangeRestrict.toRingHom = RingHom.ker p.toRingHom from
      AlgHom.ker_rangeRestrict p]
    apply le_antisymm _ bot_le
    rw [pow_two]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    have hix : inc x ∈ RingHom.ker π.toRingHom := hx
    have hiy : inc y ∈ RingHom.ker π.toRingHom := hy
    have hm := Ideal.mul_mem_mul hix hiy
    rw [← pow_two, hker] at hm
    change x * y = 0
    have hi : Function.Injective inc := Subtype.val_injective.comp eₐ.injective
    apply hi
    simpa only [map_mul, map_zero] using (show inc x * inc y = 0 from hm)
  have hqg : ∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, qg x = 0 := by
    obtain ⟨k, hk, hgk⟩ := hg
    refine ⟨k, hk, fun x hx ↦ ?_⟩
    change ep.symm (g' x) = 0
    have hz : g' x = 0 := Subtype.ext (hgk x hx)
    rw [hz, map_zero]
  obtain ⟨f, hf⟩ := hS (RingHom.ker p.rangeRestrict.toRingHom) hk qg hqg
  refine ⟨inc.comp f, ?_⟩
  ext s
  have hs := AlgHom.congr_fun hf s
  have ht := congrArg ep hs
  change ep (Ideal.Quotient.mk _ (f s)) = ep (ep.symm (g' s)) at ht
  rw [ep.apply_symm_apply] at ht
  change p.rangeRestrict (f s) = g' s at ht
  exact congrArg (fun z : p.range ↦ (z : B)) ht

private theorem lift_compatible_quotients
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (n : Ideal S) (hS : FormallySmoothAdic R S n) (K L D : Ideal A)
    (hDK : D ≤ K) (hDL : D ≤ L) (hsq : (K ⊓ L) ^ 2 ≤ D)
    (f : S →ₐ[R] A ⧸ K) (t : S →ₐ[R] A ⧸ L)
    (hf : ∃ e : ℕ, 1 ≤ e ∧ ∀ x ∈ n ^ e, f x = 0)
    (ht : ∃ e : ℕ, 1 ≤ e ∧ ∀ x ∈ n ^ e, t x = 0)
    (hc : (Ideal.Quotient.factorₐ R (le_sup_left : K ≤ K ⊔ L)).comp f =
      (Ideal.Quotient.factorₐ R (le_sup_right : L ≤ K ⊔ L)).comp t) :
    ∃ f' : S →ₐ[R] A ⧸ D,
      (Ideal.Quotient.factorₐ R hDK).comp f' = f ∧
      (Ideal.Quotient.factorₐ R hDL).comp f' = t ∧
      ∃ e : ℕ, 1 ≤ e ∧ ∀ x ∈ n ^ e, f' x = 0 := by
  let qK := Ideal.Quotient.factorₐ R (le_sup_left : K ≤ K ⊔ L)
  let qL := Ideal.Quotient.factorₐ R (le_sup_right : L ≤ K ⊔ L)
  let P := AlgHom.equalizer
    (qK.comp (AlgHom.fst R (A ⧸ K) (A ⧸ L)))
    (qL.comp (AlgHom.snd R (A ⧸ K) (A ⧸ L)))
  let p0 := (Ideal.Quotient.factorₐ R hDK).prod (Ideal.Quotient.factorₐ R hDL)
  have hp0 (z : A ⧸ D) : p0 z ∈ P := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  let p : A ⧸ D →ₐ[R] P := p0.codRestrict P hp0
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective z.val.1
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective z.val.2
    have hxy : Ideal.Quotient.mk (K ⊔ L) x = Ideal.Quotient.mk (K ⊔ L) y := by
      have hz := z.property
      change qK z.val.1 = qL z.val.2 at hz
      rw [← hx, ← hy] at hz
      exact hz
    obtain ⟨k, hk, l, hl, hkl⟩ := Submodule.mem_sup.mp
      (Ideal.Quotient.eq.mp hxy)
    refine ⟨Ideal.Quotient.mk D (x - k), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change Ideal.Quotient.mk K (x - k) = z.val.1
      rw [← hx]
      apply Ideal.Quotient.eq.mpr
      simpa only [sub_sub_cancel_left, neg_mem_iff] using hk
    · change Ideal.Quotient.mk L (x - k) = z.val.2
      rw [← hy]
      apply Ideal.Quotient.eq.mpr
      have he : x - k - y = l := by
        linear_combination -hkl
      rw [he]
      exact hl
  have hpk : (RingHom.ker p.toRingHom) ^ 2 = ⊥ := by
    apply le_antisymm _ bot_le
    rw [pow_two]
    apply Ideal.mul_le.mpr
    intro z hz z' hz'
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z'
    have hx : x ∈ K ⊓ L := by
      have he := congrArg (fun z : P ↦ z.val) hz
      exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst he),
        Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd he)⟩
    have hy : y ∈ K ⊓ L := by
      have he := congrArg (fun z : P ↦ z.val) hz'
      exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst he),
        Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd he)⟩
    have hm : x * y ∈ D := hsq (by
      rw [pow_two]
      exact Ideal.mul_mem_mul hx hy)
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  have hpair (x : S) : f.prod t x ∈ P := AlgHom.congr_fun hc x
  let pair : S →ₐ[R] P := (f.prod t).codRestrict P hpair
  obtain ⟨e, he, hfe⟩ := hf
  obtain ⟨d, hd, htd⟩ := ht
  have hcont : ∀ x ∈ n ^ (max e d), pair x = 0 := by
    intro x hx
    apply Subtype.ext
    exact Prod.ext
      (hfe x (Ideal.pow_le_pow_right (Nat.le_max_left e d) hx))
      (htd x (Ideal.pow_le_pow_right (Nat.le_max_right e d) hx))
  obtain ⟨f', hf'⟩ := lift_surjective n hS p hp hpk pair
    ⟨max e d, he.trans (Nat.le_max_left e d), hcont⟩
  refine ⟨f', ?_, ?_, ?_⟩
  · ext x
    exact congrArg (fun z : P ↦ z.val.1) (AlgHom.congr_fun hf' x)
  · ext x
    exact congrArg (fun z : P ↦ z.val.2) (AlgHom.congr_fun hf' x)
  · refine ⟨max e d * 2, by omega, ?_⟩
    have hm : (n ^ (max e d)).map f' ≤ RingHom.ker p.toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change p (f' x) = 0
      rw [← AlgHom.comp_apply, hf']
      exact hcont x hx
    have hm2 : (n ^ (max e d * 2)).map f' ≤ ⊥ := by
      rw [pow_mul, Ideal.map_pow f' (n ^ (max e d)) 2]
      simpa only [hpk] using pow_le_pow_left' hm 2
    intro x hx
    exact hm2 (Ideal.mem_map_of_mem f' hx)

private theorem square_sup_le {A : Type w} [CommRing A]
    (V W D : Ideal A) (hv : V ^ 2 ≤ D) (hw : W ≤ D) : (V ⊔ W) ^ 2 ≤ D := by
  rw [pow_two, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
  exact sup_le
    (sup_le (by simpa only [pow_two] using hv) (Ideal.mul_le_right.trans hw))
    (sup_le (Ideal.mul_le_left.trans hw) (Ideal.mul_le_left.trans hw))

/-- Two continuous compatible maps at the old diagonal and the next first-row entry
lift to the next diagonal entry. This is a single finite lifting problem.
Source: Stacks Project, More on Algebra, proof of Lemma Tag 07NJ, the square-zero
surjections and inductive lifting paragraphs; diagonal variant written by F2.
(blueprint: lem-weil-pbc-fs-adic-diagonal-step)

Proof:
Put K = J^k + I^k, L = J + I^(k+1), D = J^(k+1) + I^(k+1).
Then K+L = J+I^k. Compatible representatives x,y have x-y = z+t with
z in K and t in L; x-z = y+t gives a representative in A/D for the pair.
Thus A/D surjects onto the fibre product of A/K and A/L over A/(K+L).
Its kernel is (K intersection L)/D. Modulo D, an element of this intersection
has a representative in J, and can also be written j+i with j in J^k and i
in I^k. Since j is in J, i is in J as well. Products of two such elements
lie in J^(k+1)+I^(2*k): the j*j and mixed terms belong to J^(k+1), using
k >= 1, and the i*i terms belong to I^(2*k). Since 2*k >= k+1, the kernel
has square zero. The pair of maps kills a positive power of n: use the maximum
of the two given exponents and the decreasing property of ideal powers.
Apply adic formal smoothness to this square-zero surjection, identifying its
target with the quotient by its kernel. The two projections of the lifting
equation give the two displayed identities. If the pair kills n^e, the lift
sends n^e into the square-zero kernel, so it kills n^(2*e).
For an independent target universe w, choose representatives of the images
of elements of S in the square-zero problem and take the R-subalgebra they
generate. Its carrier has cardinality at most max(|R|, |S|, aleph_0), so it
can be shrunk to Type(max u v). The map factors through the quotient of this
subalgebra by the restricted kernel. Apply the defining lifting property there,
then compose with the inclusion into the original algebra. The kernel-square
and power-annihilation conditions restrict to this subalgebra. This argument
proves existence only and defines no object by choosing an unproved witness. -/
theorem FormallySmoothAdic.exists_diagonal_successor
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (n : Ideal S) (hS : FormallySmoothAdic R S n) (I J : Ideal A)
    (k : ℕ) (hk : 1 ≤ k)
    (f : S →ₐ[R] A ⧸ (J ^ k ⊔ I ^ k))
    (t : S →ₐ[R] A ⧸ (J ⊔ I ^ (k + 1)))
    (hf : ∃ e : ℕ, 1 ≤ e ∧ ∀ x ∈ n ^ e, f x = 0)
    (ht : ∃ e : ℕ, 1 ≤ e ∧ ∀ x ∈ n ^ e, t x = 0)
    (hcompat :
      (Ideal.Quotient.factorₐ R (sup_le_sup (Ideal.pow_le_self (by omega)) le_rfl)).comp f =
        (Ideal.Quotient.factorₐ R (sup_le_sup le_rfl
          (Ideal.pow_le_pow_right (Nat.le_succ k)))).comp t) :
    ∃ f' : S →ₐ[R] A ⧸ (J ^ (k + 1) ⊔ I ^ (k + 1)),
      (Ideal.Quotient.factorₐ R (sup_le_sup
        (Ideal.pow_le_pow_right (Nat.le_succ k))
        (Ideal.pow_le_pow_right (Nat.le_succ k)))).comp f' = f ∧
      (Ideal.Quotient.factorₐ R (sup_le_sup
        (Ideal.pow_le_self (show k + 1 ≠ 0 by omega)) le_rfl)).comp f' = t ∧
      ∃ e : ℕ, 1 ≤ e ∧ ∀ x ∈ n ^ e, f' x = 0 := by
  let K := J ^ k ⊔ I ^ k
  let L := J ⊔ I ^ (k + 1)
  let D := J ^ (k + 1) ⊔ I ^ (k + 1)
  have hDK : D ≤ K := sup_le_sup
    (Ideal.pow_le_pow_right (Nat.le_succ k))
    (Ideal.pow_le_pow_right (Nat.le_succ k))
  have hDL : D ≤ L := sup_le_sup (Ideal.pow_le_self (by omega)) le_rfl
  have hsum : K ⊔ L = J ⊔ I ^ k := by
    apply le_antisymm
    · exact sup_le (sup_le_sup (Ideal.pow_le_self (by omega)) le_rfl)
        (sup_le_sup le_rfl (Ideal.pow_le_pow_right (Nat.le_succ k)))
    · exact sup_le ((show J ≤ L from le_sup_left).trans le_sup_right)
        ((show I ^ k ≤ K from le_sup_right).trans le_sup_left)
  have hmod : K ⊓ L = (J ^ k ⊔ (I ^ k ⊓ J)) ⊔ I ^ (k + 1) := by
    have hIK : I ^ (k + 1) ≤ K :=
      (Ideal.pow_le_pow_right (Nat.le_succ k)).trans le_sup_right
    rw [show K ⊓ L = K ⊓ (J ⊔ I ^ (k + 1)) from rfl,
      ← inf_sup_assoc_of_le (x := K) (z := I ^ (k + 1)) J hIK]
    rw [show K = J ^ k ⊔ I ^ k from rfl,
      sup_inf_assoc_of_le (I ^ k) (Ideal.pow_le_self (by omega))]
  have hj2 : (J ^ k) ^ 2 ≤ D := by
    rw [← pow_mul]
    exact (Ideal.pow_le_pow_right (show k + 1 ≤ k * 2 by omega)).trans le_sup_left
  have hi2 : (I ^ k ⊓ J) ^ 2 ≤ D := by
    calc
      (I ^ k ⊓ J) ^ 2 ≤ (I ^ k) ^ 2 := pow_le_pow_left' inf_le_left 2
      _ = I ^ (k * 2) := (pow_mul I k 2).symm
      _ ≤ I ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
      _ ≤ D := le_sup_right
  have hcross : J ^ k * (I ^ k ⊓ J) ≤ D := by
    calc
      J ^ k * (I ^ k ⊓ J) ≤ J ^ k * J := Ideal.mul_mono_right inf_le_right
      _ = J ^ (k + 1) := (pow_succ J k).symm
      _ ≤ D := le_sup_left
  have hv : (J ^ k ⊔ (I ^ k ⊓ J)) ^ 2 ≤ D := by
    rw [pow_two, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le (by simpa only [pow_two] using hj2) hcross)
      (sup_le (by simpa only [mul_comm] using hcross)
        (by simpa only [pow_two] using hi2))
  have hsq : (K ⊓ L) ^ 2 ≤ D := by
    rw [hmod]
    exact square_sup_le _ _ D hv le_sup_right
  have hc : (Ideal.Quotient.factorₐ R (le_sup_left : K ≤ K ⊔ L)).comp f =
      (Ideal.Quotient.factorₐ R (le_sup_right : L ≤ K ⊔ L)).comp t := by
    have h := congrArg (fun q : S →ₐ[R] A ⧸ (J ⊔ I ^ k) ↦
      (Ideal.Quotient.factorₐ R (le_of_eq hsum.symm)).comp q) hcompat
    rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp,
      ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp] at h
    exact h
  exact lift_compatible_quotients n hS K L D hDK hDL hsq f t hf ht hc

end Algebra
