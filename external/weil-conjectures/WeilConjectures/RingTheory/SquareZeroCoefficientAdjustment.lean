/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.RingTheory.ExistsLiftOfFieldCharP
import WeilConjectures.RingTheory.FiniteRankCoefficientCorrection

/-!
# Lifting a finite coefficient model through a square-zero terminal layer

Source: Stacks Project, Tag 07FG, the inductive step of the coefficient-field claim.
(blueprint: lem-weil-pbc-square-zero-coefficient-adjustment)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

-- Completeness requires only a power of I to annihilate M, not nilpotence of I.
private theorem complete_of_power_annihilates {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : ℕ)
    (hN : I ^ N • (⊤ : Submodule R M) = ⊥) : IsAdicComplete I M := by
  refine { haus' := fun x hx ↦ ?_, prec' := fun f hf ↦ ⟨f N, fun m ↦ ?_⟩ }
  · simpa [hN, SModEq.bot] using hx N
  · by_cases hm : m ≤ N
    · exact hf hm
    · have hNm : N ≤ m := by omega
      have heq : f N = f m := by simpa [hN, SModEq.bot] using hf hNm
      rw [heq]

private theorem closure_eq_top_of_section
    (K : Type w) [Field K] (Λ : Type v) [CommRing Λ] [IsLocalRing Λ]
    (r : Λ →+* K) (hker : RingHom.ker r = IsLocalRing.maximalIdeal Λ)
    (σ : K →+* Λ) (hσ : r.comp σ = RingHom.id K)
    (t : Finset Λ) (ht : Ideal.span (t : Set Λ) = IsLocalRing.maximalIdeal Λ)
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal Λ)) :
    Subring.closure ((t : Set Λ) ∪ Set.range σ) = ⊤ := by
  let S := Subring.closure ((t : Set Λ) ∪ Set.range σ)
  let f : S →+* Λ := S.subtype
  let m := IsLocalRing.maximalIdeal Λ
  let J := m.comap f
  have hmap : J.map f = m := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.mpr le_rfl
    · change IsLocalRing.maximalIdeal Λ ≤ _
      rw [← ht]
      apply Ideal.span_le.mpr
      intro x hx
      have hxS : x ∈ S := Subring.subset_closure (Or.inl hx)
      have hxm : x ∈ m := by
        change x ∈ IsLocalRing.maximalIdeal Λ
        rw [← ht]
        exact Ideal.subset_span hx
      exact Ideal.mem_map_of_mem f (show (⟨x, hxS⟩ : S) ∈ J from hxm)
  have hJ : IsNilpotent J := by
    obtain ⟨N, hN⟩ := hnil
    refine ⟨N, eq_bot_iff.mpr ?_⟩
    intro x hx
    have hx' := Ideal.le_comap_pow f N hx
    have hz : f x = 0 := by simpa [m, hN] using hx'
    exact Subtype.val_injective (by simpa [f] using hz)
  let : IsAdicComplete J S := by
    obtain ⟨N, hN⟩ := hJ
    exact complete_of_power_annihilates J N (by simp [hN])
  let : IsAdicComplete (J.map f) Λ := by
    rw [hmap]
    obtain ⟨N, hN⟩ := hnil
    exact complete_of_power_annihilates m N (by simp [m, hN])
  have hsurj : Function.Surjective ((Ideal.Quotient.mk (J.map f)).comp f) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hσS : σ (r a) ∈ S := Subring.subset_closure (Or.inr ⟨_, rfl⟩)
    refine ⟨⟨σ (r a), hσS⟩, ?_⟩
    change Ideal.Quotient.mk (J.map f) (σ (r a)) = Ideal.Quotient.mk (J.map f) a
    rw [hmap, Ideal.Quotient.eq]
    change σ (r a) - a ∈ IsLocalRing.maximalIdeal Λ
    rw [← hker, RingHom.mem_ker, map_sub]
    change (r.comp σ) (r a) - r a = 0
    rw [hσ]
    simp
  have hf : Function.Surjective f := surjective_of_mk_map_comp_surjective f hsurj
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := hf x
  exact y.property

private theorem coefficient_closure_mono
    (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]
    (Λ : Type v) [CommRing Λ] (σ : K →+* Λ) (t : Finset Λ)
    {c d : Finset K} (h : c ⊆ d) :
    Subring.closure ((t : Set Λ) ∪
      σ '' (IntermediateField.adjoin k (c : Set K) : Set K)) ≤
    Subring.closure ((t : Set Λ) ∪
      σ '' (IntermediateField.adjoin k (d : Set K) : Set K)) := by
  apply Subring.closure_mono
  apply Set.union_subset_union_right
  apply Set.image_mono
  exact IntermediateField.adjoin.mono k _ _ h

private theorem exists_finite_coefficients_of_mem_closure
    (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]
    (Λ : Type v) [CommRing Λ] (σ : K →+* Λ) (t : Finset Λ)
    {x : Λ} (hx : x ∈ Subring.closure ((t : Set Λ) ∪ Set.range σ)) :
    ∃ c : Finset K, x ∈ Subring.closure ((t : Set Λ) ∪
      σ '' (IntermediateField.adjoin k (c : Set K) : Set K)) := by
  classical
  induction hx using Subring.closure_induction with
  | mem x hx =>
      rcases hx with hx | ⟨a, rfl⟩
      · exact ⟨∅, Subring.subset_closure (Or.inl hx)⟩
      · refine ⟨{a}, Subring.subset_closure (Or.inr ⟨a, ?_, rfl⟩)⟩
        exact IntermediateField.subset_adjoin k _ (by simp)
  | zero => exact ⟨∅, Subring.zero_mem _⟩
  | one => exact ⟨∅, Subring.one_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c ∪ d, Subring.add_mem _
        (coefficient_closure_mono k K Λ σ t Finset.subset_union_left hc)
        (coefficient_closure_mono k K Λ σ t Finset.subset_union_right hd)⟩
  | neg x _ hx =>
      obtain ⟨c, hc⟩ := hx
      exact ⟨c, Subring.neg_mem _ hc⟩
  | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c ∪ d, Subring.mul_mem _
        (coefficient_closure_mono k K Λ σ t Finset.subset_union_left hc)
        (coefficient_closure_mono k K Λ σ t Finset.subset_union_right hd)⟩

private theorem exists_finite_coefficients_for_finset
    (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]
    (Λ : Type v) [CommRing Λ] (σ : K →+* Λ) (t : Finset Λ)
    (htop : Subring.closure ((t : Set Λ) ∪ Set.range σ) = ⊤) (f : Finset Λ) :
    ∃ c : Finset K, ∀ x ∈ f, x ∈ Subring.closure ((t : Set Λ) ∪
      σ '' (IntermediateField.adjoin k (c : Set K) : Set K)) := by
  classical
  induction f using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | @insert x f hx ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨d, hd⟩ := exists_finite_coefficients_of_mem_closure k K Λ σ t
        (show x ∈ Subring.closure ((t : Set Λ) ∪ Set.range σ) by rw [htop]; trivial)
      refine ⟨c ∪ d, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact coefficient_closure_mono k K Λ σ t Finset.subset_union_right hd
      · exact coefficient_closure_mono k K Λ σ t Finset.subset_union_left (hc y hy)

private theorem exists_structure_map_lift_in_coefficient_closure
    (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]
    (Λ : Type v) [CommRing Λ] [Algebra k Λ] [IsLocalRing Λ]
    (t : Finset Λ) (I : Ideal Λ) (hI : I ≤ IsLocalRing.maximalIdeal Λ)
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal Λ))
    (σ : K →+* Λ) (σ' : K →+* Λ ⧸ I)
    (hσ : (Ideal.Quotient.mk I).comp σ = σ') (c : Finset K)
    (hc : ∀ a : k, algebraMap k (Λ ⧸ I) a ∈
      Subring.closure ((Ideal.Quotient.mk I) '' (t : Set Λ) ∪
        σ' '' (IntermediateField.adjoin k (c : Set K) : Set K)))
    (p : ℕ) [CharP k p] (hp : 0 < p) :
    ∃ ψ : k →+* Λ,
      (Ideal.Quotient.mk I).comp ψ =
        (Ideal.Quotient.mk I).comp (algebraMap k Λ) ∧
      (∀ a : k, ψ a ∈ Subring.closure ((t : Set Λ) ∪
        σ '' (IntermediateField.adjoin k (c : Set K) : Set K))) := by
  classical
  let q := Ideal.Quotient.mk I
  let S := Subring.closure ((t : Set Λ) ∪
    σ '' (IntermediateField.adjoin k (c : Set K) : Set K))
  let f := q.comp S.subtype
  have hmapS : S.map q = Subring.closure (q '' (t : Set Λ) ∪
      σ' '' (IntermediateField.adjoin k (c : Set K) : Set K)) := by
    rw [RingHom.map_closure, Set.image_union]
    congr 1
    rw [Set.image_image]
    have heq : q ∘ σ = σ' := congrArg DFunLike.coe hσ
    simpa only [Function.comp_def] using congrArg
      (fun f : K → Λ ⧸ I ↦ q '' (t : Set Λ) ∪
        f '' (IntermediateField.adjoin k (c : Set K) : Set K)) heq
  have hmem : ∀ a : k, algebraMap k (Λ ⧸ I) a ∈ f.range := by
    intro a
    have ha : algebraMap k (Λ ⧸ I) a ∈ S.map q := by
      rw [hmapS]
      exact hc a
    obtain ⟨x, hx, heq⟩ := ha
    exact ⟨⟨x, hx⟩, heq⟩
  let g0 : k →+* f.range := (algebraMap k (Λ ⧸ I)).codRestrict f.range hmem
  let J := RingHom.ker f.rangeRestrict
  let e : S ⧸ J ≃+* f.range :=
    RingHom.quotientKerEquivOfSurjective f.rangeRestrict_surjective
  let g := e.symm.toRingHom.comp g0
  have hJ : J ≤ (IsLocalRing.maximalIdeal Λ).comap S.subtype := by
    intro x hx
    have hxq : q x.val = 0 := by
      have hz := congrArg Subtype.val (RingHom.mem_ker.mp hx)
      exact hz
    exact hI ((Ideal.Quotient.eq_zero_iff_mem).mp hxq)
  obtain ⟨N, hN⟩ := hnil
  have hN' : IsLocalRing.maximalIdeal Λ ^ (N + 1) = ⊥ := by
    rw [pow_succ, hN, zero_mul]
    rfl
  have hJN : J ^ (N + 1) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hx' := Ideal.le_comap_pow S.subtype (N + 1)
      ((Ideal.pow_right_mono hJ (N + 1)) hx)
    have hz : x.val = 0 := by simpa [hN'] using hx'
    exact Subtype.val_injective (by simpa using hz)
  have hpΛ : (p : Λ) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (algebraMap k Λ) (CharP.cast_eq_zero k p)
  have hpS : (p : S) = 0 := Subtype.val_injective hpΛ
  obtain ⟨ψS, hψS⟩ :=
    RingHom.exists_lift_of_field_charP k S p hp hpS J (N + 1) (by omega) hJN g
  refine ⟨S.subtype.comp ψS, ?_, fun a ↦ (ψS a).property⟩
  ext a
  change f (ψS a) = q (algebraMap k Λ a)
  calc
    f (ψS a) = (e (Ideal.Quotient.mk J (ψS a))).val := rfl
    _ = (e (g a)).val := congrArg (fun x ↦ (e x).val) (RingHom.congr_fun hψS a)
    _ = q (algebraMap k Λ a) := by
      change (e (e.symm (g0 a))).val = _
      rw [e.apply_symm_apply]
      rfl

/-- Lift an already adjusted coefficient section through an ideal annihilated by the
maximal ideal. Unlike the full coefficient-field claim, this theorem assumes the
coefficient model in the quotient and preserves its specified section after reduction.

Source: Stacks Project, Tag 07FG, proof of the coefficient-field claim, from
"Choose a lift sigma" through "Then the claim holds".
(blueprint: lem-weil-pbc-square-zero-coefficient-adjustment).

Proof:
1. Write m for the maximal ideal and choose N with m^N = 0. Since I is contained in m
   and mI = 0, I is square-zero. Lift the specified section sigma' through I by the
   characteristic-p field lifting theorem (Tag 0320). Its composite with r is the identity.
2. Put S = Subring.closure(t union sigma0(k(c'))), and restrict the quotient map
   to S. Its image contains the image of k by the quotient coefficient hypothesis.
   Let J be its kernel. Since J lies in the contraction of m to S and m is nilpotent,
   J is nilpotent. The first isomorphism theorem identifies S/J with the image.
   Lift the induced map k -> S/J to S by Tag 0320, obtaining psi in this closure
   and equal to the structure map modulo I.
3. The difference between the structure map and the lifted evaluation is a derivation
   theta : k -> I, since the two maps agree modulo I and mI = 0. Replacing sigma by
   sigma + D for a derivation D : K -> I keeps its reduction sigma' unchanged and
   replaces theta by theta - D restricted to k. Positive-degree monomials vanish when
   multiplied by I, and the constant coefficient of the lift of a is its image in K.
4. Choose a basis dy_j of the prime-field differentials of k. Jacobi--Zariski exactness
   makes the kernel of K tensor Omega_k -> Omega_K finite dimensional by the H1
   hypothesis. It is supported on a finite subset J0 of this basis. Outside J0, the
   images dy_j are independent. Extend these images to a basis of Omega_K and choose
   a linear map to I matching theta there. Its associated derivation D makes the new
   discrepancy a finite sum of k-multiples of fixed elements f_j in I, j in J0.
5. A residue section and the generators t generate the whole nilpotent local ring over
   K: substitute the ideal generators repeatedly in a = sigma(r(a)) + z, z in m;
   after N substitutions the remainder in m^N vanishes. Thus each of the finitely many
   f_j is a polynomial in t with finitely many coefficients in K. Enlarge c' by these
   coefficients. In the discrepancy formula, replace the action of a in k on f_j by
   sigma(algebraMap k K a): their difference lies in m, which annihilates I. Both the
   lifted evaluation and every discrepancy summand now lie in the asserted ring
   closure. Closure under finite sums proves the containment. All adjustments take
   values in I, so the reduction of the final section remains sigma'. -/
theorem exists_square_zero_coefficient_adjustment
    (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]
    (Λ : Type v) [CommRing Λ] [Algebra k Λ] [IsLocalRing Λ]
    (r : Λ →+* K) (_hr : Function.Surjective r)
    (hker : RingHom.ker r = IsLocalRing.maximalIdeal Λ)
    (hcomm : r.comp (algebraMap k Λ) = algebraMap k K)
    (t : Finset Λ) (ht : Ideal.span (t : Set Λ) = IsLocalRing.maximalIdeal Λ)
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal Λ))
    (I : Ideal Λ) (hI : I ≤ RingHom.ker r)
    (hkill : IsLocalRing.maximalIdeal Λ * I = ⊥)
    (σ' : K →+* Λ ⧸ I) (c' : Finset K)
    (hσ' : (Ideal.Quotient.lift I r (fun _ hx ↦ hI hx)).comp σ' = RingHom.id K)
    (hc' : ∀ a : k, algebraMap k (Λ ⧸ I) a ∈
      Subring.closure ((Ideal.Quotient.mk I) '' (t : Set Λ) ∪
        σ' '' (IntermediateField.adjoin k (c' : Set K) : Set K)))
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (hH : Module.Finite K (H1Cotangent k K)) :
    ∃ (σ : K →+* Λ) (c : Finset K),
      r.comp σ = RingHom.id K ∧ (Ideal.Quotient.mk I).comp σ = σ' ∧
      (∀ a : k, algebraMap k Λ a ∈ Subring.closure ((t : Set Λ) ∪
        σ '' (IntermediateField.adjoin k (c : Set K) : Set K))) := by
  classical
  have hIm : I ≤ IsLocalRing.maximalIdeal Λ := hI.trans hker.le
  have hI2 : I ^ 2 = ⊥ := by
    apply eq_bot_iff.mpr
    rw [pow_two]
    exact (mul_le_mul_left hIm I).trans hkill.le
  let : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hpΛ : (p : Λ) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (algebraMap k Λ) (CharP.cast_eq_zero k p)
  obtain ⟨σ0, hσ0q⟩ := RingHom.exists_lift_of_field_charP K Λ p hp hpΛ I 2 (by omega)
    hI2 σ'
  have hσ0 : r.comp σ0 = RingHom.id K := by
    calc
      r.comp σ0 = (Ideal.Quotient.lift I r (fun _ hx ↦ hI hx)).comp
          ((Ideal.Quotient.mk I).comp σ0) := rfl
      _ = RingHom.id K := by rw [hσ0q]; exact hσ'
  obtain ⟨ψ, hψ, hψmem⟩ := exists_structure_map_lift_in_coefficient_closure
    k K Λ t I hIm hnil σ0 σ' hσ0q c' hc' p hp
  obtain ⟨σ, f, hσ, hσq, hfI, herr⟩ := exists_finite_rank_coefficient_correction
    k K Λ r hker hcomm t ht I hI hkill σ0 hσ0 c' ψ hψ hψmem p hp hH
  have htop := closure_eq_top_of_section K Λ r hker σ hσ t ht hnil
  obtain ⟨d, hd⟩ := exists_finite_coefficients_for_finset k K Λ σ t htop f
  let c := c' ∪ d
  let S := Subring.closure ((t : Set Λ) ∪
    σ '' (IntermediateField.adjoin k (c : Set K) : Set K))
  have hfS : ∀ x ∈ f, x ∈ S := fun x hx ↦
    coefficient_closure_mono k K Λ σ t Finset.subset_union_right (hd x hx)
  have hscalar (a : k) (x : Λ) (hxI : x ∈ I) (hxS : x ∈ S) : a • x ∈ S := by
    have hz : algebraMap k Λ a - σ (algebraMap k K a) ∈
        IsLocalRing.maximalIdeal Λ := by
      rw [← hker, RingHom.mem_ker, map_sub]
      have ha := RingHom.congr_fun hcomm a
      have hb := RingHom.congr_fun hσ (algebraMap k K a)
      change r (algebraMap k Λ a) - r (σ (algebraMap k K a)) = 0
      change r (algebraMap k Λ a) = algebraMap k K a at ha
      change r (σ (algebraMap k K a)) = algebraMap k K a at hb
      rw [ha, hb, sub_self]
    have hprod : (algebraMap k Λ a - σ (algebraMap k K a)) * x = 0 := by
      have hm := Ideal.mul_mem_mul hz hxI
      rw [hkill] at hm
      exact hm
    have heq : a • x = σ (algebraMap k K a) * x := by
      rw [Algebra.smul_def]
      exact sub_eq_zero.mp (by simpa only [sub_mul] using hprod)
    rw [heq]
    apply S.mul_mem _ hxS
    apply Subring.subset_closure
    exact Or.inr ⟨algebraMap k K a, IntermediateField.algebraMap_mem _ a, rfl⟩
  have hspan : ∀ x ∈ Submodule.span k (f : Set Λ), x ∈ S ∧ x ∈ I := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨hfS x hx, hfI hx⟩
    | zero => exact ⟨S.zero_mem, I.zero_mem⟩
    | add x y _ _ hx hy => exact ⟨S.add_mem hx.1 hy.1, I.add_mem hx.2 hy.2⟩
    | smul a x _ hx =>
        refine ⟨hscalar a x hx.2 hx.1, ?_⟩
        simpa only [Algebra.smul_def] using I.mul_mem_left (algebraMap k Λ a) hx.2
  refine ⟨σ, c, hσ, hσq.trans hσ0q, ?_⟩
  intro a
  obtain ⟨b, hb, he⟩ := herr a
  have hbS : b ∈ S := coefficient_closure_mono k K Λ σ t Finset.subset_union_left hb
  have heS := (hspan _ he).1
  simpa only [sub_add_cancel] using S.add_mem heS hbS

end Algebra
