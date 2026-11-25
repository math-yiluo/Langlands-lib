/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.DepthInSES
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Ring.ULift
import WeilConjectures.RingTheory.KollarRegularElementAlternatives

/-!
# Kollár's local ring dichotomy

Source: Stacks Project, Algebra, Lemma 10.119.2 (Tag 0BHZ), the existence of the four
cases and the exclusion of case (4) by case (3)
(blueprint: lem-weil-pbc-kollar-local-dichotomy).
-/

@[expose] public section

universe u v

namespace IsLocalRing

private theorem regular_element_of_depth_one
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (h : (1 : ℕ∞) ≤ depth (R := R) M) :
    ∃ x : R, x ∈ maximalIdeal R ∧ IsSMulRegular M x := by
  classical
  have ht : (maximalIdeal R) • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  rw [depth, Ideal.depth, ite_eq_right ht] at h
  by_contra hn
  have hz : sSup {n : ℕ∞ | ∃ rs : List R, RingTheory.Sequence.IsRegular M rs ∧
      (∀ x ∈ rs, x ∈ maximalIdeal R) ∧ n = (rs.length : ℕ∞)} ≤ 0 := by
    apply sSup_le
    rintro n ⟨rs, hr, hm, rfl⟩
    cases rs with
    | nil => simp
    | cons x xs =>
      exact False.elim (hn ⟨x, hm x (by simp),
        (RingTheory.Sequence.isRegular_cons_iff M x xs).mp hr |>.1⟩)
  exact (by simp : ¬ (1 : ℕ∞) ≤ 0) (h.trans hz)

private theorem depth_one_of_regular_element
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    {x : R} (hx : x ∈ maximalIdeal R) (hr : IsSMulRegular M x) :
    (1 : ℕ∞) ≤ depth (R := R) M := by
  classical
  unfold depth Ideal.depth
  split_ifs with ht
  · exact le_top
  · apply le_sSup
    refine ⟨[x], ?_, ?_, by simp⟩
    · apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
      · simpa using hx
      · rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
        exact ⟨hr, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩
    · simpa using hx

private theorem injective_of_depth_two
    {R : Type u} {S : Type v} [CommRing R] [IsLocalRing R] [CommRing S]
    (φ : R →+* S) (hd : (2 : ℕ∞) ≤ depth (R := R) R)
    (n : ℕ) (hk : (maximalIdeal R) ^ n * RingHom.ker φ = ⊥) :
    Function.Injective φ := by
  obtain ⟨x, hx, hr⟩ := regular_element_of_depth_one R (le_trans (by simp) hd)
  apply (RingHom.injective_iff_ker_eq_bot φ).mpr
  apply le_antisymm _ bot_le
  intro a ha
  have hz : x ^ n * a = 0 := by
    have hm := Ideal.mul_mem_mul (Ideal.pow_mem_pow hx n) ha
    rw [hk] at hm
    exact hm
  exact (hr.pow n) (by simpa using hz)

private theorem surjective_of_depth_two
    {R : Type u} {S : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [Nontrivial S] (φ : R →+* S)
    (hf : letI := φ.toAlgebra; Module.Finite R S)
    (hd : (2 : ℕ∞) ≤ depth (R := R) R) (hi : Function.Injective φ)
    (n : ℕ) (hc : ∀ z ∈ Ideal.map φ ((maximalIdeal R) ^ n), z ∈ φ.range)
    (ha : ¬ ∃ z : S, ∀ a : R, φ a * z = 0 ↔ a ∈ maximalIdeal R) :
    Function.Surjective φ := by
  classical
  let := φ.toAlgebra
  let : Module.Finite R S := hf
  let f : R →ₗ[R] S := Algebra.linearMap R S
  have hass : maximalIdeal R ∉ associatedPrimes R S := by
    intro h
    obtain ⟨_, z, hz⟩ := isAssociatedPrime_iff.mp h
    apply ha
    refine ⟨z, ?_⟩
    intro a
    rw [hz]
    simp [Submodule.mem_colon_singleton, Algebra.smul_def]
    rfl
  obtain ⟨xS, hxS, hrS⟩ := exists_mem_maximalIdeal_smul_injective R S hass
  have hS := depth_one_of_regular_element S hxS hrS
  by_contra hn
  have hne : LinearMap.range f ≠ ⊤ := by
    intro he
    exact hn (LinearMap.range_eq_top.mp he)
  let Q := S ⧸ LinearMap.range f
  let : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr hne
  have hQ : (1 : ℕ∞) ≤ depth (R := R) Q := by
    have he := depth_in_short_exact f (LinearMap.range f).mkQ hi
      (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)
    have hsub : (1 : ℕ∞) ≤ depth (R := R) R - 1 :=
      ENat.le_sub_of_add_le_right (by simp) (by convert hd using 1; norm_num)
    exact (le_min hS hsub).trans he.2.1
  obtain ⟨x, hx, hr⟩ := regular_element_of_depth_one Q hQ
  have hle : (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ LinearMap.range f := by
    rw [Ideal.smul_top_eq_map]
    exact hc
  have hz : ∀ z : Q, x ^ n • z = 0 := by
    intro z
    obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range f) z
    rw [← LinearMap.map_smul]
    change Submodule.Quotient.mk (x ^ n • s) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hle (Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) (Submodule.mem_top))
  have hsub : Subsingleton Q := ⟨fun a b ↦ (hr.pow n) ((hz a).trans (hz b).symm)⟩
  exact not_subsingleton Q hsub

private theorem torsion_quotient
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hArt : ¬ IsArtinianRing R) (hass : maximalIdeal R ∈ associatedPrimes R R) :
    ∃ (J : Ideal R) (n : ℕ), J ≠ ⊥ ∧ J ≠ ⊤ ∧ 1 ≤ n ∧
      (maximalIdeal R) ^ n * J = ⊥ ∧
      ¬ ∃ z : R ⧸ J, ∀ a : R,
        Ideal.Quotient.mk J a * z = 0 ↔ a ∈ maximalIdeal R := by
  classical
  let f : ℕ →o Ideal R :=
    { toFun := fun n ↦ (⊥ : Ideal R).colon ((maximalIdeal R ^ n : Ideal R) : Set R)
      monotone' := fun i j hij ↦ Submodule.colon_mono le_rfl
        (Ideal.pow_le_pow_right hij) }
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) f
  let N := n + 1
  let J := f N
  have hkill : (maximalIdeal R) ^ N * J = ⊥ := by
    apply le_antisymm _ bot_le
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have h := Submodule.mem_colon.mp hb a ha
    simpa [smul_eq_mul, mul_comm] using h
  have hJtop : J ≠ ⊤ := by
    intro hJ
    have hp : (maximalIdeal R) ^ N = ⊥ := by simpa [hJ] using hkill
    exact hArt ((isArtinianRing_iff_isNilpotent_maximalIdeal R).mpr ⟨N, hp⟩)
  have hJbot : J ≠ ⊥ := by
    obtain ⟨_, z, hz⟩ := isAssociatedPrime_iff.mp hass
    have hz0 : z ≠ 0 := by
      intro h0
      have hm : maximalIdeal R = ⊤ := by
        rw [hz]
        ext a
        simp [Submodule.mem_colon_singleton, h0]
      exact (maximalIdeal.isMaximal R).ne_top hm
    have hzJ : z ∈ J := by
      apply f.monotone (show 1 ≤ N by omega)
      apply Submodule.mem_colon.mpr
      intro a ha
      have hza : a * z = 0 := by
        have ham : a ∈ maximalIdeal R := by simpa using ha
        rw [hz, Submodule.mem_colon_singleton] at ham
        exact ham
      simpa [smul_eq_mul, mul_comm] using hza
    intro h0
    have hzbot : z ∈ (⊥ : Ideal R) := h0 ▸ hzJ
    exact hz0 hzbot
  refine ⟨J, N, hJbot, hJtop, by omega, hkill, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hym : ∀ b ∈ maximalIdeal R, b * y ∈ J := by
    intro b hb
    have h := (hz b).mpr hb
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h
    exact h
  have hyN : y ∈ f (N + 1) := by
    apply Submodule.mem_colon.mpr
    intro a ha
    have hle : (maximalIdeal R) ^ (N + 1) ≤ (⊥ : Ideal R).colon {y} := by
      rw [pow_succ]
      apply Ideal.mul_le.mpr
      intro c hc b hb
      have h := Submodule.mem_colon.mp (hym b hb) c hc
      simpa [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm, mul_left_comm,
        mul_assoc] using h
    have h := Submodule.mem_colon_singleton.mp (hle ha)
    simpa [smul_eq_mul, mul_comm] using h
  have hstable : f N = f (N + 1) := (hn N (by omega)).symm.trans (hn (N + 1) (by omega))
  have hyJ : y ∈ J := by
    change y ∈ f N
    rw [hstable]
    exact hyN
  have hy0 : Ideal.Quotient.mk J y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hyJ
  have h1 := (hz 1).mp (by simp [hy0])
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

private theorem extension_of_torsion_quotient
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (J : Ideal R) (n : ℕ) (hJbot : J ≠ ⊥) (hJtop : J ≠ ⊤) (hn : 1 ≤ n)
    (hkill : (maximalIdeal R) ^ n * J = ⊥)
    (hass : ¬ ∃ z : R ⧸ J, ∀ a : R,
      Ideal.Quotient.mk J a * z = 0 ↔ a ∈ maximalIdeal R) :
    ∃ (S : Type (max u v)) (sRing : CommRing S),
      letI := sRing
      ∃ φ : R →+* S,
        let := φ.toAlgebra
        Nontrivial S ∧ Module.Finite R S ∧ ¬ Function.Bijective φ ∧
          (∃ n : ℕ, 1 ≤ n ∧ (maximalIdeal R) ^ n * RingHom.ker φ = ⊥ ∧
            ∀ z ∈ Ideal.map φ ((maximalIdeal R) ^ n), z ∈ φ.range) ∧
          ¬ ∃ z : S, ∀ a : R, φ a * z = 0 ↔ a ∈ maximalIdeal R := by
  classical
  let S := ULift.{v} (R ⧸ J)
  let e : S ≃+* R ⧸ J := ULift.ringEquiv
  let φ : R →+* S := e.symm.toRingHom.comp (Ideal.Quotient.mk J)
  have hsurj : Function.Surjective φ :=
    e.symm.surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = J := by
    ext a
    change e.symm (Ideal.Quotient.mk J a) = 0 ↔ a ∈ J
    rw [map_eq_zero_iff e.symm e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  let : Nontrivial S := e.nontrivial
  refine ⟨S, inferInstance, φ, ?_⟩
  let := φ.toAlgebra
  refine ⟨inferInstance, ?_, ?_, ⟨n, hn, by rw [hker]; exact hkill, ?_⟩, ?_⟩
  · exact Module.Finite.of_surjective (Algebra.linearMap R S) hsurj
  · intro hb
    exact hJbot (hker.symm.trans ((RingHom.injective_iff_ker_eq_bot φ).mp hb.1))
  · intro z _
    exact hsurj z
  · rintro ⟨z, hz⟩
    apply hass
    refine ⟨e z, ?_⟩
    intro a
    have he : e (φ a) = Ideal.Quotient.mk J a := by simp [φ]
    rw [← he, ← map_mul, map_eq_zero_iff e e.injective]
    exact hz a

/-- A Noetherian local ring satisfies one of Kollár's four properties, and depth at least
 two excludes the finite extension property. Source: Stacks Project, Algebra, Tag 0BHZ
(blueprint: lem-weil-pbc-kollar-local-dichotomy).

Proof: First, an Artinian ring satisfies (1). Otherwise no power of its maximal ideal vanishes
(lem-weil-pbc-noetherian-local-quotient-artinian-local). Let J be the largest ideal killed by
some power of the maximal ideal. Noetherianity makes J killed by one fixed positive power,
and the maximal ideal is not associated to R/J. If J is nonzero, R/J gives (4): the quotient
is nonzero, finite, nonisomorphic, and its kernel and cokernel have the required annihilation.
If J is zero, choose a nonzerodivisor x in the maximal ideal using
lem-weil-pbc-nonzerodivisor-if-maximal-not-associated. If the maximal ideal is not associated
to R/xR, the same lemma supplies a second regular element, so depth is at least two (3).
Otherwise choose y outside xR with y times the maximal ideal contained in xR. If that product
is contained in x times the maximal ideal, multiplication by y/x is an endomorphism of the
finite maximal ideal. The determinantal trick
(lem-weil-pbc-endomorphism-finite-module-monic) makes y/x integral. Thus R[y/x] inside R_x
is finite by lem-weil-pbc-finite-of-integral-generators. Its inclusion has zero kernel,
is not surjective, has cokernel killed by the maximal ideal, and x prevents the maximal
ideal from being associated. This gives (4). In the other subcase, yt = x after multiplying
t by a unit, y is a nonzerodivisor, and the maximal ideal is generated by t. The dimension
bound lem-weil-pbc-noetherian-local-dimension-le-generators and the exclusion of dimension
zero by lem-weil-pbc-noetherian-minimal-prime-associated give regularity of dimension one (2).
Finally assume (3) and (4). A regular element in the maximal ideal has a power killing the
kernel, so the kernel vanishes. If the finite cokernel is nonzero, the depth lemma
lem-weil-pbc-depth-in-ses and the absence of the maximal associated prime of the extension
show that its depth is at least one. But a power of the maximal ideal kills this cokernel,
contradicting a regular element in that ideal. Hence the cokernel also vanishes, making the
map an isomorphism, a contradiction. -/
theorem kollar_local_dichotomy (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    let extension : Prop := ∃ (S : Type (max u v)) (sRing : CommRing S),
      letI := sRing
      ∃ φ : R →+* S,
        letI := φ.toAlgebra
        Nontrivial S ∧ Module.Finite R S ∧ ¬ Function.Bijective φ ∧
          (∃ n : ℕ, 1 ≤ n ∧ (maximalIdeal R) ^ n * RingHom.ker φ = ⊥ ∧
            ∀ z ∈ Ideal.map φ ((maximalIdeal R) ^ n), z ∈ φ.range) ∧
          ¬ ∃ z : S, ∀ a : R, φ a * z = 0 ↔ a ∈ maximalIdeal R
    (IsArtinianRing R ∨ (IsRegularLocalRing R ∧ ringKrullDim R = 1) ∨
      (2 : ℕ∞) ≤ depth (R := R) R ∨ extension) ∧
      ¬ ((2 : ℕ∞) ≤ depth (R := R) R ∧ extension) := by
  classical
  dsimp only
  constructor
  · by_cases hArt : IsArtinianRing R
    · exact Or.inl hArt
    by_cases hass : maximalIdeal R ∈ associatedPrimes R R
    · obtain ⟨J, n, hbot, htop, hn, hk, ha⟩ := torsion_quotient R hArt hass
      exact Or.inr (Or.inr (Or.inr
        (extension_of_torsion_quotient R J n hbot htop hn hk ha)))
    obtain ⟨x, hx, hr⟩ := exists_mem_maximalIdeal_smul_injective R R hass
    by_cases hquot : maximalIdeal R ∈ associatedPrimes R (QuotSMulTop x R)
    · obtain hreg | hext := kollar_regular_element_alternatives R x hx hr hquot
      · exact Or.inr (Or.inl hreg)
      · exact Or.inr (Or.inr (Or.inr hext))
    · obtain ⟨y, hy, hry⟩ :=
        exists_mem_maximalIdeal_smul_injective R (QuotSMulTop x R) hquot
      apply Or.inr ∘ Or.inr ∘ Or.inl
      unfold depth Ideal.depth
      split_ifs
      · exact le_top
      · apply le_sSup
        refine ⟨[x, y], ?_, ?_, by simp⟩
        · apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
          · simpa using And.intro hx hy
          · rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
              RingTheory.Sequence.isWeaklyRegular_singleton_iff]
            exact ⟨hr, hry⟩
        · simpa using And.intro hx hy
  · rintro ⟨hd, S, sRing, φ, hS, hfin, hnot, ⟨n, hn, hk, hc⟩, ha⟩
    let := sRing
    let : Nontrivial S := hS
    have hi := injective_of_depth_two φ hd n hk
    exact hnot ⟨hi, surjective_of_depth_two φ hfin hd hi n hc ha⟩

end IsLocalRing
