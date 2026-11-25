/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Tactic.Ring

/-!
# Transfer of a closed-fibre section factor to a subalgebra

Source: Stacks Project, Tag 09XI, proof of (5) implies (2), decomposition of B''/IB''.
(blueprint: lem-weil-pbc-quotient-section-factor-transfer)
-/

@[expose] public section

universe u v w

namespace Algebra

-- Keep the corner calculations over an abstract ring to avoid unfolding nested quotients.
private theorem idempotent_section_prod
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
    (s : R →ₐ[A] A) (δ : R) (hδ : IsIdempotentElem δ) (hsδ : s δ = 1)
    (H : ∀ x y : R, s x = s y ↔ δ * x = δ * y) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra A C) (Φ : R ≃ₐ[A] A × C),
      Φ δ = (1, 0) ∧ ∀ x : R, (Φ x).1 = s x := by
  let q : R →+* hδ.one_sub.Corner :=
    { toFun := fun x ↦ ⟨(1 - δ) * x, (Subsemigroup.mem_corner_iff hδ.one_sub).mpr
        ⟨by rw [← mul_assoc, hδ.one_sub.eq],
          by rw [mul_assoc, mul_comm x (1 - δ), ← mul_assoc, hδ.one_sub.eq]⟩⟩
      map_one' := by apply Subtype.ext; exact mul_one (1 - δ)
      map_mul' := fun x y ↦ by
        apply Subtype.ext
        change (1 - δ) * (x * y) = ((1 - δ) * x) * ((1 - δ) * y)
        calc
          _ = ((1 - δ) * (1 - δ)) * (x * y) := by rw [hδ.one_sub.eq]
          _ = _ := by ring
      map_zero' := by apply Subtype.ext; exact mul_zero (1 - δ)
      map_add' := fun x y ↦ by apply Subtype.ext; exact mul_add (1 - δ) x y }
  let : Algebra A hδ.one_sub.Corner :=
    (q.comp (algebraMap A R)).toAlgebra
  let qa : R →ₐ[A] hδ.one_sub.Corner := { q with commutes' := fun _ ↦ rfl }
  let φ := s.prod qa
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have hδxy := (H x y).mp (congrArg Prod.fst hxy)
      have hqxy := congrArg (fun z : A × hδ.one_sub.Corner ↦ z.2.1) hxy
      change (1 - δ) * x = (1 - δ) * y at hqxy
      have hx : x = δ * x + (1 - δ) * x := by ring
      have hy : y = δ * y + (1 - δ) * y := by ring
      rw [hx, hy, hδxy, hqxy]
    · rintro ⟨r, y⟩
      have hfy : (1 - δ) * y.1 = y.1 :=
        ((Subsemigroup.mem_corner_iff hδ.one_sub).mp y.2).1
      have hsy : s y.1 = 0 := by
        rw [← hfy, map_mul, map_sub, map_one, hsδ, sub_self, zero_mul]
      refine ⟨δ * algebraMap A R r + y.1, ?_⟩
      apply Prod.ext
      · change s (δ * algebraMap A R r + y.1) = r
        simp [hsδ, hsy]
      · apply Subtype.ext
        change (1 - δ) * (δ * algebraMap A R r + y.1) = y.1
        rw [mul_add, ← mul_assoc, sub_mul, one_mul, hδ.eq, sub_self, zero_mul,
          zero_add, hfy]
  let Φ := AlgEquiv.ofBijective φ hbij
  refine ⟨hδ.one_sub.Corner, inferInstance, inferInstance, Φ, ?_, fun _ ↦ rfl⟩
  apply Prod.ext
  · exact hsδ
  · apply Subtype.ext
    change (1 - δ) * δ = 0
    rw [sub_mul, one_mul, hδ.eq, sub_self]

private theorem quotient_away_isLocalization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (I : Ideal R) :
    IsLocalization.Away (Ideal.Quotient.mk I r) (S ⧸ I.map (algebraMap R S)) := by
  have h : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers r))
      (S ⧸ I.map (algebraMap R S)) := inferInstance
  rw [Algebra.algebraMapSubmonoid_powers] at h
  exact h

private theorem idempotent_mul_eq_of_localization_eq
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : R) (hδ : IsIdempotentElem δ) [IsLocalization.Away δ S]
    {x y : R} (h : algebraMap R S x = algebraMap R S y) : δ * x = δ * y := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers δ) S).mp h
  cases n with
  | zero => simpa only [pow_zero, one_mul] using congrArg (fun z ↦ δ * z) hn
  | succ n => simpa only [hδ.pow_succ_eq] using hn

set_option backward.isDefEq.respectTransparency false in
/-- A localization isomorphism transfers a specified section factor of the closed fibre,
provided its parameter is already idempotent in the smaller closed fibre.

Source: Stacks Project, Tag 09XI, proof of (5) implies (2), decomposition of B''/IB''.
(blueprint: lem-weil-pbc-quotient-section-factor-transfer)

Proof:
1. Quotient the given localization isomorphism by I. Quotient commutes with
localization, giving (D/ID)[1/b] isomorphic to (B/IB)[1/b].
2. Under e the image of b is (1,0), so the latter localization is A/I, by the
first projection. Thus the b-corner of D/ID maps isomorphically to A/I by σ.
3. Split D/ID using its idempotent b into its b-corner and (1-b)-corner. Identify
the first corner using step 2, and use the second as C. The corner projection
is x mapped to (1-b)x, giving its A/I-algebra structure. Both projections commute
with scalars; the first projection is σ and the image of b is (1,0).
The complementary corner lives in the universe of D and hence of B. -/
theorem quotient_section_factor_transfer
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (σ : B →ₐ[A] A ⧸ I)
    (C₀ : Type w) [CommRing C₀]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* ((A ⧸ I) × C₀))
    (hes : ∀ x : B, (e (Ideal.Quotient.mk _ x)).1 = σ x)
    (D : Subalgebra A B) (b : D)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A D)) b))
    (hloc : Function.Bijective (Localization.awayMap D.val.toRingHom b))
    (heb : e (Ideal.Quotient.mk _ b.1) = (1, 0)) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra (A ⧸ I) C)
      (Φ : (D ⧸ I.map (algebraMap A D)) ≃+* ((A ⧸ I) × C)),
      (∀ a : A, Φ (Ideal.Quotient.mk _ (algebraMap A D a)) =
        (algebraMap (A ⧸ I) (A ⧸ I) (Ideal.Quotient.mk I a),
          algebraMap (A ⧸ I) C (Ideal.Quotient.mk I a))) ∧
      Φ (Ideal.Quotient.mk _ b) = (1, 0) ∧
      (∀ x : D, (Φ (Ideal.Quotient.mk _ x)).1 = σ x.1) := by
  classical
  let JD := I.map (algebraMap A D)
  let JB := I.map (algebraMap A B)
  let R := D ⧸ JD
  let π := Ideal.Quotient.mk JD
  let δ : R := π b
  have hδ : IsIdempotentElem δ := hb
  let σD := σ.comp D.val
  have hJD : JD ≤ RingHom.ker σD.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change σD (algebraMap A D a) = 0
    rw [σD.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  let s : R →ₐ[A ⧸ I] A ⧸ I :=
    (Ideal.Quotient.liftₐ JD σD hJD).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  have hsδ : s δ = 1 := (hes b.1).symm.trans (congrArg Prod.fst heb)
  let LD := Localization.Away b
  let LB := Localization.Away b.1
  let : IsLocalization.Away (D.val.toRingHom b) LB := by
    have hv : D.val.toRingHom b = b.1 := rfl
    rw [hv]
    exact inferInstanceAs (IsLocalization.Away b.1 (Localization.Away b.1))
  let QD := LD ⧸ JD.map (algebraMap D LD)
  let QB := LB ⧸ JB.map (algebraMap B LB)
  let k : LD ≃ₐ[A] LB := AlgEquiv.ofBijective (Localization.awayMapₐ D.val b) hloc
  have hkI : JB.map (algebraMap B LB) =
      (JD.map (algebraMap D LD)).map k.toRingHom := by
    dsimp only [JD, JB]
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    exact (k.commutes a).symm
  let kq : QD ≃+* QB := Ideal.quotientEquiv _ _ k.toRingEquiv hkI
  let tD : R →+* QD :=
    Ideal.quotientMap _ (algebraMap D LD) Ideal.le_comap_map
  let tB : (B ⧸ JB) →+* QB :=
    Ideal.quotientMap _ (algebraMap B LB) Ideal.le_comap_map
  have hjmap : JD.map D.val.toRingHom = JB := by
    rw [Ideal.map_map]
    rfl
  let j : R →+* B ⧸ JB := Ideal.quotientMap _ D.val.toRingHom
    (Ideal.map_le_iff_le_comap.mp hjmap.le)
  have hcomp (x : R) : kq (tD x) = tB (j x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (k (algebraMap D LD x)) =
      Ideal.Quotient.mk _ (algebraMap B LB x.1)
    congr 1
    change Localization.awayMap D.val.toRingHom b (algebraMap D LD x) = _
    exact IsLocalization.map_eq (S := LD) (Q := LB) _ x
  have hjs (x : R) : (e (j x)).1 = s x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hes x.1
  have hjδ : e (j δ) = (1, 0) := heb
  let : IsLocalization.Away δ QD := quotient_away_isLocalization (S := LD) b JD
  let : IsLocalization.Away (j δ) QB := quotient_away_isLocalization (S := LB) b.1 JB
  have H (x y : R) : s x = s y ↔ δ * x = δ * y := by
    constructor
    · intro hxy
      have hjxy : j δ * j x = j δ * j y := by
        apply e.injective
        simp only [map_mul, hjδ]
        apply Prod.ext
        · simpa only [Prod.fst_mul, Prod.fst_zero, Prod.fst_one, one_mul, hjs] using hxy
        · simp
      have htB : tB (j x) = tB (j y) := by
        apply (IsLocalization.eq_iff_exists (Submonoid.powers (j δ)) QB).mpr
        exact ⟨⟨j δ, Submonoid.mem_powers _⟩, hjxy⟩
      have htD : tD x = tD y := kq.injective ((hcomp x).trans (htB.trans (hcomp y).symm))
      exact idempotent_mul_eq_of_localization_eq (S := QD) δ hδ htD
    · intro hxy
      simpa only [map_mul, hsδ, one_mul] using congrArg s hxy
  obtain ⟨C, hC, hAC, Φ, hΦδ, hΦs⟩ := idempotent_section_prod s δ hδ hsδ H
  exact ⟨C, hC, hAC, Φ.toRingEquiv,
    (fun a ↦ Φ.commutes (Ideal.Quotient.mk I a)), hΦδ, fun x ↦ hΦs (π x)⟩

end Algebra
