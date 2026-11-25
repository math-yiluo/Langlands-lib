/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.Ring

/-!
# Transfer an integral idempotent factor through a localization isomorphism

Source: Stacks Project, Tag 09XI, proof of (5) implies (2), the passage from
B'₁ to A'₁, and compatibility of the closed-fibre decompositions.
-/

@[expose] public section

universe u v w

namespace Algebra

/-- A finite subalgebra controls the idempotent factor on which the localization
parameter becomes a unit. The product description specifies the closed fibre.

Source: Stacks Project, Tag 09XI (lemma-characterize-henselian-pair), proof of
(5) implies (2), the sentence identifying B'₁ with A'₁ and the final compatible
splitting; the same argument applies to the finite subalgebra B''.
(blueprint: lem-weil-pbc-finite-idempotent-factor-transfer)

Proof:
1. Set e to the image of d in B. In D[1/d] and B[1/e], the images of d and e
are 1. The relation bd = αd therefore makes the image of b equal to the unit α.
The universal property of localization gives D[1/d] = (D[1/b])[1/d] and
B[1/e] = (B[1/b])[1/e]. The given localization isomorphism respects d, and
hence induces an A-algebra isomorphism D[1/d] to B[1/e].
2. Since d is idempotent, every fraction x/dⁿ equals x/1 for n = 0 and
(dx)/1 for n > 0. Thus D to D[1/d] is surjective. The finite A-algebra D
is integral over A, and its quotient D[1/d] remains integral. Transfer this
integrality along the A-algebra isomorphism of step 1.
3. Quotient commutes with localization, so the same isomorphism gives
B[1/e]/IB[1/e] = (D/ID)[1/d̄]. Under Φ, d̄ is (1,0), whose localization
is precisely the first factor A/I. The specified formula for Φ on A shows
that this identification inverts the structure map A/I to the localized
quotient. That map is therefore bijective. -/
theorem finite_idempotent_factor_transfer
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (D : Subalgebra A B) [Module.Finite A D]
    (C : Type w) [CommRing C] [Algebra (A ⧸ I) C]
    (Φ : (D ⧸ I.map (algebraMap A D)) ≃+* ((A ⧸ I) × C))
    (hΦ : ∀ a : A, Φ (Ideal.Quotient.mk _ (algebraMap A D a)) =
      (algebraMap (A ⧸ I) (A ⧸ I) (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) C (Ideal.Quotient.mk I a)))
    (b d : D) (hd : IsIdempotentElem d)
    (α : A) (hα : IsUnit α) (hbd : b * d = algebraMap A D α * d)
    (hloc : Function.Bijective (Localization.awayMap D.val.toRingHom b))
    (hΦd : Φ (Ideal.Quotient.mk _ d) = (1, 0)) :
    (algebraMap A (Localization.Away d.1)).IsIntegral ∧
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap A (Localization.Away d.1)))
          (algebraMap A (Localization.Away d.1)) Ideal.le_comap_map) := by
  classical
  obtain ⟨v, hv⟩ := hα
  have hdiv : b ∣ d := by
    refine ⟨algebraMap A D (↑v⁻¹ : A) * d, ?_⟩
    calc
      d = algebraMap A D (↑v⁻¹ : A) * (algebraMap A D α * d) := by
        rw [← hv, ← mul_assoc, ← map_mul]
        simp
      _ = b * (algebraMap A D (↑v⁻¹ : A) * d) := by rw [← hbd]; ring
  have hkd := Localization.awayMap_bijective_of_dvd D.val.toRingHom hdiv hloc
  let S := Localization.Away d.1
  let F : D →ₐ[A] S := (IsScalarTower.toAlgHom A B S).comp D.val
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨z, rfl⟩ := hkd.2 y
    obtain ⟨x, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (S := Localization.Away d) d hd z
    refine ⟨x, ?_⟩
    simp [F, S, Localization.awayMap, IsLocalization.Away.map]
  have he : IsIdempotentElem d.1 := congrArg (fun x : D ↦ x.1) hd
  have hFd : F d = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit
      (IsLocalization.Away.algebraMap_isUnit (S := S) d.1)).mp
        (he.map (algebraMap B S))
  have hint : (algebraMap A S).IsIntegral := by
    have : Algebra.IsIntegral A S := Algebra.IsIntegral.of_surjective F hFsurj
    exact fun x ↦ Algebra.IsIntegral.isIntegral x
  let J := I.map (algebraMap A D)
  let K := I.map (algebraMap A S)
  let π := Ideal.Quotient.mk J
  let τ := Ideal.Quotient.mk K
  let q := Ideal.Quotient.mk I
  let t := Ideal.quotientMap K (algebraMap A S) Ideal.le_comap_map
  let s : D →+* A ⧸ I := (RingHom.fst _ _).comp (Φ.toRingHom.comp π)
  have hsA : ∀ a : A, s (algebraMap A D a) = q a := by
    intro a
    change (Φ (Ideal.Quotient.mk _ (algebraMap A D a))).1 = _
    rw [hΦ]
    rfl
  have hsd : s d = 1 := congrArg Prod.fst hΦd
  let sₐ : D →ₐ[A] A ⧸ I := { s with commutes' := hsA }
  let sd : Localization.Away d →ₐ[A] A ⧸ I :=
    IsLocalization.Away.liftAlgHom d (f := sₐ) (hsd.symm ▸ isUnit_one)
  let kd : Localization.Away d ≃ₐ[A] S :=
    AlgEquiv.ofBijective (Localization.awayMapₐ D.val d) hkd
  let ρ : S →ₐ[A] A ⧸ I := sd.comp kd.symm.toAlgHom
  have hK : K ≤ RingHom.ker ρ.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change ρ (algebraMap A S a) = 0
    rw [ρ.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  let ρbar := Ideal.Quotient.lift K ρ.toRingHom (fun x hx ↦ hK hx)
  have htleft : Function.LeftInverse ρbar t := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change ρ (algebraMap A S a) = q a
    exact ρ.commutes a
  refine ⟨hint, htleft.injective, ?_⟩
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, rfl⟩ := hFsurj y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((Φ (π x)).1)
  refine ⟨q a, ?_⟩
  have hmem : d * (x - algebraMap A D a) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply Φ.injective
    rw [map_zero]
    simp only [map_mul, map_sub]
    change Φ (π d) * (Φ (π x) - Φ (π (algebraMap A D a))) = 0
    rw [hΦd, hΦ]
    apply Prod.ext
    · simp [ha]
    · simp
  have hmapmem : F (d * (x - algebraMap A D a)) ∈ K := by
    have hmap : J.map F.toRingHom = K := by
      dsimp only [J]
      rw [Ideal.map_map]
      congr 1
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hmem
  have heq : τ (F x) = τ (algebraMap A S a) := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    simpa [hFd] using hmapmem
  exact heq.symm

end Algebra
