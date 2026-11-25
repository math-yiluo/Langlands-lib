/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Ideal.Pure

/-!
# Isomorphisms modulo powers of an ideal under a flat ring map

Source: Stacks Project, More on Algebra, proof of Tag 0AGU, using Algebra, Tag 051H
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v

namespace RingHom

-- Quotient base change preserves flatness.
private theorem flat_quotientMap {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.Flat) (J : Ideal A) :
    (Ideal.quotientMap (J.map φ) φ Ideal.le_comap_map).Flat := by
  let := φ.toAlgebra
  let : Module.Flat A B := hφ
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B J
  have h : Module.Flat (A ⧸ J) (B ⧸ J.map (algebraMap A B)) :=
    Module.Flat.of_linearEquiv e.toLinearEquiv
  exact (RingHom.flat_algebraMap_iff).mpr h

-- Successively lift representatives using surjectivity modulo I.
private theorem surjective_mkQ_pow {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : R →ₗ[R] M)
    (h : Function.Surjective ((I • ⊤ : Submodule R M).mkQ ∘ₗ f)) (n : ℕ) :
    Function.Surjective ((I ^ n • ⊤ : Submodule R M).mkQ ∘ₗ f) := by
  induction n with
  | zero =>
    intro y
    refine ⟨0, ?_⟩
    have : Subsingleton (M ⧸ (I ^ 0 • ⊤ : Submodule R M)) := by
      simp only [pow_zero, one_smul]
      infer_instance
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro y
    obtain ⟨x, hx⟩ := ih
      (Submodule.factor (Submodule.pow_smul_top_le I M n.le_succ) y)
    obtain ⟨x', _, hx'⟩ := AdicCompletion.exists_smodEq_pow_smul_top_and_mkQ_eq h
      (hyy' := rfl) hx
    exact ⟨x', hx'⟩

-- A pure ideal is idempotent, and a nilpotent idempotent ideal is zero.
private theorem injective_of_flat_surjective_nilpotent_ker {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (hs : Function.Surjective f) (hk : IsNilpotent (RingHom.ker f)) :
    Function.Injective f := by
  let := f.toAlgebra
  let : Module.Flat R S := hf
  let e := RingHom.quotientKerEquivOfSurjective hs
  let eₗ : (R ⧸ RingHom.ker f) ≃ₗ[R] S :=
    { __ := e.toAddEquiv
      map_smul' r x := by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp [Algebra.smul_def, e, f.algebraMap_toAlgebra] }
  let : (RingHom.ker f).Pure := Module.Flat.of_linearEquiv eₗ
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  obtain ⟨n, hn⟩ := hk
  have hid := Ideal.isIdempotentElem_of_pure (RingHom.ker f)
  rcases n with _ | n
  · have ht : (⊤ : Ideal R) = ⊥ := by simpa using hn
    exact bot_unique (ht ▸ le_top)
  · simpa [hid.pow_succ_eq n] using hn

/-- A flat ring map that induces an isomorphism modulo an ideal induces an isomorphism
modulo every positive power of that ideal. Here `Ideal.map` is extension of the ideal,
and bijectivity of the induced ring homomorphism expresses that this map is an isomorphism.
Source: Stacks Project, proof of Tag 0AGU, referring to Tag 051H
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof: Write βₙ for the induced map on quotients and αₙ for the induced map
`I^n / I^(n+1) → I^n B / I^(n+1) B`. The inclusion and reduction maps give two short
exact rows with vertical maps αₙ, βₙ₊₁, βₙ, and the squares commute.
Surjectivity of β₁ gives `B = φ(A) + IB`. Writing each coefficient of a generator
`φ(x)b` of `I^n B` in this form gives `I^n B = φ(I^n) + I^(n+1) B`, so αₙ is surjective.
For injectivity, put `N = I^n / I^(n+1)`, annihilated by I. The inverse of β₁ defines
an A-linear retraction of `N → N ⊗[A] B`, by sending `x ⊗ b` to `β₁⁻¹(b mod IB) • x`.
Flatness (def-weil-pbc-flat-ring-map) makes the tensor of `N → A/I^(n+1)` injective.
The tensor-quotient isomorphism (lem-weil-pbc-tensor-quotient-base-change) identifies
its target with `B/I^(n+1) B`. The composite on N is the inclusion composed with αₙ,
so αₙ is injective. Starting with β₁, induction and the short five lemma
(lem-weil-pbc-short-five-lemma) now show that every βₙ for n ≥ 1 is bijective.
A bijective ring homomorphism has an additive and multiplicative inverse. -/
theorem bijective_quotientMap_pow_of_flat {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.Flat) (I : Ideal A)
    (hI : Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    ∀ n : ℕ, 1 ≤ n → Function.Bijective
      (Ideal.quotientMap ((I ^ n).map φ) φ Ideal.le_comap_map) := by
  let := φ.toAlgebra
  let f := (Algebra.ofId A B).toLinearMap
  have hsurj : Function.Surjective
      ((I • ⊤ : Submodule A B).mkQ ∘ₗ f) := by
    rw [Ideal.smul_top_eq_map]
    intro y
    obtain ⟨x, hx⟩ := hI.2 y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, hx⟩
  intro n hn
  let β := Ideal.quotientMap ((I ^ n).map φ) φ Ideal.le_comap_map
  have hs : Function.Surjective β := by
    have h := surjective_mkQ_pow I f hsurj n
    rw [Ideal.smul_top_eq_map] at h
    intro y
    obtain ⟨a, ha⟩ := h y
    exact ⟨Ideal.Quotient.mk (I ^ n) a, ha⟩
  have hker : RingHom.ker β ≤ I.map (Ideal.Quotient.mk (I ^ n)) := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hmem : φ a ∈ I.map φ := by
      apply Ideal.map_mono (Ideal.pow_le_self (Nat.ne_of_gt hn))
      simpa [β, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
    have ha : a ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply hI.1
      simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
    exact Ideal.mem_map_of_mem _ ha
  have hk : IsNilpotent (RingHom.ker β) := by
    refine ⟨n, ?_⟩
    apply bot_unique
    calc
      RingHom.ker β ^ n ≤ (I.map (Ideal.Quotient.mk (I ^ n))) ^ n :=
        pow_le_pow_left' hker n
      _ = (I ^ n).map (Ideal.Quotient.mk (I ^ n)) := (Ideal.map_pow _ _ _).symm
      _ = ⊥ := by simp
  exact ⟨injective_of_flat_surjective_nilpotent_ker β (flat_quotientMap φ hφ _) hs hk, hs⟩

end RingHom
