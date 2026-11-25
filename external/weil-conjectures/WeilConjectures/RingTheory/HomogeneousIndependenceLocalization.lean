/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Nakayama

/-!
# Homogeneous independence survives localization at a rational point

Source: blueprint `lem-wf-height-of-homogeneous-independence`, steps 1 to 3, in the
local dimension argument of `lemma-connected-components-images-homomorphisms--3`, clause (2).
-/

@[expose] public section

open MvPolynomial

namespace AlgHom

/-- Source: blueprint `lem-wf-height-of-homogeneous-independence`, steps 1 to 3,
following Waterhouse, *Introduction to Affine Group Schemes*, §11.4.

Proof in words: put I=ker ε, which is maximal since ε is onto. Its extension to R=A_I
is the maximal ideal m. A fraction a/s has residue ε(a)/ε(s), so every residue
class is represented by k. The spanning congruence extends to m modulo m^2: write an
element as a/s with a in I and s outside I, and divide its coefficients by ε(s).
Nakayama, applied to the finite ideal m, shows that the images of x_i generate m.
For independence, if f(x)/1 belongs to m^(r+1), clearing denominators gives
s f(x) in I^(r+1), with s outside I. Since s-ε(s) belongs to I, and f(x) belongs
to I^r by homogeneity, ε(s)f(x) lies in I^(r+1). The scalar ε(s) is nonzero and
invertible, so f(x) lies in I^(r+1). The original independence hypothesis gives f=0.
No finite-type hypothesis on A over k is needed; Noetherianity supplies finite
generation for Nakayama. The empty-index case gives m=0 by the same argument.
(blueprint: lem-wf-homogeneous-independence-localization). -/
theorem homogeneous_independence_localization
    {k A R ι : Type*} [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
    [CommRing R] [Algebra A R] [Algebra k R] [IsScalarTower k A R]
    [Fintype ι] (ε : A →ₐ[k] k) [(RingHom.ker ε).IsPrime]
    [IsLocalization.AtPrime R (RingHom.ker ε)]
    (x : ι → A) (hx : ∀ i, x i ∈ RingHom.ker ε)
    (hspan : ∀ a ∈ RingHom.ker ε, ∃ c : ι → k,
      a - ∑ i, algebraMap k A (c i) * x i ∈ RingHom.ker ε ^ 2)
    (hind : ∀ (r : ℕ) (f : MvPolynomial ι k), f.IsHomogeneous r →
      aeval x f ∈ RingHom.ker ε ^ (r + 1) → f = 0) :
    (∀ a : R, ∃ c : k,
      a - algebraMap k R c ∈ Ideal.map (algebraMap A R) (RingHom.ker ε)) ∧
    Ideal.map (algebraMap A R) (RingHom.ker ε) =
      Ideal.span (Set.range (fun i ↦ algebraMap A R (x i))) ∧
      ∀ (r : ℕ) (f : MvPolynomial ι k), f.IsHomogeneous r →
        aeval (fun i ↦ algebraMap A R (x i)) f ∈
          (Ideal.map (algebraMap A R) (RingHom.ker ε)) ^ (r + 1) → f = 0 := by
  classical
  let I := RingHom.ker ε
  let m := Ideal.map (algebraMap A R) I
  let z : ι → R := fun i ↦ algebraMap A R (x i)
  have hsurj : Function.Surjective ε := fun c ↦ ⟨algebraMap k A c, ε.commutes c⟩
  have : I.IsMaximal := RingHom.ker_isMaximal_of_surjective ε.toRingHom hsurj
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R I
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing I.primeCompl R inferInstance
  have hm : m = IsLocalRing.maximalIdeal R := IsLocalization.AtPrime.map_eq_maximalIdeal I R
  refine ⟨?_, ?_, ?_⟩
  · intro v
    obtain ⟨a, s, hv⟩ := IsLocalization.exists_mk'_eq I.primeCompl v
    have hs : ε s ≠ 0 := by
      exact fun h ↦ s.property h
    let c : k := ε a / ε s
    have hc : a - algebraMap k A c * s ∈ I := by
      change ε (a - algebraMap k A c * s) = 0
      simp only [map_sub, map_mul, ε.commutes]
      dsimp [c]
      rw [div_mul_cancel₀ _ hs, sub_self]
    refine ⟨c, ?_⟩
    apply (Ideal.unit_mul_mem_iff_mem m (IsLocalization.map_units R s)).mp
    have heq : algebraMap A R s * (v - algebraMap k R c) =
        algebraMap A R (a - algebraMap k A c * s) := by
      rw [mul_sub, mul_comm (algebraMap A R s) v, ← hv, IsLocalization.mk'_spec,
        map_sub, map_mul, ← IsScalarTower.algebraMap_apply k A R]
      ring
    rw [heq]
    exact Ideal.mem_map_of_mem _ hc
  · have hI : I ≤ Ideal.span (Set.range x) ⊔ I ^ 2 := by
      intro a ha
      obtain ⟨c, hc⟩ := hspan a ha
      have hsum : ∑ i, algebraMap k A (c i) * x i ∈ Ideal.span (Set.range x) :=
        Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ Ideal.mem_span_range_self
      have h := (Ideal.span (Set.range x) ⊔ I ^ 2).add_mem
        (Ideal.mem_sup_right hc) (Ideal.mem_sup_left hsum)
      simpa only [sub_add_cancel] using h
    have hmap : m ≤ Ideal.span (Set.range z) ⊔ m ^ 2 := by
      simpa only [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, ← Set.range_comp', m, z]
        using Ideal.map_mono (f := algebraMap A R) hI
    have hJac : m ≤ Ideal.jacobson (⊥ : Ideal R) := by
      rw [hm, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    apply le_antisymm
    · exact Submodule.le_of_le_smul_of_le_jacobson_bot
        (IsNoetherian.noetherian m) hJac (by simpa only [smul_eq_mul, pow_two] using hmap)
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_map_of_mem _ (hx i)
  · intro r f hf hmem
    apply hind r f hf
    have heval : algebraMap A R (aeval x f) = aeval z f := by
      exact MvPolynomial.comp_aeval_apply x (IsScalarTower.toAlgHom k A R) f
    rw [← heval, ← Ideal.map_pow] at hmem
    obtain ⟨s, hs, hmul⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff I.primeCompl R _ _).mp hmem
    exact (Ideal.IsMaximal.mul_mem_pow I hmul).resolve_left hs


end AlgHom
