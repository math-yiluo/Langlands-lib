/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.KollarLocalDichotomy
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Depth of a normal local domain in dimension at least two

Source: Stacks Project, Algebra, Tag 031S, forward implication, second paragraph.
(blueprint: lem-weil-pbc-normal-local-depth-two).
-/

@[expose] public section

universe u

private theorem finite_extension_surjective
    {A B : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (hi : Function.Injective (algebraMap A B)) (c : A) (hc : c ≠ 0)
    (hr : IsSMulRegular B c)
    (hclear : ∀ b : B, ∃ a : A, algebraMap A B a = c • b) :
    Function.Surjective (algebraMap A B) := by
  classical
  -- The numerator is uniquely determined because the structure map is injective.
  let g : B → A := fun b ↦ (hclear b).choose
  have hg (b : B) : algebraMap A B (g b) = algebraMap A B c * b := by
    simpa only [g, Algebra.smul_def] using (hclear b).choose_spec
  have g_one : g 1 = c := hi (by simpa using hg 1)
  have g_add (b d : B) : g (b + d) = g b + g d := by
    apply hi
    simp only [hg, map_add, mul_add]
  have g_mul (b d : B) : c * g (b * d) = g b * g d := by
    apply hi
    simp only [map_mul, hg]
    ring
  have g_map (a : A) : g (algebraMap A B a) = c * a := by
    apply hi
    simp only [hg, map_mul]
  let K := FractionRing A
  let j := algebraMap A K
  have hj : Function.Injective j := IsFractionRing.injective A K
  have hcn : j c ≠ 0 := fun h ↦ hc (hj (h.trans (map_zero j).symm))
  -- Divide the cleared numerator by the fixed nonzero denominator.
  let f : B →ₐ[A] K :=
    { toFun := fun b ↦ j (g b) / j c
      map_zero' := by
        have gz : g 0 = 0 := hi (by simp [hg])
        simp [gz]
      map_one' := by simp [g_one, hcn]
      map_add' := fun b d ↦ by simp [g_add, add_div]
      map_mul' := fun b d ↦ by
        have hm := congrArg j (g_mul b d)
        simp only [map_mul] at hm
        rw [div_mul_div_comm]
        apply (div_eq_div_iff hcn (mul_ne_zero hcn hcn)).mpr
        calc
          _ = (j c * j (g (b * d))) * j c := by ring
          _ = _ := by rw [hm]
      commutes' := fun a ↦ by
        simp only [g_map, map_mul, mul_div_cancel_left₀ _ hcn]
        rfl }
  have hf : Function.Injective f := by
    intro b d hbd
    have hnum : g b = g d := hj ((div_left_inj' hcn).mp hbd)
    apply hr
    simp only [Algebra.smul_def]
    rw [← hg, ← hg, hnum]
  intro b
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    ((IsIntegral.of_finite A b).map f)
  exact ⟨a, hf (by simpa only [AlgHom.commutes] using ha)⟩

/-- A Noetherian normal local domain of dimension at least two has depth at least two.
Source: Stacks Project, Algebra, Tag 031S, forward implication, second paragraph
(blueprint: lem-weil-pbc-normal-local-depth-two).

Proof: Apply Kollár's local dichotomy (Tag 0BHZ). The Artinian case has dimension zero,
and the regular dimension-one case is excluded by the dimension bound. In the finite
extension case A → B, a power of the maximal ideal kills the kernel. The maximal ideal
contains a nonzero element, so the domain property forces the kernel to vanish. Tag 00LL
provides x in the maximal ideal acting injectively on B. If its nth power kills B/A,
embed B in Frac(A) by sending y to (x^n y)/x^n. This is an injective A-algebra map:
cross-multiplication verifies multiplication, and x^n is regular. Every element of B
is integral because B is finite over A. Integral closedness therefore puts its image
in A. Injectivity makes A → B surjective, contradicting the extension case. Thus the
remaining case of the dichotomy gives depth at least two. -/
theorem IsLocalRing.depth_two_of_normal (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A := by
  classical
  have hfield : ¬ IsField A := by
    intro h
    have hz := ringKrullDim_eq_zero_of_isField h
    rw [hz] at hdim
    norm_num at hdim
  obtain hArt | hreg | hdepth | hext := (IsLocalRing.kollar_local_dichotomy.{u, u} A).1
  · let := hArt
    exact (hfield (IsArtinianRing.isField_of_isDomain A)).elim
  · rw [hreg.2] at hdim
    norm_num at hdim
  · exact hdepth
  · obtain ⟨B, sRing, φ, hB, hfin, hnot, ⟨n, hn, hk, hclear⟩, hass⟩ := hext
    let := sRing
    let := φ.toAlgebra
    let : Nontrivial B := hB
    let : Module.Finite A B := hfin
    have hm : IsLocalRing.maximalIdeal A ≠ ⊥ :=
      fun h ↦ hfield (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    obtain ⟨x, hx, hx0⟩ : ∃ x : A, x ∈ IsLocalRing.maximalIdeal A ∧ x ≠ 0 := by
      by_contra! h
      exact hm (le_antisymm (fun x hx ↦ h x hx) bot_le)
    have hi : Function.Injective φ := by
      apply (RingHom.injective_iff_ker_eq_bot φ).mpr
      apply le_antisymm _ bot_le
      intro a ha
      have hz := Ideal.mul_mem_mul (Ideal.pow_mem_pow hx n) ha
      rw [hk] at hz
      exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero n hx0)
    have hna : IsLocalRing.maximalIdeal A ∉ associatedPrimes A B := by
      intro h
      obtain ⟨_, z, hz⟩ := isAssociatedPrime_iff.mp h
      apply hass
      refine ⟨z, ?_⟩
      intro a
      rw [hz]
      simp [Submodule.mem_colon_singleton, Algebra.smul_def]
      rfl
    obtain ⟨y, hy, hry⟩ := exists_mem_maximalIdeal_smul_injective A B hna
    have hy0 : y ≠ 0 := by
      intro h
      have : (0 : B) = 1 := hry (by simp [h])
      exact zero_ne_one this
    exfalso
    apply hnot
    refine ⟨hi, finite_extension_surjective hi (y ^ n) (pow_ne_zero n hy0)
      (hry.pow n) ?_⟩
    intro b
    have hz : φ (y ^ n) * b ∈ Ideal.map φ ((IsLocalRing.maximalIdeal A) ^ n) :=
      Ideal.mul_mem_right b _ (Ideal.mem_map_of_mem φ (Ideal.pow_mem_pow hy n))
    exact hclear _ hz

