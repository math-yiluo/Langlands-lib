/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.GroupRingAction
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Invariants of a strictly henselian local ring under an inertia-type action

Let `A` be a local ring and `G` a group acting on `A` by ring automorphisms which act trivially
on the residue field: `g • x - x ∈ 𝔪_A` for all `g` and `x`. Then the fixed subring `A^G` is a
local ring whose units are the invariant units of `A`
(`FixedPoints.isLocalRing_subring`). If `A` is henselian, so is `A^G`; if `A` is strictly
henselian, so is `A^G` (`FixedPoints.isStrictlyHenselianLocalRing_subring`). Both rest on the
uniqueness of henselian lifts of simple roots
(`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`): `G` permutes the roots of an invariant
polynomial lifting a given simple residue root, so it fixes the unique one.

For `A` the localization at a point `Q` over a boundary point `z` of the integral closure of a
Dedekind ring in a separable closure of its fraction field and `G` the inertia group of `Q`,
`A^G` is the strict henselization at `z`, the strictly henselian pro-étale neighbourhood used to
compute boundary stalks (blueprint `lemma-boundary-stalk--1`).
-/

@[expose] public section

open Polynomial IsLocalRing

namespace FixedPoints

variable {A : Type*} [CommRing A] (G : Type*) [Group G] [MulSemiringAction G A]

/-- An invariant element is a unit among the invariants iff it is a unit. -/
lemma isUnit_subring_iff (x : FixedPoints.subring A G) : IsUnit x ↔ IsUnit (x : A) := by
  refine ⟨fun h ↦ h.map (FixedPoints.subring A G).subtype, fun ⟨u, hu⟩ ↦ ?_⟩
  have hinv : (↑u⁻¹ : A) ∈ FixedPoints.subring A G := fun g ↦ by
    have hx : g • (x : A) = x := x.2 g
    rw [← hu] at hx
    have h' : g • ((u⁻¹ : Aˣ) : A) * g • (u : A) = 1 := by
      rw [← smul_mul', Units.inv_mul, smul_one]
    rw [hx] at h'
    calc g • ((u⁻¹ : Aˣ) : A) = g • ((u⁻¹ : Aˣ) : A) * ((u : A) * ((u⁻¹ : Aˣ) : A)) := by
            rw [Units.mul_inv, mul_one]
      _ = ((u⁻¹ : Aˣ) : A) := by rw [← mul_assoc, h', one_mul]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change (x : A) * ((u⁻¹ : Aˣ) : A) = 1
  rw [← hu, Units.mul_inv]

/-- The invariants of a local ring form a local ring. -/
theorem isLocalRing_subring [IsLocalRing A] : IsLocalRing (FixedPoints.subring A G) := by
  have : Nontrivial (FixedPoints.subring A G) :=
    ⟨⟨0, 1, fun h ↦ zero_ne_one (congrArg Subtype.val h : (0 : A) = 1)⟩⟩
  refine IsLocalRing.of_nonunits_add fun x y hx hy hxy ↦ ?_
  rw [mem_nonunits_iff, isUnit_subring_iff] at hx hy
  rw [isUnit_subring_iff] at hxy
  exact IsLocalRing.nonunits_add hx hy (by simpa using hxy)

attribute [local instance] isLocalRing_subring

/-- The maximal ideal of the invariants is the preimage of the maximal ideal. -/
lemma mem_maximalIdeal_subring_iff [IsLocalRing A] (x : FixedPoints.subring A G) :
    x ∈ maximalIdeal (FixedPoints.subring A G) ↔ (x : A) ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_subring_iff]

variable {G}

/-- An element acting trivially on the residue field preserves the maximal ideal. -/
lemma smul_mem_maximalIdeal_iff [IsLocalRing A]
    (hG : ∀ g : G, ∀ x : A, g • x - x ∈ maximalIdeal A) (g : G) (x : A) :
    g • x ∈ maximalIdeal A ↔ x ∈ maximalIdeal A := by
  constructor
  · intro h
    have := (maximalIdeal A).sub_mem h (hG g x)
    rwa [sub_sub_cancel] at this
  · intro h
    have := (maximalIdeal A).add_mem (hG g x) h
    rwa [sub_add_cancel] at this

/-- **The invariants of a henselian local ring under a group acting trivially on the residue
field are henselian.** -/
theorem henselianLocalRing_subring [HenselianLocalRing A]
    (hG : ∀ g : G, ∀ x : A, g • x - x ∈ maximalIdeal A) :
    HenselianLocalRing (FixedPoints.subring A G) where
  is_henselian f hf a₀ h₁ h₂ := by
    let fA := f.map (FixedPoints.subring A G).subtype
    have hev (b : FixedPoints.subring A G) :
        fA.eval (b : A) = ((f.eval b : FixedPoints.subring A G) : A) := by
      simp only [fA, eval_map]
      exact eval₂_at_apply (FixedPoints.subring A G).subtype b
    have hev' (b : FixedPoints.subring A G) :
        fA.derivative.eval (b : A) = ((f.derivative.eval b : FixedPoints.subring A G) : A) := by
      rw [show fA.derivative = f.derivative.map (FixedPoints.subring A G).subtype from
        derivative_map _ _]
      simp only [eval_map]
      exact eval₂_at_apply (FixedPoints.subring A G).subtype b
    have h₁' : fA.eval (a₀ : A) ∈ maximalIdeal A := by
      rw [hev]
      exact (mem_maximalIdeal_subring_iff G _).1 h₁
    have h₂' : IsUnit (fA.derivative.eval (a₀ : A)) := by
      rw [hev']
      exact h₂.map (FixedPoints.subring A G).subtype
    obtain ⟨a, ha, haa₀⟩ := HenselianLocalRing.is_henselian fA (hf.map _) _ h₁' h₂'
    -- the derivative at `a` is a unit
    have hua : IsUnit (fA.derivative.eval a) := by
      by_contra hn
      obtain ⟨k, hk⟩ := fA.derivative.binomExpansion a ((a₀ : A) - a)
      rw [add_sub_cancel] at hk
      have hm : (a₀ : A) - a ∈ maximalIdeal A := by
        rw [← neg_sub]
        exact (maximalIdeal A).neg_mem haa₀
      refine ((mem_maximalIdeal _).1 ?_) h₂'
      rw [hk]
      exact (maximalIdeal A).add_mem ((maximalIdeal A).add_mem ((mem_maximalIdeal _).2 hn)
        ((maximalIdeal A).mul_mem_left _ hm)) ((maximalIdeal A).mul_mem_left _
          ((maximalIdeal A).pow_mem_of_mem hm 2 two_pos))
    -- `a` is invariant
    have hfix : a ∈ FixedPoints.subring A G := fun g ↦ by
      have hfA : g • fA = fA := by
        ext n
        simp only [fA, coeff_smul, coeff_map, Subring.subtype_apply]
        exact (f.coeff n).2 g
      have hroot : fA.IsRoot (g • a) := by
        rw [IsRoot, ← hfA, smul_eval_smul, ha.eq_zero, smul_zero]
      exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ha hroot
        (fun hu' ↦ (mem_maximalIdeal _).1 (hG g a) (by simpa using hu'.neg)) hua).symm
    refine ⟨⟨a, hfix⟩, ?_, ?_⟩
    · apply Subtype.ext
      rw [← hev]
      exact ha.eq_zero
    · rw [mem_maximalIdeal_subring_iff]
      exact haa₀
variable (G) in
instance isLocalHom_subtype [IsLocalRing A] :
    IsLocalHom (FixedPoints.subring A G).subtype :=
  ⟨fun x hx ↦ (isUnit_subring_iff G x).2 hx⟩

/-- **The invariants of a strictly henselian local ring under a group acting trivially on the
residue field are strictly henselian.** The residue field of the invariants is separably closed:
a simple residue root of a separable polynomial lifts to a root in `A`, which is invariant by
uniqueness of henselian lifts. -/
theorem isStrictlyHenselianLocalRing_subring [IsStrictlyHenselianLocalRing A]
    (hG : ∀ g : G, ∀ x : A, g • x - x ∈ maximalIdeal A) :
    IsStrictlyHenselianLocalRing (FixedPoints.subring A G) where
  toHenselianLocalRing := henselianLocalRing_subring hG
  isSepClosed_residueField := by
    refine IsSepClosed.of_exists_root _ fun p hp hirr hsep ↦ ?_
    let S := FixedPoints.subring A G
    let φ := ResidueField.map S.subtype
    -- lift `p` to a monic polynomial `P` over the invariants
    obtain ⟨P, hPp, -, hPm⟩ := lifts_and_degree_eq_and_monic
      (map_surjective _ (residue_surjective (R := S)) p) hp
    let PA := P.map S.subtype
    have hPA : PA.map (residue A) = p.map φ := by
      rw [← hPp, map_map, map_map]
      rfl
    -- a simple root of `p` in the residue field of `A`, lifted to `A`
    have hdeg : (p.map φ).degree ≠ 0 := by
      rw [degree_map]
      exact fun h ↦ hirr.not_isUnit (isUnit_iff_degree_eq_zero.2 h)
    obtain ⟨β, hβ⟩ := IsSepClosed.exists_root (p.map φ) hdeg hsep.map
    obtain ⟨b₀, rfl⟩ := residue_surjective β
    have hev (Q : A[X]) (x : A) : residue A (Q.eval x) = (Q.map (residue A)).eval (residue A x) :=
      (eval_map_apply ..).symm
    have h₁ : PA.eval b₀ ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff, hev, hPA, hβ]
    have h₂ : IsUnit (PA.derivative.eval b₀) := by
      by_contra hn
      rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, hev,
        ← derivative_map, hPA, derivative_map, eval_map] at hn
      rw [IsRoot, eval_map] at hβ
      exact hsep.eval₂_derivative_ne_zero φ hβ hn
    obtain ⟨b, hb, hbb₀⟩ := HenselianLocalRing.is_henselian PA (hPm.map _) _ h₁ h₂
    have hub : IsUnit (PA.derivative.eval b) := by
      by_contra hn
      have hm : PA.derivative.eval b₀ - PA.derivative.eval b ∈ maximalIdeal A := by
        obtain ⟨c, hc⟩ := sub_dvd_eval_sub b₀ b PA.derivative
        rw [hc]
        refine (maximalIdeal A).mul_mem_right _ ?_
        rw [← neg_sub]
        exact (maximalIdeal A).neg_mem hbb₀
      have := (maximalIdeal A).add_mem hm ((mem_maximalIdeal _).2 hn)
      rw [sub_add_cancel] at this
      exact ((mem_maximalIdeal _).1 this) h₂
    -- the root `b` is invariant
    have hfix : b ∈ S := fun g ↦ by
      have hfA : g • PA = PA := by
        ext n
        simp only [PA, coeff_smul, coeff_map, Subring.subtype_apply]
        exact (P.coeff n).2 g
      have hroot : PA.IsRoot (g • b) := by
        rw [IsRoot, ← hfA, smul_eval_smul, hb.eq_zero, smul_zero]
      exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hb hroot
        (fun hu' ↦ (mem_maximalIdeal _).1 (hG g b) (by simpa using hu'.neg)) hub).symm
    refine ⟨residue S ⟨b, hfix⟩, ?_⟩
    rw [← hPp, eval_map, eval₂_at_apply]
    have : P.eval (⟨b, hfix⟩ : S) = 0 := Subtype.ext (by
      change S.subtype (P.eval ⟨b, hfix⟩) = 0
      rw [← eval₂_at_apply, ← eval_map]
      exact hb.eq_zero)
    rw [this, map_zero]

end FixedPoints
