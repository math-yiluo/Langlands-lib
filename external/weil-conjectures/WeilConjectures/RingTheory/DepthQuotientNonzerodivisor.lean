/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.RingTheory.DepthQuotSMulTop
import WeilConjectures.RingTheory.DepthOverQuotientRing
import WeilConjectures.RingTheory.DepthLeSupportDimension
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Cohen–Macaulay quotients by a nonzerodivisor

Source: Stacks Project, Algebra, Lemma 10.104.2 (Tag 02JN), last assertion for one
regular element (blueprint: lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm).
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A quotient of a Noetherian local Cohen–Macaulay ring by a nonzerodivisor in its
maximal ideal is again Cohen–Macaulay, of dimension one less (Stacks, Tag 02JN)
(blueprint: lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm).

Proof, following the blueprint's five steps:
1. Since `x` lies in the maximal ideal, its principal ideal is proper. The quotient is
nonzero, Noetherian and local, with maximal ideal the image of the original maximal ideal.
The dimension-quotient-nonzerodivisor lemma gives dimension plus one equal to `d`, hence
`d ≥ 1` and quotient dimension `d - 1`.
2. The support-annihilator lemma identifies the supports of `S` and `S/xS` with `Spec S`
and `V(x)`. Prime correspondence identifies the dimension of `V(x)` with that of the
quotient, so intersecting the support with `V(x)` decreases dimension by one.
3. The depth-le-support-dimension lemma and the assumed depth bound show that `S` is a
Cohen–Macaulay module over itself, of depth `d`.
4. The cm-module-good-element-nonzerodivisor lemma (Stacks, Tag 00N5, clause (b)) gives
`S/xS` depth `d - 1` as an `S`-module and makes it Cohen–Macaulay over `S`.
5. Choose a regular sequence of this length in the maximal ideal using the definition
of depth. Its images in the quotient maximal ideal act by the same maps on every
successive module quotient. They therefore form a regular sequence over `S/xS` itself,
which gives the asserted quotient-ring depth bound (change of rings, Tag 0AAD).
-/
theorem depth_quotient_nonzerodivisor
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (d : ℕ) (hd : ringKrullDim S = (d : WithBot ℕ∞))
    (hdepth : (d : ℕ∞) ≤ depth (R := S) S) (x : S)
    (hx : x ∈ maximalIdeal S) (hregular : x ∈ nonZeroDivisors S) :
    ∃ hQ : IsLocalRing (S ⧸ Ideal.span {x}),
      letI := hQ
      IsNoetherianRing (S ⧸ Ideal.span {x}) ∧
      ringKrullDim (S ⧸ Ideal.span {x}) = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
      maximalIdeal (S ⧸ Ideal.span {x}) =
        (maximalIdeal S).map (Ideal.Quotient.mk (Ideal.span {x})) ∧
      ((d - 1 : ℕ) : ℕ∞) ≤ depth (R := S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x}) ∧
      ∃ rs : List (S ⧸ Ideal.span {x}),
        RingTheory.Sequence.IsRegular (S ⧸ Ideal.span {x}) rs ∧
        (∀ y ∈ rs, y ∈ maximalIdeal (S ⧸ Ideal.span {x})) ∧ rs.length = d - 1 := by
  -- Use the proved depth-drop and quotient-ring comparison in place of the historical
  -- support-cutting argument above; attain the finite depth to extract the regular list.
  classical
  let : DistribMulAction S (Submodule S S) := Submodule.pointwiseDistribMulAction
  have hI : Ideal.span {x} ≤ maximalIdeal S := by simpa using hx
  let : Nontrivial (S ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hI)
  let : IsLocalRing (S ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hsucc :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      hregular hx
  rw [hd] at hsucc
  obtain ⟨q, hq⟩ := WithBot.ne_bot_iff_exists.mp
    (ringKrullDim_ne_bot (R := S ⧸ Ideal.span {x}))
  have hqfinite : q ≠ ⊤ := by
    intro htop
    rw [← hq, htop] at hsucc
    have hbad : (⊤ : ℕ∞) + 1 = (d : ℕ∞) := by exact_mod_cast hsucc
    simp at hbad
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hqfinite
  have hnd : n + 1 = d := by
    rw [← hq, ← hn] at hsucc
    exact_mod_cast hsucc
  have hdim : ringKrullDim (S ⧸ Ideal.span {x}) =
      ((d - 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hq, ← hn]
    congr 2
    omega
  have hdepthS : depth (R := S) S = (d : ℕ∞) := by
    apply le_antisymm _ hdepth
    apply WithBot.coe_le_coe.mp
    simpa only [Module.supportDim_self_eq_ringKrullDim, hd, WithBot.coe_natCast] using
      depth_le_supportDim (R := S) S
  have hreg : IsSMulRegular S x :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hregular
  obtain ⟨_, e, he, hS, hQ⟩ := depth_quotSMulTop_of_isSMulRegular S x hx hreg
  have hed : e = d := by
    rw [hdepthS] at hS
    exact_mod_cast hS.symm
  have hsub : x • (⊤ : Submodule S S) = Ideal.span {x} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]
    simp
  change depth (R := S) (S ⧸ x • (⊤ : Submodule S S)) = _ at hQ
  rw [hsub, hed] at hQ
  have hzero : Module.IsTorsionBySet S (S ⧸ Ideal.span {x}) (Ideal.span {x}) := by
    intro y a
    induction y using Quotient.inductionOn with
    | h y =>
      change Ideal.Quotient.mk _ (a.val * y) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.span {x}).mul_mem_right y a.property)
  have hdepthQ : depth (R := S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x}) =
      ((d - 1 : ℕ) : ℕ∞) :=
    (depth_over_quotient_ring S (Ideal.span {x}) hI (S ⧸ Ideal.span {x}) hzero).2.trans hQ
  refine ⟨inferInstance, inferInstance, hdim,
    (map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective).symm,
    hdepthQ.ge, ?_⟩
  have hm : maximalIdeal (S ⧸ Ideal.span {x}) •
      (⊤ : Submodule (S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x})) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator _ _))).symm
  have hdef : depth (R := S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x}) =
      sSup {k : ℕ∞ | ∃ rs : List (S ⧸ Ideal.span {x}),
        RingTheory.Sequence.IsRegular (S ⧸ Ideal.span {x}) rs ∧
        (∀ y ∈ rs, y ∈ maximalIdeal (S ⧸ Ideal.span {x})) ∧
        k = (rs.length : ℕ∞)} := by
    simp only [depth, Ideal.depth, ite_eq_right hm]
  have hmem : depth (R := S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x}) ∈
      {k : ℕ∞ | ∃ rs : List (S ⧸ Ideal.span {x}),
        RingTheory.Sequence.IsRegular (S ⧸ Ideal.span {x}) rs ∧
        (∀ y ∈ rs, y ∈ maximalIdeal (S ⧸ Ideal.span {x})) ∧
        k = (rs.length : ℕ∞)} := by
    rw [hdef]
    let : Nonempty {k : ℕ∞ | ∃ rs : List (S ⧸ Ideal.span {x}),
        RingTheory.Sequence.IsRegular (S ⧸ Ideal.span {x}) rs ∧
        (∀ y ∈ rs, y ∈ maximalIdeal (S ⧸ Ideal.span {x})) ∧
        k = (rs.length : ℕ∞)} :=
      ⟨⟨0, [], by simp [RingTheory.Sequence.isRegular_iff], by simp, rfl⟩⟩
    apply ENat.sSup_mem_of_nonempty_of_lt_top
    rw [← hdef, hdepthQ]
    exact ENat.natCast_lt_top _
  obtain ⟨rs, hrs, hmemrs, hlen⟩ := hmem
  refine ⟨rs, hrs, hmemrs, ?_⟩
  rw [hdepthQ] at hlen
  exact_mod_cast hlen.symm

end IsLocalRing
