/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.CmModuleGoodElementNonzerodivisor
import WeilConjectures.RingTheory.DepthLeSupportDimension
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Dimension drop gives a regular sequence in a Cohen-Macaulay local ring

Source: Stacks Project, Algebra, Proposition 10.103.4 (Tag 00N6), first assertion for
`M = R`; Definition 10.103.1 (Tag 00N3)
(blueprint: lem-weil-pbc-cm-local-dimension-drop-regular-sequence).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

private theorem supportDim_le_quotient_add_length
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (gs : List R) (hmem : ∀ g ∈ gs, g ∈ IsLocalRing.maximalIdeal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.supportDim R M ≤
      Module.supportDim R (M ⧸ Ideal.ofList gs • (⊤ : Submodule R M)) + gs.length := by
  induction gs generalizing M with
  | nil =>
    rw [Ideal.ofList_nil, Submodule.bot_smul]
    simpa using (Module.supportDim_eq_of_equiv
      (Submodule.quotEquivOfEqBot (⊥ : Submodule R M) rfl)).ge
  | cons g gs ih =>
    have hg := hmem g (by simp)
    have hgs : ∀ x ∈ gs, x ∈ IsLocalRing.maximalIdeal R :=
      fun x hx ↦ hmem x (by simp [hx])
    rw [Module.supportDim_eq_of_equiv
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M g gs)]
    calc
      Module.supportDim R M ≤ Module.supportDim R (QuotSMulTop g M) + 1 :=
        Module.supportDim_le_supportDim_quotSMulTop_succ hg
      _ ≤ (Module.supportDim R
          (QuotSMulTop g M ⧸ Ideal.ofList gs • ⊤) + gs.length) + 1 :=
        add_le_add (ih hgs (QuotSMulTop g M)) le_rfl
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc]

private theorem isRegular_of_cm_dimension_drop
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (gs : List R) (hmem : ∀ g ∈ gs, g ∈ IsLocalRing.maximalIdeal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hCM : (IsLocalRing.depth (R := R) M : WithBot ℕ∞) = Module.supportDim R M)
    (hdrop : Module.supportDim R (M ⧸ Ideal.ofList gs • (⊤ : Submodule R M)) +
      gs.length = Module.supportDim R M) : IsRegular M gs := by
  induction gs generalizing M with
  | nil => exact IsRegular.nil R M
  | cons g gs ih =>
    have hg := hmem g (by simp)
    have hgs : ∀ x ∈ gs, x ∈ IsLocalRing.maximalIdeal R :=
      fun x hx ↦ hmem x (by simp [hx])
    have htail := supportDim_le_quotient_add_length gs hgs (QuotSMulTop g M)
    have hequiv := Module.supportDim_eq_of_equiv
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M g gs)
    rw [hequiv, List.length_cons, Nat.cast_add, Nat.cast_one, ← add_assoc] at hdrop
    have hdim : Module.supportDim R (QuotSMulTop g M) + 1 = Module.supportDim R M :=
      le_antisymm ((add_le_add htail (le_rfl : (1 : WithBot ℕ∞) ≤ 1)).trans_eq hdrop)
        (Module.supportDim_le_supportDim_quotSMulTop_succ hg)
    have hgood := Module.cm_module_good_element_nonzerodivisor M hCM g hg (by
      change Order.krullDim (Module.support R (QuotSMulTop g M)) + 1 =
        Order.krullDim (Module.support R M) at hdim
      rw [Module.support_quotSMulTop] at hdim
      exact hdim)
    have hnonzero : Nontrivial (QuotSMulTop g M) :=
      Submodule.Quotient.nontrivial_iff.mpr
        (Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
          ((IsLocalRing.maximalIdeal_le_jacobson _) hg)).symm
    let := hnonzero
    apply (isRegular_cons_iff M g gs).mpr
    refine ⟨hgood.1, ih hgs (QuotSMulTop g M) hgood.2.1 ?_⟩
    exact ENat.WithBot.add_one_cancel.mp (hdrop.trans hdim.symm)

/-- In a finite-dimensional Cohen-Macaulay Noetherian local ring, a list in the maximal
ideal cutting the dimension by its length is regular. Source: Stacks, Tag 00N6, first
assertion for `M = R`; Tag 00N3
(blueprint: lem-weil-pbc-cm-local-dimension-drop-regular-sequence).

Proof plan:
1. Put `I_i = (gs.take i)` and `M_i = R/I_i`. These are finite nonzero modules, since
   `I_i` lies in the maximal ideal. Their annihilators are `I_i`, so their supports are
   `V(I_i)` by lem-weil-pbc-finite-module-support-annihilator. Prime-ideal correspondence
   identifies their support dimensions with the dimensions of the quotient rings.
2. The bound lem-weil-pbc-support-dimension-quotient-element-bound says each step decreases
   dimension by at most one. Summing the bounds before and after each index, and using
   the final dimension hypothesis, shows `dim Supp(M_i) = d - i` at every step.
3. By lem-weil-pbc-depth-le-support-dimension and the depth hypothesis, `M_0 = R` has
   depth equal to support dimension, hence is Cohen-Macaulay.
4. Inductively apply lem-weil-pbc-cm-module-good-element-nonzerodivisor to `M_i` and the
   next element: it is injective on `M_i`, and `M_{i+1}` is again Cohen-Macaulay.
5. These injectivity statements and the nonzero final quotient give `IsRegular R gs`.
   For the empty list, regularity follows from the nonzero ring.

The additive dimension equality encodes integer subtraction without truncating `d - c`.
-/
theorem isRegular_of_dimension_drop {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (hdepth : (d : ℕ∞) ≤ IsLocalRing.depth (R := R) R) (gs : List R)
    (hmem : ∀ g ∈ gs, g ∈ IsLocalRing.maximalIdeal R)
    (hdrop : ringKrullDim (R ⧸ Ideal.ofList gs) + (gs.length : WithBot ℕ∞) =
      (d : WithBot ℕ∞)) :
    IsRegular R gs := by
  have hCM : (IsLocalRing.depth (R := R) R : WithBot ℕ∞) = Module.supportDim R R := by
    apply le_antisymm (IsLocalRing.depth_le_supportDim R)
    rw [Module.supportDim_self_eq_ringKrullDim, hd]
    exact WithBot.coe_le_coe.mpr hdepth
  apply isRegular_of_cm_dimension_drop gs hmem R hCM
  have heq : Ideal.ofList gs • (⊤ : Ideal R) = Ideal.ofList gs := by simp
  change Module.supportDim R (R ⧸ (Ideal.ofList gs • (⊤ : Ideal R))) +
    gs.length = Module.supportDim R R
  rw [heq, Module.supportDim_quotient_eq_ringKrullDim,
    Module.supportDim_self_eq_ringKrullDim, hd]
  exact hdrop

end RingTheory.Sequence
