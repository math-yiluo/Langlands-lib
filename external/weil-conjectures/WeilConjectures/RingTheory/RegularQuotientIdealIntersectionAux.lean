/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence

/-! Auxiliary inclusion for regular-sequence ideal intersections. -/

@[expose] public section

universe u

namespace Ideal

/-- If a sequence is regular after quotienting by `I`, every element of the
intersection with its generated ideal has coefficients in `I`.
Source: Stacks Project, More on Algebra, Tag 0665, proof of Lemma H1-regular-in-quotient.
(blueprint: aux-regular-quotient-ideal-intersection-inclusion).

Proof: reduce a Koszul degree-one presentation of an element of the
intersection modulo `I`. The reduction is a one-cycle; regularity gives
H₁-vanishing, so it is a boundary. Lift the degree-two boundary and subtract
it from the presentation. The resulting coefficients lie in `I`, proving the
element lies in the product ideal. -/
theorem inf_ofList_le_mul_of_regular_quotient {R : Type u} [CommRing R]
    (I : Ideal R) (gs : List R)
    (hgs : RingTheory.Sequence.IsRegular (R ⧸ I) (gs.map (Ideal.Quotient.mk I))) :
    I ⊓ Ideal.ofList gs ≤ I * Ideal.ofList gs := by
  let := Submodule.pointwiseDistribMulAction (α := R) (R := R) (M := R)
  have hreg : RingTheory.Sequence.IsWeaklyRegular (R ⧸ I) gs := by
    apply (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff
      (R ⧸ I) (R ⧸ I) gs).mp
    simpa only [Ideal.Quotient.algebraMap_eq] using hgs.toIsWeaklyRegular
  have hex := RingTheory.Sequence.map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
    ((LinearMap.exact_zero_iff_injective R I.subtype).mpr I.subtype_injective)
    (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective hreg
  intro x hx
  let xi : I := ⟨x, hx.1⟩
  have hxzero : (Ideal.ofList gs • (⊤ : Submodule R R)).mkQ x = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hx.2
  have himage :
      ((Ideal.ofList gs • (⊤ : Submodule R I)).mapQ
        (Ideal.ofList gs • (⊤ : Submodule R R)) I.subtype
        (Submodule.smul_top_le_comap_smul_top (Ideal.ofList gs) I.subtype))
        ((Ideal.ofList gs • (⊤ : Submodule R I)).mkQ xi) = 0 := by
    simpa only [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply] using hxzero
  obtain ⟨y, hy⟩ := (hex _).mp himage
  have hxi : (Ideal.ofList gs • (⊤ : Submodule R I)).mkQ xi = 0 := by
    simpa only [Submodule.mapQ_zero, LinearMap.zero_apply] using hy.symm
  have hxmem := (Submodule.mem_smul_top_iff (Ideal.ofList gs) I xi).mp
    ((Submodule.Quotient.mk_eq_zero _).mp hxi)
  simpa only [Ideal.smul_eq_mul, Ideal.mul_comm] using hxmem

end Ideal
