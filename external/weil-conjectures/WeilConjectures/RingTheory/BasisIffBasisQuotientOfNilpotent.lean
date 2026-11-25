/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.NakayamaNilpotent
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Lifting bases over a local ring with nilpotent maximal ideal

Source: Stacks Project, Algebra, Lemma 10.101.1, Tag 051F
(blueprint: lem-weil-pbc-local-artinian-basis-when-flat).
-/

@[expose] public section

universe u v w

namespace Module

/-- A family in a flat module over a local ring with nilpotent maximal ideal is a basis
if and only if its reductions form a basis over the residue field. No finite generation
of the module or finiteness of the index type is assumed.

Source: Stacks Project, Algebra, Lemma 10.101.1, Tag 051F
(blueprint: lem-weil-pbc-local-artinian-basis-when-flat).

Proof: Identify (R/m) tensor M with M/mM by
TensorProduct.quotTensorEquivQuotSMul, upgraded to an R/m-linear equivalence using
surjectivity of R -> R/m. A basis of M reduces to a basis by Basis.baseChange and
this equivalence. Conversely, transport a basis of M/mM to (R/m) tensor M.
Mathlib's Module.IsLocalRing.linearIndependent_of_flat shows that the lifted
family x is R-linearly independent, without any finiteness assumption.
Let L be the R-span of x. Since R -> R/m is surjective, the R-span of the reduced
family is also all of M/mM (Submodule.restrictScalars_span). Thus the image of
L under M -> M/mM is all of M/mM, and the induced map L/mL -> M/mM is surjective.
Apply nilpotent Nakayama (lem-weil-pbc-nakayama-nilpotent) to the inclusion L -> M
to obtain L = M. Basis.mk combines this spanning assertion with independence,
and its value at each index is x at that index. -/
theorem basis_iff_basisQuotient_of_nilpotent
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hm : IsNilpotent (IsLocalRing.maximalIdeal R)) {A : Type w} (x : A → M) :
    (∃ b : Basis A (R ⧸ IsLocalRing.maximalIdeal R)
      (M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))),
      ∀ a : A, b a = (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ (x a)) ↔
    (∃ b : Basis A R M, ∀ a : A, b a = x a) := by
  classical
  let I := IsLocalRing.maximalIdeal R
  let Q := I • (⊤ : Submodule R M)
  let e : TensorProduct R (R ⧸ I) M ≃ₗ[R ⧸ I] (M ⧸ Q) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective (I := I))
  constructor
  · rintro ⟨b, hb⟩
    have hx : (fun a ↦ Q.mkQ (x a)) = b := funext fun a ↦ (hb a).symm
    have hli : LinearIndependent R x := by
      have ht : (fun a ↦ e.symm (b a)) =
          TensorProduct.mk R (R ⧸ I) M 1 ∘ x := by
        funext a
        rw [hb a]
        rfl
      have hi := (b.map e.symm).linearIndependent
      change LinearIndependent (R ⧸ I) (fun a ↦ e.symm (b a)) at hi
      rw [ht] at hi
      exact Module.IsLocalRing.linearIndependent_of_flat x hi
    let L := Submodule.span R (Set.range x)
    have hspan : Submodule.span R (Set.range (fun a ↦ Q.mkQ (x a))) = ⊤ := by
      rw [hx, ← Submodule.restrictScalars_span R (R ⧸ I)
        (Ideal.Quotient.mk_surjective (I := I)), b.span_eq]
      rfl
    have hmap : L.map Q.mkQ = ⊤ := by
      change (Submodule.span R (Set.range x)).map Q.mkQ = ⊤
      rw [Submodule.map_span, ← Set.range_comp]
      exact hspan
    have hsurj : Function.Surjective (Q.mkQ.comp L.subtype) := by
      apply LinearMap.range_eq_top.mp
      simpa only [LinearMap.range_comp, Submodule.range_subtype] using hmap
    have hmod : Function.Surjective
        ((I • ⊤ : Submodule R L).mapQ Q L.subtype
          (Submodule.smul_top_le_comap_smul_top I L.subtype)) := by
      intro y
      obtain ⟨z, hz⟩ := hsurj y
      exact ⟨(I • ⊤ : Submodule R L).mkQ z, hz⟩
    have hI : ∃ k : ℕ, 0 < k ∧ I ^ k = ⊥ := by
      obtain ⟨k, hk⟩ := hm
      exact ⟨k + 1, Nat.succ_pos _, by rw [pow_succ, hk, zero_mul]; rfl⟩
    have hL := RingTheory.surjective_of_surjective_mod_nilpotent R L M I L.subtype hI hmod
    have htop : L = ⊤ := by
      simpa only [Submodule.range_subtype] using LinearMap.range_eq_top.mpr hL
    exact ⟨Basis.mk hli htop.ge, fun a ↦ Basis.mk_apply _ _ a⟩
  · rintro ⟨b, hb⟩
    refine ⟨(b.baseChange (R ⧸ I)).map e, ?_⟩
    intro a
    change (TensorProduct.quotTensorEquivQuotSMul M I)
      ((b.baseChange (R ⧸ I)) a) = Q.mkQ (x a)
    simpa only [Basis.baseChange_apply, hb a, Submodule.mkQ_apply] using
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I (x a)

end Module
