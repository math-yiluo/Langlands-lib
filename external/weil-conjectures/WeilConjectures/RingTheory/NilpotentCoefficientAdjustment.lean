/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import WeilConjectures.RingTheory.SquareZeroCoefficientAdjustment
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Finite coefficient adjustment for a nilpotent local algebra

Source: Stacks Project, Tag 07FG, the induction proving the coefficient-field claim.
(blueprint: lem-weil-pbc-nilpotent-coefficient-adjustment)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

-- Keep the residue field fixed during induction, so no cotangent-homology transport
-- is needed when passing to a quotient of the local ring.
private theorem exists_coefficient_adjustment_of_pow_eq_bot
    (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (hH : Module.Finite K (H1Cotangent k K)) (n : ℕ) :
    ∀ (Λ : Type v) [CommRing Λ] [Algebra k Λ] [IsLocalRing Λ]
      (r : Λ →+* K), Function.Surjective r →
      RingHom.ker r = IsLocalRing.maximalIdeal Λ →
      r.comp (algebraMap k Λ) = algebraMap k K →
      ∀ (t : Finset Λ), Ideal.span (t : Set Λ) = IsLocalRing.maximalIdeal Λ →
      IsLocalRing.maximalIdeal Λ ^ n = ⊥ →
      ∃ (σ : K →+* Λ) (c : Finset K),
        r.comp σ = RingHom.id K ∧
        (∀ a : k, algebraMap k Λ a ∈ Subring.closure ((t : Set Λ) ∪
          σ '' (IntermediateField.adjoin k (c : Set K) : Set K))) := by
  classical
  induction n with
  | zero =>
      intro Λ _ _ _ r hr hker hcomm t ht hn
      simp [Ideal.one_eq_top] at hn
  | succ n ih =>
      intro Λ _ _ _ r hr hker hcomm t ht hn
      by_cases hn0 : n = 0
      · have hm : IsLocalRing.maximalIdeal Λ = ⊥ := by simpa [hn0] using hn
        have hinj : Function.Injective r :=
          (RingHom.injective_iff_ker_eq_bot r).mpr (hker.trans hm)
        let e := RingEquiv.ofBijective r ⟨hinj, hr⟩
        refine ⟨e.symm.toRingHom, ∅, ?_, ?_⟩
        · ext a
          exact e.apply_symm_apply a
        · intro a
          have ha : algebraMap k Λ a = e.symm (algebraMap k K a) := by
            apply hinj
            exact (RingHom.congr_fun hcomm a).trans (e.apply_symm_apply _).symm
          rw [ha]
          apply Subring.subset_closure
          exact Or.inr ⟨algebraMap k K a, IntermediateField.algebraMap_mem _ a, rfl⟩
      · let I := IsLocalRing.maximalIdeal Λ ^ n
        have hI : I ≤ RingHom.ker r := by
          rw [hker]
          exact Ideal.pow_le_self hn0
        have hIne : I ≠ ⊤ := by
          intro htop
          have hle : (⊤ : Ideal Λ) ≤ IsLocalRing.maximalIdeal Λ := by
            simpa [htop, hker] using hI
          exact (IsLocalRing.maximalIdeal.isMaximal Λ).ne_top (top_le_iff.mp hle)
        let : Nontrivial (Λ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
        let q := Ideal.Quotient.mk I
        let : IsLocalRing (Λ ⧸ I) :=
          IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
        let r' := Ideal.Quotient.lift I r (fun x hx ↦ hI hx)
        have hr' : Function.Surjective r' := by
          intro a
          obtain ⟨b, rfl⟩ := hr a
          exact ⟨q b, rfl⟩
        have hmap : (IsLocalRing.maximalIdeal Λ).map q =
            IsLocalRing.maximalIdeal (Λ ⧸ I) :=
          IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
        have hker' : RingHom.ker r' = IsLocalRing.maximalIdeal (Λ ⧸ I) := by
          rw [Ideal.ker_quotient_lift, hker]
          exact hmap
        have hcomm' : r'.comp (algebraMap k (Λ ⧸ I)) = algebraMap k K := by
          ext a
          change r (algebraMap k Λ a) = algebraMap k K a
          exact RingHom.congr_fun hcomm a
        let t' := t.image q
        have ht' : Ideal.span (t' : Set (Λ ⧸ I)) =
            IsLocalRing.maximalIdeal (Λ ⧸ I) := by
          rw [← hmap, ← ht, Ideal.map_span]
          simp [t']
        have hn' : IsLocalRing.maximalIdeal (Λ ⧸ I) ^ n = ⊥ := by
          rw [← hmap, ← Ideal.map_pow]
          exact Ideal.map_quotient_self I
        obtain ⟨σ', c', hσ', hc'⟩ :=
          ih (Λ ⧸ I) r' hr' hker' hcomm' t' ht' hn'
        have hkill : IsLocalRing.maximalIdeal Λ * I = ⊥ := by
          change IsLocalRing.maximalIdeal Λ * IsLocalRing.maximalIdeal Λ ^ n = ⊥
          rw [← pow_succ']
          exact hn
        have hc'' : ∀ a : k, algebraMap k (Λ ⧸ I) a ∈
            Subring.closure (q '' (t : Set Λ) ∪
              σ' '' (IntermediateField.adjoin k (c' : Set K) : Set K)) := by
          simpa [t'] using hc'
        obtain ⟨σ, c, hσ, _, hc⟩ := exists_square_zero_coefficient_adjustment
          k K Λ r hr hker hcomm t ht ⟨n + 1, hn⟩ I hI hkill σ' c' hσ' hc'' p hp hH
        exact ⟨σ, c, hσ, hc⟩

/-- Adjust the coefficient section for a fixed generating family of a nilpotent maximal ideal.
The section need not preserve the base-field algebra structure. The containment is in
ring closure, so it is not automatic from the algebra structure.

Source: Stacks Project, Tag 07FG, proof of the claim and the paragraph beginning
"Choose sigma and F as in the claim" (steps 2--7 of the parent node)
(blueprint: lem-weil-pbc-nilpotent-coefficient-adjustment).

Proof:
1. The given maximal ideal is nilpotent and the fixed finite set t generates it.
   In positive characteristic the residue field has a ring section by formal smoothness
   over the prime field (Tag 0320).
2. Induct on the nilpotence exponent n to adjust this section so that the image of k lies
   in the ring generated by t and a subfield finitely generated over k. For n=1 the ring is
   its residue field and the section is the inverse of the residue map; no coefficients
   beyond k are needed.
3. For n>1 pass to the quotient by I=m^(n-1). Here I^2=mI=0. Apply induction, then lift the
   resulting section and the map from k into the truncated polynomial algebra along their
   nilpotent kernels, using Tag 0320 as in the field lifting node.
4. The discrepancy between the lifted map and the structure map is a derivation k -> I.
   Changing the section by a derivation K -> I subtracts its restriction to k from that
   discrepancy. Positive degree monomials do not contribute, because mI=0.
5. Exactness of the Jacobi--Zariski sequence at K tensor Omega_k, and finite dimensionality
   of H1(K/k), put its kernel in the span of finitely many members of a differential basis
   dy_j. The remaining images are independent in Omega_K. Extend them to a basis and choose
   a linear map Omega_K -> I agreeing with the discrepancy on them. Its derivation adjusts
   the section so that the remaining discrepancy has only finitely many values f_j.
6. Write each f_j as a linear combination over K of degree n-1 monomials in t. Adjoin their
   finitely many coefficients to the field supplied by induction. In each term i(a_j)f_j,
   replace i(a_j) by sigma(residue(a_j)): their difference lies in m and mI=0. Its residue
   belongs to k, so this term is in the polynomial image over the enlarged field. The lifted
   map is also in that image. Their sum, the structure map, is too. A generating set c gives
   the closure
   clause below. This uses ring closure rather than k-algebra generation, so the clause does
   not become automatic merely because the structure map is part of an algebra structure.
7. Choose c to be the union of the finite coefficient set from induction and the finite
   set of coefficients introduced in step 6. Its intermediate-field adjoin contains all
   coefficients used, so ring closure under sums and products proves the containment. -/
theorem exists_nilpotent_coefficient_adjustment
    (k : Type u) [Field k] (Λ : Type v) [CommRing Λ] [Algebra k Λ]
    [IsLocalRing Λ] (t : Finset Λ)
    (ht : Ideal.span (t : Set Λ) = IsLocalRing.maximalIdeal Λ)
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal Λ))
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (hH : Module.Finite (IsLocalRing.ResidueField Λ)
      (H1Cotangent k (IsLocalRing.ResidueField Λ))) :
    ∃ (σ : IsLocalRing.ResidueField Λ →+* Λ)
      (c : Finset (IsLocalRing.ResidueField Λ)),
      (IsLocalRing.residue Λ).comp σ = RingHom.id _ ∧
      (∀ a : k, algebraMap k Λ a ∈ Subring.closure ((t : Set Λ) ∪
        σ '' (IntermediateField.adjoin k (c : Set (IsLocalRing.ResidueField Λ)) :
          Set (IsLocalRing.ResidueField Λ)))) := by
  obtain ⟨n, hn⟩ := hnil
  exact exists_coefficient_adjustment_of_pow_eq_bot k (IsLocalRing.ResidueField Λ)
    p hp hH n Λ (IsLocalRing.residue Λ) IsLocalRing.residue_surjective
    IsLocalRing.ker_residue (by
      ext a
      exact (IsScalarTower.algebraMap_apply k Λ (IsLocalRing.ResidueField Λ) a).symm)
    t ht hn

end Algebra
