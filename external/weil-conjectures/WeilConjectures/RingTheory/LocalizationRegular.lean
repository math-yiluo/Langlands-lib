/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization maps are regular

Source: Stacks Project, More on Algebra, proof of Lemma 07PT and Definition 07BZ;
Algebra, Lemmas 00HT, 00DK and 00CQ, Proposition 00CP
(blueprint: lem-weil-pbc-localization-regular).
-/

@[expose] public section

universe u v

namespace IsLocalization

private theorem regular_of_field (k : Type*) (A : Type*) [Field k] [CommRing A]
    [Algebra k A] (M : Submonoid k) [IsLocalization M A] : IsRegularRing A := by
  classical
  by_cases h : (0 : k) ∈ M
  · have : Subsingleton A := (IsLocalization.subsingleton_iff).mpr h
    refine ⟨fun p hp ↦ ?_⟩
    exact False.elim (hp.ne_top (Subsingleton.elim p ⊤))
  · have hu : M ≤ IsUnit.submonoid k := by
      intro x hx
      exact isUnit_iff_ne_zero.mpr (fun e ↦ h (e ▸ hx))
    exact IsRegularRing.of_ringEquiv (IsLocalization.atUnits k M hu).toRingEquiv

/-- Every localization map is regular. Its fibre at a prime disjoint from the denominators
is the residue field as an algebra over that field; otherwise its fibre is the zero ring.
Source: Stacks Project, More on Algebra, proof of Lemma 07PT and Definition 07BZ
(blueprint: lem-weil-pbc-localization-regular).

Proof:
1. The localization map is flat by `lem-weil-pbc-localization-flat` (Algebra, 00HT).
2. For a prime p, base change identifies `p.Fiber T` with a localization of `p.ResidueField`
at the image of W, by `lem-weil-pbc-localization-base-change` (Algebra, 00DK).
The tensor swap identifies this with the tensor order in the node.
3. The kernel of S to its residue field at p is p: membership in the extended maximal
ideal gives an equation u(st-a) = 0 with u and t outside p and a in p; primality forces s in p.
4. If W misses p, all its images in the residue field are nonzero, hence units; localization
at units is an algebra isomorphism. If W meets p, its image contains zero, and localization
is the zero ring. These are `lem-weil-pbc-localization-units-or-zero` (Algebra, 00CQ, 00CP).
5. Both fibres are Noetherian. Base change to any finite purely inseparable extension of
`p.ResidueField` is that extension field or the zero ring. The field is regular by
`lem-weil-pbc-field-regular-ring`; the zero ring is regular because it has no prime ideals.
Thus each fibre is geometrically regular, as in `theorem-finite-etale-covers-proper-henselian--2`
(Algebra, 0382, 0381).
6. Flatness from step 1 and the fibres from step 5 give regularity by
`theorem-finite-etale-covers-proper-henselian--2` (More on Algebra, 07BZ). -/
theorem isRegular_and_fiber
    {S : Type u} {T : Type v} [CommRing S] [CommRing T] [Algebra S T]
    (W : Submonoid S) [IsLocalization W T] :
    RingHom.IsRegular (algebraMap S T) ∧
      ∀ (p : Ideal S) [p.IsPrime],
        ((∀ w : W, (w : S) ∉ p) → Nonempty (p.Fiber T ≃ₐ[p.ResidueField] p.ResidueField)) ∧
        ((∃ w : W, (w : S) ∈ p) → Subsingleton (p.Fiber T)) := by
  classical
  have hf (p : Ideal S) [p.IsPrime] :
      ((∀ w : W, (w : S) ∉ p) →
        Nonempty (p.Fiber T ≃ₐ[p.ResidueField] p.ResidueField)) ∧
      ((∃ w : W, (w : S) ∈ p) → Subsingleton (p.Fiber T)) := by
    let M := Algebra.algebraMapSubmonoid p.ResidueField W
    have : IsLocalization M (p.Fiber T) := IsLocalization.tensor T W
    constructor
    · intro h
      have hu : M ≤ IsUnit.submonoid p.ResidueField := by
        rintro x ⟨w, hw, rfl⟩
        exact isUnit_iff_ne_zero.mpr (fun e ↦ h ⟨w, hw⟩
          (Ideal.algebraMap_residueField_eq_zero.mp e))
      exact ⟨(IsLocalization.atUnits p.ResidueField M hu).symm⟩
    · rintro ⟨w, hw⟩
      apply (IsLocalization.subsingleton_iff (M := M) (S := p.Fiber T)).mpr
      exact ⟨w, w.prop, Ideal.algebraMap_residueField_eq_zero.mpr hw⟩
  refine ⟨?_, hf⟩
  rw [RingHom.IsRegular, toAlgebra_algebraMap]
  refine ⟨RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat T W), ?_⟩
  intro p hp
  let M := Algebra.algebraMapSubmonoid p.ResidueField W
  have : IsLocalization M (p.Fiber T) := IsLocalization.tensor T W
  have : IsRegularRing (p.Fiber T) := regular_of_field p.ResidueField (p.Fiber T) M
  refine ⟨inferInstance, ?_⟩
  intro k' _ _ _ _
  exact regular_of_field k' (TensorProduct p.ResidueField k' (p.Fiber T))
    (Algebra.algebraMapSubmonoid k' M)

end IsLocalization
