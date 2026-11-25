/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Zero-dimensional local rings with separably closed residue field

Source: Stacks Project, Algebra, Tags 06RS, 00J9, 04GG and 04GF
(blueprint: lem-weil-pbc-dimension-zero-local-strictly-henselian).
-/

@[expose] public section

universe u v

/-- The extended maximal ideal is nil in every algebra over a dimension-zero local ring.
Apply Stacks Tag 00J9 (Mathlib's nil-kernel idempotent lifting theorem). -/
private theorem lift_idempotent_of_dimension_zero
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : ringKrullDim R = 0)
    (B : Type v) [CommRing B] [Algebra R B]
    (e : B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B))
    (he : IsIdempotentElem e) :
    ∃! b : B, IsIdempotentElem b ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) b = e := by
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  have hnil : (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ nilradical B := by
    rw [Ideal.map_le_iff_le_comap, ← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
    intro x hx
    exact (show IsNilpotent x from hx).map (algebraMap R B)
  apply existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)))
    (fun x hx ↦ hnil (by simpa using hx)) e _ he
  exact RingHom.mem_range.mpr (Ideal.Quotient.mk_surjective e)

/-- A zero-dimensional local ring with separably closed residue field is strictly henselian;
idempotents lift uniquely in every finite algebra modulo the extended maximal ideal.
Source: Stacks Project, Algebra, Tags 06RS and 00J9, Tag 04GG, and Definition Tag 04GF
(blueprint: lem-weil-pbc-dimension-zero-local-strictly-henselian).

The hypothesis that `m` is the only prime of `R` is `ringKrullDim R = 0`
(`def-weil-pbc-krull-dimension-ring`), equivalent for a local ring.

Proof: (1) The maximal ideal is the nilradical by dimension zero. Its image in any
`R`-algebra consists of nilpotents, so the ideal it generates is contained in the
nilradical of that algebra (`Ideal.map_le_iff_le_comap` and `IsNilpotent.map`).
(2) The quotient map has this nil ideal as its kernel. Mathlib's theorem
`existsUnique_isIdempotentElem_eq_of_ker_isNilpotent` (Stacks Tag 00J9) therefore gives
unique idempotent lifting, even without assuming the algebra finite. The argument also
covers the zero algebra.
(3) Apply `lem-weil-pbc-henselian-of-nil-maximal-ideal`: finite Newton iteration
lifts simple roots because every element of the maximal ideal is nilpotent.
(4) Combine henselianity with the separably closed residue-field hypothesis using
`isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed`. The idempotent
clause in the independent universe `v` is given by step (2). -/
theorem isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : ringKrullDim R = 0)
    [IsSepClosed (IsLocalRing.ResidueField R)] :
    IsStrictlyHenselianLocalRing R ∧
      ∀ (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B],
        ∀ e : B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B),
          IsIdempotentElem e →
            ∃! b : B, IsIdempotentElem b ∧
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) b = e := by
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  have hhens : HenselianLocalRing R :=
    henselianLocalRing_of_maximalIdeal_le_nilradical R
      (by rw [Ring.KrullDimLE.nilradical_eq_maximalIdeal])
  refine ⟨(isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed R).mpr
    ⟨hhens, inferInstance⟩, ?_⟩
  intro B _ _ _ e he
  exact lift_idempotent_of_dimension_zero R hdim B e he
