/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.Algebra.Algebra.Rat

/-! # Lifting a characteristic-zero residue field
Source: Stacks Project, Algebra, Theorem 032A(1), first proof paragraph. -/

@[expose] public section

universe u
namespace IsLocalRing

/-- The residue map of a complete local ring in residue characteristic zero has a section.
Source: Stacks Project, Algebra, Theorem 032A(1), first proof paragraph.
(blueprint: theorem-finite-etale-covers-proper-henselian--2)

Proof: Every nonzero integer is a unit in R, since its residue is nonzero, so R and
all its adic quotients are Q-algebras. The residue field is formally smooth over Q.
Start with the identity map into R/m. Inductively lift a section into R/m^n through
R/m^(n+1): the kernel is square-zero because 2n >= n+1 for n >= 1. The lift reduces
to the preceding section, hence still reduces to the identity on the residue field.
The compatible family defines a ring map into the adic completion. Compose it with
the inverse of the canonical completion isomorphism to obtain f. Its first component
is the identity, which is the stated equality. -/
theorem exists_residue_section (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharP (ResidueField R) 0] :
    ∃ f : ResidueField R →+* R, (residue R).comp f = RingHom.id _ := by
  let : CharZero (ResidueField R) := CharP.charP_to_charZero (ResidueField R)
  have hunits : ∀ z : nonZeroDivisors ℤ, IsUnit (Int.castRingHom R z) := by
    intro z
    apply (residue_ne_zero_iff_isUnit (R := R) _).mp
    change (residue R) ((z : ℤ) : R) ≠ 0
    rw [map_intCast]
    exact_mod_cast (mem_nonZeroDivisors_iff_ne_zero.mp z.property)
  let : Algebra ℚ R :=
    (IsLocalization.lift (S := ℚ) (g := Int.castRingHom R) hunits).toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ (ResidueField R)
  have : Algebra.IsAlgebraic
      (IntermediateField.adjoin ℚ (Set.range ((↑) : s → ResidueField R)))
      (ResidueField R) := hs.isAlgebraic_field
  have : Algebra.FormallySmooth ℚ (ResidueField R) :=
    Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  let g : ResidueField R →ₐ[ℚ] R ⧸ maximalIdeal R :=
    { RingHom.id (ResidueField R) with
      commutes' := fun q ↦ RingHom.congr_fun
        (Subsingleton.elim
          ((RingHom.id (ResidueField R)).comp (algebraMap ℚ (ResidueField R)))
          (algebraMap ℚ (R ⧸ maximalIdeal R))) q }
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (S := R) (I := maximalIdeal R) g
  exact ⟨f.toRingHom, congrArg AlgHom.toRingHom hf⟩

end IsLocalRing
