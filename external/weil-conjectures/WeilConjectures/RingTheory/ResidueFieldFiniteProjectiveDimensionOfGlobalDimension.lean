/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.RingTheory.GlobalDimension
import WeilConjectures.RingTheory.ProjectiveResolutionExtCharacterization
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-! Finite global dimension gives finite projective dimension for the residue field.

Source: Stacks Project, Algebra, Proposition 00OC, implication (2) ⇒ (1).
(blueprint: lem-weil-pbc-residue-field-finite-projective-dimension)
-/

@[expose] public section

universe u v

namespace Ring

/-- The residue field of a ring of finite global dimension has finite projective dimension.
Source: Stacks Project, Algebra, Proposition Tag 00OC, implication (2) ⇒ (1).
(blueprint: lem-weil-pbc-residue-field-finite-projective-dimension). -/
theorem residueField_hasFiniteProjectiveDimension (R : Type u) [CommRing R]
    [IsLocalRing R] (h : Ring.HasFiniteGlobalDimension.{u, max u v} R) :
    ModuleCat.HasFiniteProjectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
  obtain ⟨n, hn⟩ := h
  let K := ModuleCat.of R (IsLocalRing.ResidueField R)
  let L := ModuleCat.of R (ULift.{v} (IsLocalRing.ResidueField R))
  have : CategoryTheory.HasProjectiveDimensionLE L n := hn L
  exact ⟨n, ModuleCat.hasProjectiveDimensionLE_of_linearEquiv.{max u v, u}
    (M := L) (N := K) (ULift.moduleEquiv : L ≃ₗ[R] K) n⟩

end Ring
