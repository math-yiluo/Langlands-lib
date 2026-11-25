/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.EssFiniteType

/-!
# Essentially of finite type algebras over Artinian local rings

An algebra `S` over `R` which is an Artinian local ring is essentially of finite type as soon
as its residue field is (Stacks, Tag 07DT (3)).

## Main results

- `Algebra.EssFiniteType.of_isArtinianRing_of_residueField`
-/

@[expose] public section

open IsLocalRing

namespace Algebra.EssFiniteType

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Let `S` be an Artinian local `R`-algebra. If the residue field of `S` is essentially of
finite type over `R`, then so is `S` (Stacks, Tag 07DT (3)).
(blueprint: `theorem-finite-etale-covers-proper-henselian--2`) -/
theorem of_isArtinianRing_of_residueField [IsArtinianRing S] [IsLocalRing S]
    [EssFiniteType R (ResidueField S)] : EssFiniteType R S := by
  classical
  obtain ⟨σ, hσ⟩ := (essFiniteType_iff R (ResidueField S)).mp ‹_›
  choose lift hlift using residue_surjective (R := S)
  let A : Subalgebra R S := Algebra.adjoin R (σ.image lift : Set S)
  have hA : A.map (IsScalarTower.toAlgHom R S (ResidueField S)) = Algebra.adjoin R σ := by
    rw [AlgHom.map_adjoin]
    congr 1
    ext z
    simp [hlift]
  let M : Submonoid A := (IsUnit.submonoid S).comap (algebraMap A S)
  let L := Localization M
  let f : L →+* S := IsLocalization.lift (M := M) (g := algebraMap A S) fun m ↦ m.2
  let _ : Algebra L S := f.toAlgebra
  have hf (a : A) : f (algebraMap A L a) = a := IsLocalization.lift_eq _ _
  have : IsScalarTower R L S := .of_algebraMap_eq fun r ↦ by
    change _ = f (algebraMap R L r)
    rw [IsScalarTower.algebraMap_apply R A L, hf]
    rfl
  have hsurj : Function.Surjective (algebraMap L (ResidueField S)) := by
    intro z
    obtain ⟨t, ht, htu, hzt⟩ := hσ z
    rw [← hA] at ht hzt
    obtain ⟨a, ha, rfl⟩ := ht
    obtain ⟨b, hb, hzb⟩ := hzt
    have hau : IsUnit (a : S) := by
      rw [← residue_ne_zero_iff_isUnit]
      exact htu.ne_zero
    let m : M := ⟨⟨a, ha⟩, (IsUnit.mem_submonoid_iff _).mpr hau⟩
    refine ⟨IsLocalization.mk' L (⟨b, hb⟩ : A) m, ?_⟩
    have key : f (IsLocalization.mk' L (⟨b, hb⟩ : A) m) * a = b := by
      have := congrArg f (IsLocalization.mk'_spec L (⟨b, hb⟩ : A) m)
      rwa [map_mul, hf, hf] at this
    rw [IsScalarTower.algebraMap_apply L S]
    refine (htu.mul_left_inj).mp ?_
    rw [← hzb]
    conv_rhs => rw [← key]
    simp only [ResidueField.algebraMap_eq, map_mul]
    rfl
  have : Module.Finite L (S ⧸ Ring.jacobson S) := by
    rw [ringJacobson_eq_maximalIdeal]
    exact .of_surjective (Algebra.linearMap L (ResidueField S)) hsurj
  have : Module.Finite L S := IsSemiprimaryRing.finite_of_isArtinian L S S
  have : FiniteType R A := (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset _)
  have : EssFiniteType R L := inferInstance
  exact comp R L S

end Algebra.EssFiniteType
