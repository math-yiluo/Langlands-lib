/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Essential finite type for Artinian local algebras

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 07DT (blueprint:
theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

namespace RingHom

/--
(blueprint: theorem-finite-etale-covers-proper-henselian--2)
Let `f : R →+* S` be a homomorphism of commutative rings. If `S` is Artinian and
local, and the induced map from `R` to its residue field is essentially of finite
type, then `f` is essentially of finite type. This is the converse direction of
Stacks Project, Lemma Tag 07DT, part (3); its proof uses the finite generation
statement for Artinian local algebras over their residue fields and composition
of essentially finite type maps.
-/
theorem essFiniteType_of_artinian_local_residue
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    [IsArtinianRing S] [IsLocalRing S]
    (h : (IsLocalRing.residue S).comp f |>.EssFiniteType) :
    f.EssFiniteType := by
  classical
  let := f.toAlgebra
  let K := IsLocalRing.ResidueField S
  let π : S →ₐ[R] K := ⟨IsLocalRing.residue S, fun _ ↦ rfl⟩
  have hK : Algebra.EssFiniteType R K := h
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff R K).mp hK
  let lift : K → S := Function.surjInv IsLocalRing.residue_surjective
  have hlift (x : K) : π (lift x) = x :=
    Function.surjInv_eq IsLocalRing.residue_surjective x
  let τ := σ.image lift
  let A := Algebra.adjoin R (τ : Set S)
  have hA : A.map π = Algebra.adjoin R (σ : Set K) := by
    change (Algebra.adjoin R (τ : Set S)).map π = _
    rw [← Algebra.adjoin_image]
    congr 1
    simp only [τ, Finset.coe_image, Set.image_image]
    simp only [hlift, Set.image_id']
  -- Localize precisely at the elements of A that are units in S.
  let M : Submonoid A := (IsUnit.submonoid S).comap A.val.toRingHom
  let C := Localization M
  let g : C →+* S := IsLocalization.lift (S := C) (g := A.val.toRingHom)
    (fun m : M ↦ m.property)
  let := g.toAlgebra
  have hg (a : A) : g (algebraMap A C a) = a := IsLocalization.lift_eq _ a
  have htower : IsScalarTower R C S :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      exact (hg ⟨f r, A.algebraMap_mem r⟩).symm)
  have hsurj : Function.Surjective ((IsLocalRing.residue S).comp g) := by
    intro x
    obtain ⟨t, ht, hunit, hxt⟩ := hσ x
    rw [← hA] at ht hxt
    obtain ⟨a, ha, hat⟩ := ht
    obtain ⟨b, hb, hbt⟩ := hxt
    have hat' : π a = t := hat
    have hbt' : π b = x * t := hbt
    have hau : IsUnit a := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit a).mp
      change π a ≠ 0
      rw [hat']
      exact hunit.ne_zero
    let m : M := ⟨⟨a, ha⟩, hau⟩
    refine ⟨IsLocalization.mk' C ⟨b, hb⟩ m, ?_⟩
    apply (hunit.mul_left_inj).mp
    change π (g (IsLocalization.mk' C ⟨b, hb⟩ m)) * t = x * t
    rw [← hat', ← map_mul]
    have he := congrArg g (IsLocalization.mk'_spec C ⟨b, hb⟩ m)
    rw [map_mul, hg, hg] at he
    exact (congrArg π he).trans (by simpa only [hat'] using hbt')
  -- Finiteness of the residue quotient lifts through the Artinian ring.
  have hfiniteK : Module.Finite C (S ⧸ Ring.jacobson S) := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact (RingHom.Finite.of_surjective _ hsurj)
  have hfinite : Module.Finite C S := IsSemiprimaryRing.finite_of_isArtinian C S S
  have hC : Algebra.EssFiniteType R C := by
    have : Algebra.FiniteType R A := Algebra.FiniteType.adjoin_of_finite τ.finite_toSet
    have : Algebra.EssFiniteType A C := Algebra.EssFiniteType.of_isLocalization C M
    exact Algebra.EssFiniteType.comp R A C
  exact Algebra.EssFiniteType.comp R C S

end RingHom
