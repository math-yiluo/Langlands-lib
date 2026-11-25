/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# A finite coefficient model for a polynomial residue field extension

Source: Stacks Project, More on Algebra, Tag 07PU, first paragraph.
-/

@[expose] public section

universe u

namespace Polynomial

/-- The image of `X` generates the residue field over the fraction field and is algebraic.
The fraction presentation of the polynomial quotient proves that the intermediate field
it generates contains every element of the residue field. -/
private theorem residue_finite_over_fraction_field
    (A : Type u) [CommRing A] [IsDomain A]
    (r : Ideal (Polynomial A)) [r.IsPrime] (hr : r ≠ ⊥)
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K r.ResidueField] [IsScalarTower A K r.ResidueField] :
    Module.Finite K r.ResidueField := by
  classical
  let x : r.ResidueField := algebraMap (Polynomial A) r.ResidueField X
  have heval : aeval x = IsScalarTower.toAlgHom A (Polynomial A) r.ResidueField := by
    ext
    simp [x]
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hr
  have hxA : IsAlgebraic A x := ⟨f, hf0, by
    rw [heval]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hf⟩
  have hx : IsAlgebraic K x := hxA.extendScalars (IsFractionRing.injective A K)
  let F := IntermediateField.adjoin K ({x} : Set r.ResidueField)
  have hF : Module.Finite K F := IntermediateField.finiteDimensional_adjoin
    (by simpa using hx.isIntegral)
  have hp : ∀ p : Polynomial A, algebraMap (Polynomial A) r.ResidueField p ∈ F := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa using F.add_mem hp hq
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply F.mul_mem
      · change algebraMap A r.ResidueField a ∈ F
        rw [IsScalarTower.algebraMap_apply A K r.ResidueField]
        exact F.algebraMap_mem _
      · have hxF : x ∈ F := IntermediateField.subset_adjoin K {x} (by simp)
        exact pow_mem hxF n
  have hs : Function.Surjective F.val := by
    intro z
    obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective (Polynomial A ⧸ r) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨⟨z, ?_⟩, rfl⟩
    rw [← hz]
    exact F.div_mem (hp a) (hp b)
  exact Module.Finite.of_surjective F.val.toLinearMap hs

/-- Adjoin an integral basis, then clear denominators in the basis coordinates.
This is the finite-model construction of Stacks Tag 07PU; the denominator calculation
also occurs in `MvPolynomial.exists_finite_subalgebra_fraction_field`. -/
private theorem finite_subalgebra_with_fraction_field
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L] :
    ∃ B : Subalgebra A L, Module.Finite A B ∧ IsFractionRing B L := by
  classical
  obtain ⟨t, e, he⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let B := Algebra.adjoin A (Set.range e)
  have hB : Module.Finite A B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range e)
      (by rintro _ ⟨i, rfl⟩; exact he i)
  refine ⟨B, hB, IsFractionRing.of_field B L (fun z ↦ ?_)⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors A) (fun i ↦ e.repr z i)
  choose a ha using hd
  have hd0 : (d : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hdm : algebraMap A L d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K L]
    exact (map_ne_zero_iff (algebraMap K L) (RingHom.injective _)).mpr
      ((map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr hd0)
  have hdz : (d : A) • z ∈ B := by
    rw [← e.sum_repr z, Finset.smul_sum]
    apply B.sum_mem
    intro i _
    rw [← smul_assoc, ← ha i, algebraMap_smul]
    exact B.smul_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (a i)
  refine ⟨(⟨(d : A) • z, hdz⟩ : B),
    (⟨algebraMap A L d, B.algebraMap_mem d⟩ : B), ?_⟩
  change z = ((d : A) • z) / algebraMap A L d
  rw [Algebra.smul_def, mul_div_cancel_left₀ _ hdm]

/-- A finite extension of a nonzero polynomial residue field above zero has a finite
coefficient model inside the extension field. Its evaluation prime has that extension
as residue field, compatibly with the original polynomial map.
Source: Stacks Project, More on Algebra, Tag 07PU, first paragraph.
(blueprint: lem-weil-pbc-polynomial-residue-finite-coefficient-model)

Proof:
Let K be the fraction field of A. Localization at the nonzero elements of A carries
r to a nonzero prime of K[X]. A nonzero prime of the PID K[X] is maximal, and its
quotient is finite over K, by reducing powers of X modulo a monic generator.
Localization preserves the residue field, so kappa(r), and then L, is finite over K.
Scale a finite K-basis of L by a common nonzero element of A so all basis elements
are integral over A. Let B be their A-subalgebra in L. Finite integral generation
makes B finite over A. Clearing denominators of the coordinates of each element of
L expresses it as a quotient of elements of B, so L is a fraction field of B.
Evaluate B[X] in L with X equal to the image of X under A[X] to kappa(r) to L.
Let s be the kernel. It is prime since L is a field and contracts to zero in B
since B is a subalgebra of L. A nonzero polynomial in r stays nonzero under the
injective coefficient map A[X] to B[X] and lies in s, so s is nonzero.
The quotient B[X]/s embeds in L and contains B. Since L is the fraction field of
B, it is also the fraction field of this quotient: every element is a quotient
of elements of B. Uniqueness of fraction fields identifies kappa(s) with L.
This identification is a B-algebra equivalence and agrees with evaluation on
B[X], hence on the mapped polynomials from A[X]. Transporting the fraction-field
structure along this equivalence proves the last required structure. -/
theorem exists_finite_coefficient_model
    (A : Type u) [CommRing A] [IsDomain A]
    (r : Ideal (Polynomial A)) [r.IsPrime] (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥)
    (L : Type u) [Field L] [Algebra r.ResidueField L] [Module.Finite r.ResidueField L] :
    letI : Algebra A L :=
      ((algebraMap r.ResidueField L).comp
        ((algebraMap (Polynomial A) r.ResidueField).comp Polynomial.C)).toAlgebra
    ∃ B : Subalgebra A L, Module.Finite A B ∧
      ∃ (s : Ideal (Polynomial B)) (hs : s.IsPrime),
        letI := hs
        s ≠ ⊥ ∧ s.comap (Polynomial.C : B →+* Polynomial B) = ⊥ ∧
          IsFractionRing B s.ResidueField ∧
          ∃ e : s.ResidueField ≃ₐ[B] L,
            ∀ f : Polynomial A,
              e (algebraMap (Polynomial B) s.ResidueField
                (Polynomial.map (algebraMap A B) f)) =
                algebraMap r.ResidueField L (algebraMap (Polynomial A) r.ResidueField f) := by
  classical
  let : Algebra A L :=
    ((algebraMap r.ResidueField L).comp
      ((algebraMap (Polynomial A) r.ResidueField).comp Polynomial.C)).toAlgebra
  -- The zero contraction gives the embedding needed to lift the fraction field.
  have hinj : Function.Injective (algebraMap A r.ResidueField) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    change (RingHom.ker (algebraMap (Polynomial A) r.ResidueField)).comap C = ⊥
    rw [Ideal.ker_algebraMap_residueField, hrA]
  let : FaithfulSMul A r.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective A r.ResidueField).mpr hinj
  let : IsScalarTower A r.ResidueField L := .of_algebraMap_eq' rfl
  let K := FractionRing A
  let : Algebra K r.ResidueField := FractionRing.liftAlgebra A r.ResidueField
  let : IsScalarTower A K r.ResidueField := FractionRing.isScalarTower_liftAlgebra ..
  let : Algebra K L := ((algebraMap r.ResidueField L).comp
    (algebraMap K r.ResidueField)).toAlgebra
  let : IsScalarTower K r.ResidueField L := .of_algebraMap_eq' rfl
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A r.ResidueField L,
      IsScalarTower.algebraMap_apply K r.ResidueField L,
      ← IsScalarTower.algebraMap_apply A K r.ResidueField]
  let : Module.Finite K r.ResidueField := residue_finite_over_fraction_field A r hr K
  let : Module.Finite K L := Module.Finite.trans r.ResidueField L
  -- Construct the coefficient model from an integral basis of the finite extension.
  obtain ⟨B, hB, hFrac⟩ := finite_subalgebra_with_fraction_field A K L
  let : IsFractionRing B L := hFrac
  let x : L := algebraMap r.ResidueField L (algebraMap (Polynomial A) r.ResidueField X)
  let g : Polynomial B →ₐ[B] L := aeval x
  let s := RingHom.ker g
  have hs : s.IsPrime := RingHom.ker_isPrime g.toRingHom
  let : s.IsPrime := hs
  have heval : ∀ f : Polynomial A,
      g (f.map (algebraMap A B)) =
        algebraMap r.ResidueField L (algebraMap (Polynomial A) r.ResidueField f) := by
    have h : (g.restrictScalars A).comp (mapAlgHom (Algebra.ofId A B)) =
        (IsScalarTower.toAlgHom A r.ResidueField L).comp
          (IsScalarTower.toAlgHom A (Polynomial A) r.ResidueField) := by
      ext
      simp [g, x]
    intro f
    exact congrArg (fun h : Polynomial A →ₐ[A] L ↦ h f) h
  have hs0 : s ≠ ⊥ := by
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hr
    have hfB : f.map (algebraMap A B) ≠ 0 := by
      have hAB : Function.Injective (algebraMap A B) := Function.Injective.of_comp
        (show Function.Injective (fun a ↦ (algebraMap A B a : L)) from
          (RingHom.injective (algebraMap r.ResidueField L)).comp hinj)
      simpa only [Polynomial.map_zero] using (Polynomial.map_injective _ hAB).ne hf0
    intro hzero
    apply hfB
    have hmem : f.map (algebraMap A B) ∈ s := by
      change g (f.map (algebraMap A B)) = 0
      rw [heval, Ideal.algebraMap_residueField_eq_zero.mpr hf, map_zero]
    simpa [hzero] using hmem
  have hsB : s.comap (C : B →+* Polynomial B) = ⊥ := by
    ext b
    change g (C b) = 0 ↔ b = 0
    simp [g]
  have hu : s.primeCompl ≤ (IsUnit.submonoid L).comap g.toRingHom := by
    intro f hf
    change IsUnit (g f)
    exact isUnit_iff_ne_zero.mpr hf
  -- Evaluation lifts to the residue field; fractions of constants give surjectivity.
  let φ : s.ResidueField →ₐ[B] L := Ideal.ResidueField.liftₐ s g le_rfl hu
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective B z
    refine ⟨algebraMap B s.ResidueField a / algebraMap B s.ResidueField b, ?_⟩
    simpa using hz
  let e : s.ResidueField ≃ₐ[B] L := AlgEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have hFrac' : IsFractionRing B s.ResidueField := IsFractionRing.of_algEquiv e.symm
  refine ⟨B, hB, s, hs, hs0, hsB, hFrac', e, ?_⟩
  intro f
  change φ (algebraMap (Polynomial B) s.ResidueField (f.map (algebraMap A B))) = _
  rw [Ideal.ResidueField.liftₐ_algebraMap]
  exact heval f

end Polynomial
