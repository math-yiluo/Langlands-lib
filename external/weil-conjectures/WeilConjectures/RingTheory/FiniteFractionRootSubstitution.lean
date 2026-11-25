/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Rooting a finite family of fractions by polynomial substitution

Source: Stacks Project, Algebra, Tag 032O, coefficient-root construction.
(blueprint: lem-weil-pbc-finite-fraction-root-substitution)
-/

@[expose] public section
set_option autoImplicit false
universe u

private theorem polynomial_root_of_coefficient_roots
    (R A : Type u) [CommRing R] [CommRing A]
    (p n : ℕ) [Fact p.Prime] [CharP A p] (f : R →+* A) (P : Polynomial R)
    (hc : ∀ c ∈ P.coeffs, ∃ z : A, z ^ (p ^ n) = f c) :
    ∃ Q : Polynomial A,
      Q ^ (p ^ n) = Polynomial.eval₂RingHom (Polynomial.C.comp f)
        (Polynomial.X ^ (p ^ n)) P := by
  classical
  have hmem : P.map f ∈ (Polynomial.mapRingHom (iterateFrobenius A p n)).range := by
    apply (Polynomial.mem_map_range _).mpr
    intro j
    rw [Polynomial.coeff_map]
    by_cases hj : P.coeff j = 0
    · refine ⟨0, ?_⟩
      simp [hj]
    · obtain ⟨z, hz⟩ := hc _ (Polynomial.coeff_mem_coeffs hj)
      exact ⟨z, hz⟩
  obtain ⟨Q, hQ⟩ := hmem
  refine ⟨Q, ?_⟩
  rw [← Polynomial.map_iterateFrobenius_expand p Q n, Polynomial.map_expand]
  change Q.map (iterateFrobenius A p n) = P.map f at hQ
  rw [hQ]
  change (P.map f).eval₂ Polynomial.C (Polynomial.X ^ (p ^ n)) = _
  rw [Polynomial.eval₂_map]
  rfl

/-- Finitely many rational functions acquire prescribed p-power roots after a finite
coefficient extension and the substitution X ↦ T^(p^n).

Source: Stacks Project, Algebra, Tag 032O, the coefficient-root construction in the
second assertion, with the omitted finite-coefficient argument expanded.
(blueprint: lem-weil-pbc-finite-fraction-root-substitution)

Proof. Put K = Frac(R). Write each fraction as a quotient of polynomials over R.
In an algebraic closure of K adjoin the p^n-th roots of the finite union of their
nonzero coefficients. Each root is integral over K because its positive p^n-th
power is in K; the finite algebraic-generators theorem makes the generated subfield
E finite over K. Give E the R-algebra structure induced through K. Each chosen root
is also integral over R, since its p^n-th power is the image of a coefficient in R.
Thus the roots already belong to A = integralClosure R E. The coefficient map R → A
is injective. Polynomial expansion by the positive integer p^n is injective, so
mapping coefficients and substituting X ↦ T^(p^n) gives an injective map R[X] → A[T].
Extend its composite with A[T] → Frac(A[T]) to fractions by IsFractionRing.lift.
For each numerator and denominator, Polynomial.mem_map_range lifts its coefficient
image along iterated Frobenius on A. If Q is the lifted polynomial, the identity
map_iterateFrobenius_expand shows Q^(p^n) equals the substituted original polynomial.
The quotient of the lifted polynomials therefore has p^n-th power equal to the image
of the original fraction, by compatibility of ring homomorphisms with powers and
division. All subfields and fraction fields stay in Type u. This construction also
handles n=0, empty families and zero numerators; no nonzero numerator is assumed. -/
theorem exists_finite_fraction_root_substitution
    (R : Type u) [CommRing R] [IsDomain R]
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing (Polynomial R)) p]
    (n m : ℕ) (a : Fin m → FractionRing (Polynomial R)) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra (FractionRing R) E) (_ : Algebra R E)
      (_ : IsScalarTower R (FractionRing R) E) (_ : FiniteDimensional (FractionRing R) E),
      ∃ h : FractionRing (Polynomial R) →+* FractionRing (Polynomial (integralClosure R E)),
        (∀ b : Polynomial R,
          h (algebraMap (Polynomial R) (FractionRing (Polynomial R)) b) =
            algebraMap (Polynomial (integralClosure R E))
              (FractionRing (Polynomial (integralClosure R E)))
              (Polynomial.eval₂RingHom
                (Polynomial.C.comp (algebraMap R (integralClosure R E)))
                (Polynomial.X ^ (p ^ n)) b)) ∧
        ∀ i, ∃ z : FractionRing (Polynomial (integralClosure R E)), z ^ (p ^ n) = h (a i) := by
  classical
  let K := FractionRing R
  let F := FractionRing (Polynomial R)
  let Ω := AlgebraicClosure K
  let c : R →+* F := (algebraMap (Polynomial R) F).comp Polynomial.C
  have hc : Function.Injective c :=
    (IsFractionRing.injective (Polynomial R) F).comp Polynomial.C_injective
  have : CharP R p := c.charP hc p
  have : CharP K p := inferInstance
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap K Ω).injective p
  have hq : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos _
  choose P D _ ha using fun i ↦ IsFractionRing.div_surjective (Polynomial R) (a i)
  let S : Finset R := Finset.univ.biUnion fun i ↦ (P i).coeffs ∪ (D i).coeffs
  choose rt hrt using fun r : R ↦
    IsAlgClosed.exists_pow_nat_eq (algebraMap R Ω r) hq
  let U : Finset Ω := S.image rt
  let E := IntermediateField.adjoin K (U : Set Ω)
  have hfin : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin <| by
    intro x hx
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx
    apply IsIntegral.of_pow hq
    rw [hrt]
    exact isIntegral_algebraMap
  let : Algebra R E := ((algebraMap K E).comp (algebraMap R K)).toAlgebra
  have ht : IsScalarTower R K E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R E Ω := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R Ω r = algebraMap E Ω (algebraMap K E (algebraMap R K r))
    rw [← IsScalarTower.algebraMap_apply K E Ω,
      ← IsScalarTower.algebraMap_apply R K Ω]
  let A := integralClosure R E
  have : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
  have : CharP A p := (algebraMap A E).charP Subtype.val_injective p
  have hr (r : R) (hr : r ∈ S) : ∃ z : A, z ^ (p ^ n) = algebraMap R A r := by
    let z : E := ⟨rt r, IntermediateField.subset_adjoin K _
      (Finset.mem_image_of_mem rt hr)⟩
    have hz : z ^ (p ^ n) = algebraMap R E r := by
      apply (algebraMap E Ω).injective
      simpa [z, ← IsScalarTower.algebraMap_apply R E Ω] using hrt r
    have hi : IsIntegral R z := IsIntegral.of_pow hq (hz ▸ isIntegral_algebraMap)
    exact ⟨⟨z, hi⟩, Subtype.ext hz⟩
  have injRA : Function.Injective (algebraMap R A) := by
    intro x y hxy
    apply IsFractionRing.injective R K
    apply (algebraMap K E).injective
    exact congrArg (fun x : A ↦ (x : E)) hxy
  let j : Polynomial R →+* Polynomial A :=
    Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R A))
      (Polynomial.X ^ (p ^ n))
  have hj (B : Polynomial R) : j B = Polynomial.expand A (p ^ n)
      (B.map (algebraMap R A)) := by
    change B.eval₂ _ _ = (B.map _).eval₂ _ _
    rw [Polynomial.eval₂_map]
  have hij : Function.Injective j := by
    intro B C heq
    apply Polynomial.map_injective (algebraMap R A) injRA
    exact Polynomial.expand_injective hq (by simpa only [hj] using heq)
  let g : Polynomial R →+* FractionRing (Polynomial A) :=
    (algebraMap (Polynomial A) (FractionRing (Polynomial A))).comp j
  have hg : Function.Injective g :=
    (IsFractionRing.injective (Polynomial A) (FractionRing (Polynomial A))).comp hij
  let h : F →+* FractionRing (Polynomial A) := IsFractionRing.lift hg
  have hpoly (B : Polynomial R) : h (algebraMap (Polynomial R) F B) =
      algebraMap (Polynomial A) (FractionRing (Polynomial A)) (j B) :=
    IsFractionRing.lift_algebraMap hg B
  refine ⟨E, inferInstance, inferInstance, inferInstance, ht, hfin, h, hpoly, ?_⟩
  intro i
  have hP : ∀ r ∈ (P i).coeffs, ∃ z : A, z ^ (p ^ n) = algebraMap R A r := by
    intro r hri
    apply hr
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_union_left _ hri⟩
  have hD' : ∀ r ∈ (D i).coeffs, ∃ z : A, z ^ (p ^ n) = algebraMap R A r := by
    intro r hri
    apply hr
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_union_right _ hri⟩
  obtain ⟨Q, hQ⟩ := polynomial_root_of_coefficient_roots R A p n (algebraMap R A) (P i) hP
  obtain ⟨B, hB⟩ := polynomial_root_of_coefficient_roots R A p n (algebraMap R A) (D i) hD'
  refine ⟨algebraMap (Polynomial A) (FractionRing (Polynomial A)) Q /
    algebraMap (Polynomial A) (FractionRing (Polynomial A)) B, ?_⟩
  rw [div_pow, ← map_pow, ← map_pow, hQ, hB, ← ha i, map_div₀, hpoly, hpoly]
