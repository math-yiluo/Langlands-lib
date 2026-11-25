/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The explicit localized polynomial image

Source: Stacks Project, Tags 07FH and 07FI, transcendental case.
(blueprint: def-weil-pbc-popescu-localized-polynomial-image).
-/

@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra

variable {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
  [IsLocalRing B]

/-- Evaluate polynomials with coefficients in the given subalgebra. 
(blueprint: def-weil-pbc-popescu-localized-polynomial-image)
-/
def popescuPolynomialEval (A₀ : Subalgebra k B) (x : B) : Polynomial A₀ →ₐ[k] B :=
  Polynomial.aevalTower A₀.val x

/-- The prime at which polynomial evaluation is localized. 
(blueprint: def-weil-pbc-popescu-localized-polynomial-image)
-/
noncomputable def popescuPolynomialPrime (A₀ : Subalgebra k B) (x : B) : Ideal (Polynomial A₀) :=
  (IsLocalRing.maximalIdeal B).comap (popescuPolynomialEval A₀ x).toRingHom

instance (A₀ : Subalgebra k B) (x : B) : (popescuPolynomialPrime A₀ x).IsPrime :=
  Ideal.comap_isPrime _ _

/-- Evaluation extends to the localization because precisely the denominators have unit image. 
(blueprint: def-weil-pbc-popescu-localized-polynomial-image)
-/
noncomputable def popescuLocalizedPolynomialMap (A₀ : Subalgebra k B) (x : B) :
    Localization.AtPrime (popescuPolynomialPrime A₀ x) →ₐ[k] B :=
  IsLocalization.liftAlgHom (f := popescuPolynomialEval A₀ x)
    (M := (popescuPolynomialPrime A₀ x).primeCompl)
    (fun s ↦ IsLocalRing.notMem_maximalIdeal.mp s.property)

/-- The enlargement is a genuine image, with no choice of an existence witness.
Source: Stacks Project, Tag 07FI, transcendental case.
(blueprint: def-weil-pbc-popescu-localized-polynomial-image). -/
noncomputable def popescuLocalizedPolynomialImage (A₀ : Subalgebra k B) (x : B) :
    Subalgebra k B :=
  (popescuLocalizedPolynomialMap A₀ x).range

instance (A₀ : Subalgebra k B) (x : B) :
    IsLocalRing (popescuLocalizedPolynomialImage A₀ x) :=
  IsLocalRing.of_surjective' (popescuLocalizedPolynomialMap A₀ x).rangeRestrict.toRingHom
    (popescuLocalizedPolynomialMap A₀ x).rangeRestrict_surjective

/-- (blueprint: def-weil-pbc-popescu-localized-polynomial-image) -/
lemma popescuLocalizedPolynomialMap_algebraMap (A₀ : Subalgebra k B) (x : B)
    (f : Polynomial A₀) :
    popescuLocalizedPolynomialMap A₀ x
      (algebraMap (Polynomial A₀) _ f) = popescuPolynomialEval A₀ x f :=
  IsLocalization.lift_eq
    (M := (popescuPolynomialPrime A₀ x).primeCompl)
    (fun s ↦ IsLocalRing.notMem_maximalIdeal.mp s.property) f

/-- (blueprint: def-weil-pbc-popescu-localized-polynomial-image) -/
lemma le_popescuLocalizedPolynomialImage (A₀ : Subalgebra k B) (x : B) :
    A₀ ≤ popescuLocalizedPolynomialImage A₀ x := by
  intro a ha
  refine ⟨algebraMap (Polynomial A₀) _ (Polynomial.C ⟨a, ha⟩), ?_⟩
  simp [popescuLocalizedPolynomialMap_algebraMap, popescuPolynomialEval]

/-- (blueprint: def-weil-pbc-popescu-localized-polynomial-image) -/
lemma mem_popescuLocalizedPolynomialImage (A₀ : Subalgebra k B) (x : B) :
    x ∈ popescuLocalizedPolynomialImage A₀ x := by
  refine ⟨algebraMap (Polynomial A₀) _ Polynomial.X, ?_⟩
  simp [popescuLocalizedPolynomialMap_algebraMap, popescuPolynomialEval]

/-- (blueprint: def-weil-pbc-popescu-localized-polynomial-image) -/
lemma essFiniteType_popescuLocalizedPolynomialImage (A₀ : Subalgebra k B) (x : B)
    [EssFiniteType k A₀] : EssFiniteType k (popescuLocalizedPolynomialImage A₀ x) := by
  let D := Localization.AtPrime (popescuPolynomialPrime A₀ x)
  have : EssFiniteType k (Polynomial A₀) := EssFiniteType.comp k A₀ (Polynomial A₀)
  have : EssFiniteType (Polynomial A₀) D :=
    EssFiniteType.of_isLocalization D (popescuPolynomialPrime A₀ x).primeCompl
  have : EssFiniteType k D := EssFiniteType.comp k (Polynomial A₀) D
  exact EssFiniteType.of_surjective (popescuLocalizedPolynomialMap A₀ x).rangeRestrict
    (popescuLocalizedPolynomialMap A₀ x).rangeRestrict_surjective

end Algebra
