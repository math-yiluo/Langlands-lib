/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated

/-! # Triangulated closure for the ell-adic finiteness coefficients

Stated per coefficient ring (`𝒪̲_E`, `E̲`, `ℚ̲̄_ℓ`, unit ball `O̲`). The field cases use local
finite freeness. The integral cases use the integral Serre
criterion. These are exactly the heart-closure inputs in the last step of blueprint
`proposition-six-operations-dctf--14`.
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace CondensedRing

variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The bounded constructible module-object category over `𝒪̲_E` is triangulated: the integral
case of the ell-adic finiteness coefficients, by the integral constructible Serre theorem.
Applying homology to distinguished triangles gives triangulated closure.
Source: Bhatt--Scholze, Proposition 6.8.11(1),(3), and the heart-closure inputs in
`proposition-six-operations-dctf--14`, step 10.
(blueprint: lem-sfb-dc-ell-adic-triangulated) -/
theorem isTriangulated_boundedConstructible_ellAdic_padicIntegers (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)).IsTriangulated :=
  isTriangulated_boundedConstructible_padicIntegersRingObj X ℓ E

/-- The bounded constructible module-object category over `E̲`, `E` a finite normed extension of
`ℚ_ℓ`, is triangulated: field presentations become locally free, so the constructible heart is
Serre.
(blueprint: lem-sfb-dc-ell-adic-triangulated) -/
theorem isTriangulated_boundedConstructible_ellAdic_continuous (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)).IsTriangulated :=
  isTriangulated_boundedConstructible_continuousMapRingObj X ℓ E

/-- The bounded constructible module-object category over `ℚ̲̄_ℓ` is triangulated.
(blueprint: lem-sfb-dc-ell-adic-triangulated) -/
theorem isTriangulated_boundedConstructible_ellAdic_padicAlgCl :
    (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).IsTriangulated :=
  isTriangulated_boundedConstructible_padicAlgClRingObj X ℓ

/-- The bounded constructible module-object category over the closed unit ball `O̲` of a finite
normed extension `E` of `ℚ_ℓ` is triangulated, by the integral Serre criterion.
(blueprint: lem-sfb-dc-ell-adic-triangulated) -/
theorem isTriangulated_boundedConstructible_ellAdic_unitBall {E : Type} [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (O : Subring E)
    (hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1) :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} O) X)).IsTriangulated :=
  have : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1) := ⟨hO⟩
  isTriangulated_boundedConstructible_unitBallRingObj X ℓ O

end CondensedRing
end AlgebraicGeometry.ProEtale
