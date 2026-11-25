/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.LocalRing
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport

/-!
# Perfectness of geometric stalks

Let `x̄ : Spec Ω ⟶ X` be a geometric point (`Ω` separably closed). The derived geometric stalk
of `K ∈ D(X_ét, Λ)` is `K_x̄ = RΓ(Spec Ω, Lx̄^* K) ∈ D(Λ)`. This file records
`lemma-perfect-complexes-geometric-point--6`:

* for a finite local coefficient ring `Λ` (such as `A_{E,n}`) and `K ∈ D^b_{ctf}(X, Λ)`, the
  stalk `K_x̄` is quasi-isomorphic to a bounded complex of finite free `Λ`-modules;
* for a field `Λ` and `K` bounded constructible, `K_x̄` is a perfect complex of `Λ`-vector spaces
  (bounded with finite-dimensional cohomology).

## Main statements

- `AlgebraicGeometry.Etale.exists_free_geometricStalk`
- `AlgebraicGeometry.Etale.isPerfect_geometricStalk_of_field`
- `AlgebraicGeometry.Etale.isPerfect_geometricStalk_padicAlgCl`

## Implementation notes

The blueprint states the finite-coefficient assertion on the pro-étale coefficient site and on
the small étale site; only the étale site is treated here. The `ℚ̄_ℓ` case is stated for the
étale model `ULift ℚ̄_ℓ` of `ℚ̄_ℓ`-coefficients used in
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek_padicAlgCl`, as a special
case of the field case.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Blueprint `lemma-perfect-complexes-geometric-point--6`: Geometric-stalk perfectness at finite
and field coefficients (finite coefficients).

Let `Λ` be a finite local ring (for instance `Λ = A_{E,n}`), `K ∈ D^b_{ctf}(X, Λ)` and
`x̄ : Spec Ω ⟶ X` a geometric point. Then the derived geometric stalk
`K_x̄ = RΓ(Spec Ω, Lx̄^* K)` is quasi-isomorphic to a bounded complex of finite free
`Λ`-modules: it is perfect (`AlgebraicGeometry.Etale.isPerfect_geometricStalk`), and finite
projective modules over a local ring are free. -/
theorem exists_free_geometricStalk (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [IsLocalRing Λ]
    (x : Spec (.of Ω) ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ∃ (P : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ), P.IsStrictlyGE a ∧
      P.IsStrictlyLE b ∧ (∀ i, Module.Free Λ (P.X i) ∧ Module.Finite Λ (P.X i)) ∧
      Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).obj
        ((L((x)^*[ModuleCat.{u + 1} Λ])).obj K) ≅ _root_.DerivedCategory.Q.obj P) :=
  (isPerfect_geometricStalk Λ x K hK).exists_free

/-- Blueprint `lemma-perfect-complexes-geometric-point--6`: Geometric-stalk perfectness at finite
and field coefficients (field coefficients).

Let `Λ` be a field (a field coefficient stage `E`, or `ℚ̄_ℓ`), `K` a bounded constructible
complex of étale sheaves of `Λ`-vector spaces on `X` and `x̄ : Spec Ω ⟶ X` a geometric point.
Then the derived geometric stalk `K_x̄ = RΓ(Spec Ω, Lx̄^* K)` is bounded with finite-dimensional
cohomology, hence a perfect complex of `Λ`-vector spaces. No Tor amplitude condition is needed
over a field. -/
theorem isPerfect_geometricStalk_of_field (Λ : Type (u + 1)) [Field Λ]
    (x : Spec (.of Ω) ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).obj
      ((L((x)^*[ModuleCat.{u + 1} Λ])).obj K)).IsPerfect := by
  obtain ⟨hb, hc⟩ := boundedConstructible_leftDerivedUpperStar _ x hK
  obtain ⟨c, d, hc', hd'⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded
    _).2 hb
  obtain ⟨h₁, h₂⟩ := homologyConcentratedIn_rightDerivedGlobalSections_of_isSepClosed _ ⟨hc', hd'⟩
  exact (_root_.DerivedCategory.isPerfect_iff _).2 ⟨⟨c, d, h₁, h₂⟩, fun n ↦
    moduleFinite_homology_rightDerivedGlobalSections_of_isSepClosed _ n
      (Scheme.IsConstructibleSheaf.isFiniteSheaf (hc n))⟩

/-- Blueprint `lemma-perfect-complexes-geometric-point--6`: Geometric-stalk perfectness at finite
and field coefficients (`ℚ̄_ℓ`-coefficients).

The case `Λ = ℚ̄_ℓ` of `AlgebraicGeometry.Etale.isPerfect_geometricStalk_of_field`, for the étale
model `ULift ℚ̄_ℓ` of the common-stage `ℚ̄_ℓ`-coefficients. -/
theorem isPerfect_geometricStalk_padicAlgCl (l : ℕ) [Fact l.Prime] (x : Spec (.of Ω) ⟶ X)
    (K : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)))))
    (hK : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))) X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)))
      (Spec (.of Ω))).obj
        ((L((x)^*[ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))])).obj K)).IsPerfect :=
  isPerfect_geometricStalk_of_field _ x K hK

end AlgebraicGeometry.Etale
