/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.GeometricStalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-!
# Perfectness of geometric stalks on the pro-étale site

Let `Λ` be a finite local ring (for instance `A_{E,n}`). The geometric stalk of a pro-étale
complex `M ∈ D(Y_proét, Λ)` at a geometric point `ȳ : Spec Ω ⟶ Y` is computed through the site
comparison `ν : Y_proét ⟶ Y_ét`: it is the derived geometric stalk
`RΓ(Spec Ω, Lȳ^* Rν_* M)` of the étale complex `Rν_* M`. For `M = ν^* G` of étale origin and
bounded below, `Rν_* M ≅ G`, so this is the geometric stalk of the étale model `G`.

This file records the pro-étale clause of blueprint `lemma-perfect-complexes-geometric-point--6`:
for `M ∈ D^b_{ctf}(Y_proét, Λ)` the geometric stalk is quasi-isomorphic to a bounded complex of
finite free `Λ`-modules.

## Main definitions and statements

- `AlgebraicGeometry.ProEtale.geometricStalk`
- `AlgebraicGeometry.ProEtale.exists_free_geometricStalk`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The derived geometric stalk `M_ȳ = RΓ(Spec Ω, Lȳ^* Rν_* M) ∈ D(Λ)` of a pro-étale complex `M`
at a geometric point `ȳ : Spec Ω ⟶ Y`: the étale geometric stalk of `Rν_* M`. -/
noncomputable def geometricStalk (y : Spec (.of Ω) ⟶ Y) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (ModuleCat.{u + 1} Λ) :=
  R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ L(Etale.upperStar (ModuleCat.{u + 1} Λ) y) ⋙
    Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))

/-- On a bounded below complex of étale origin `ν^* G`, the pro-étale geometric stalk is the
étale geometric stalk of `G`. -/
noncomputable def geometricStalkComparisonIso (y : Spec (.of Ω) ⟶ Y)
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : _root_.DerivedCategory.TStructure.t.plus G) :
    (geometricStalk Λ y).obj (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj G) ≅
      (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).obj
        ((L(Etale.upperStar (ModuleCat.{u + 1} Λ) y)).obj G) :=
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) Y G hG
  (Etale.rightDerivedGlobalSections _ _).mapIso ((L(Etale.upperStar (ModuleCat.{u + 1} Λ) y)).mapIso
    (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app G)).symm)

/-- Blueprint `lemma-perfect-complexes-geometric-point--6`: Geometric-stalk perfectness at finite
and field coefficients (finite coefficients, on the pro-étale site).

Let `Λ` be a finite local ring (for instance `Λ = A_{E,n}`), `M ∈ D^b_{ctf}(Y_proét, Λ)` and
`ȳ : Spec Ω ⟶ Y` a geometric point. Then the geometric stalk `M_ȳ` is quasi-isomorphic to a
bounded complex of finite free `Λ`-modules. Indeed `M ≅ ν^* G` with `G` bounded constructible on
`Y_ét`; `G` has finite Tor amplitude since `ν^*` detects Tor amplitude
(`ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory_comparisonUpperStar`); and
`M_ȳ` is the étale geometric stalk of `G`, to which
`AlgebraicGeometry.Etale.exists_free_geometricStalk` applies. -/
theorem exists_free_geometricStalk [Finite Λ] [IsLocalRing Λ] (y : Spec (.of Ω) ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y M) :
    ∃ (P : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ), P.IsStrictlyGE a ∧
      P.IsStrictlyLE b ∧ (∀ i, Module.Free Λ (P.X i) ∧ Module.Finite Λ (P.X i)) ∧
      Nonempty ((geometricStalk Λ y).obj M ≅ _root_.DerivedCategory.Q.obj P) := by
  obtain ⟨hbc, a, b, hta⟩ := hM
  obtain ⟨G, hG, ⟨e⟩⟩ := (DerivedCategory.boundedConstructible_iff _ _ M).1 hbc
  have hGt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b G :=
    DerivedCategory.torAmplitudeIn_of_mapDerivedCategory_comparisonUpperStar Λ
      ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b).prop_of_iso e.symm hta)
  obtain ⟨P, a', b', h₁, h₂, hP, ⟨e'⟩⟩ :=
    Etale.exists_free_geometricStalk Λ y G ⟨hG, a, b, hGt⟩
  exact ⟨P, a', b', h₁, h₂, hP,
    ⟨(geometricStalk Λ y).mapIso e.symm ≪≫ geometricStalkComparisonIso Λ y G hG.1.1 ≪≫ e'⟩⟩

end AlgebraicGeometry.ProEtale
