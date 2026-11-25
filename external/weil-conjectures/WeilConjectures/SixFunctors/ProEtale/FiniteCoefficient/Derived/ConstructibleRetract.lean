/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin

/-!
# `Dᵇc(X, Λ)` is stable under retracts

For a finite coefficient ring `Λ`, the bounded constructible pro-étale complexes of étale origin
are stable under retracts (`ProEtale.DerivedCategory.boundedConstructible_of_retract`):
a retract of an object of étale origin is bounded below of étale origin, hence `D(ν^*)` of a
retract of a bounded constructible étale complex, `D(ν^*)` being fully faithful on bounded below
complexes.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **`Dᵇc(X, Λ)` is stable under retracts**, for a finite coefficient ring `Λ`: a retract of an
object of étale origin is bounded below of étale origin, hence `D(ν^*)` of a retract of a bounded
constructible étale complex, `D(ν^*)` being fully faithful on bounded below complexes. -/
lemma DerivedCategory.boundedConstructible_of_retract {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} {K K' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ))} (r : Retract K K')
    (hK' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K') :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).prop_of_retract
    r hK'.plusEtaleOrigin
  obtain ⟨K₀', hK₀', ⟨e'⟩⟩ := hK'
  obtain ⟨i, hi⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map K₀ K₀'
    hK₀'.1.1).2 (e.hom ≫ r.i ≫ e'.inv)
  obtain ⟨p, hp⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map K₀' K₀ hK₀).2
    (e'.hom ≫ r.r ≫ e.inv)
  have hip : i ≫ p = 𝟙 K₀ := (bijective_comparisonUpperStar_mapDerivedCategory_map K₀ K₀
    hK₀).1 (by
      simp only [Functor.map_comp, CategoryTheory.Functor.map_id, hi, hp, Category.assoc,
        Iso.inv_hom_id_assoc, r.retract_assoc, e.hom_inv_id])
  exact ⟨K₀, (Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).prop_of_retract
    ⟨i, p, hip⟩ hK₀', ⟨e⟩⟩

end AlgebraicGeometry.ProEtale
