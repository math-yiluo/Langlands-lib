/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingGenericBaseOpen

/-!

# Existence of the dualizing maps of nearby cycles over generic bases

The dualizing maps `θ_N` of the trait models over generic bases
(`NearbyCyclesModel.IsTraitModelOfGenericBase.dualizingMap`) form a family
`NearbyCyclesModel.NearbyDualizingDataOfGenericBase`
(`NearbyCyclesModel.nonempty_nearbyDualizingDataOfGenericBase`, blueprint
`prose-E-15`).

The dualizing maps are built from the trait as a model of the point `Spec F` along
`ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`, while the trace property is asked for every `ε₀'` compatible with
the identification `ε`. Both agree as soon as the base `X₁` is nonempty: then so is the geometric
generic fibre, which is all of `X₁ ×_F Spec Ω`, and its structure morphism to `Spec Ω` is an
epimorphism (`AlgebraicGeometry.epi_of_nonempty_of_field`). If `X₁` is empty, both sides of the
trace property are morphisms out of a zero object
(`IsTraitModelOfGenericBase.pushforwardExchange_app_comp_map_dualizingMap_comp_trace_of_comp_eq`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

/-- A morphism from a nonempty scheme to the spectrum of a field is an epimorphism: it is flat
(`AlgebraicGeometry.Flat.of_field`) and surjective. -/
lemma epi_of_nonempty_of_field {Z : Scheme.{u}} [Nonempty Z] {K : Type u} [Field K]
    (f : Z ⟶ Spec (.of K)) : Epi f := by
  have := Flat.of_field K f
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Surjective f := ⟨fun _ ↦ ⟨Classical.arbitrary Z, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective f

namespace ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

namespace IsTraitModelOfGenericBase

variable (ℓ : ℕ) [Fact ℓ.Prime] {F : Type u} [Field F] [Fact (ringChar F).Prime]
  [Fact (ringChar F ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {Y : Over (Spec (.of F))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The trace property of the dualizing maps over a generic base**, for every
`ε₀ : Spec Ω ⟶ Spec F` compatible with `ε`: `tr_{Y'} ∘ Ra'_*(θ_N) ∘ χ_a(ω_Y) = σ⁻¹ ∘ Ψ_S(tr_Y)`
for `q` proper and geometric generic fibre all of `Y ×_F Spec Ω`. If `Y` is nonempty, so is the
geometric generic fibre, whose structure morphism to `Spec Ω` is then an epimorphism, so that
`ε₀ = (Spec Ω ⟶ η ⟶ Spec F)` and this is
`IsTraitModelOfGenericBase.pushforwardExchange_app_comp_map_dualizingMap_comp_trace`;
if `Y` is empty, `Ra_* ω_Y` vanishes and both sides are morphisms out of a zero object. -/
theorem pushforwardExchange_app_comp_map_dualizingMap_comp_trace_of_comp_eq
    [IsProper (CondensedRing.toPoint Y).left] [IsProper (CondensedRing.toPoint Y').left]
    (h : N.IsTraitModelOfGenericBase Y ι q g) [IsProper q]
    (hgen : IsPullback N.ε g Y.hom (traitGenericPointToSpec k' ≫ ι))
    (ε₀ : Spec (.of (traitGenericField k')) ⟶ Spec (.of F)) (hε₀ : g ≫ ε₀ = N.ε ≫ Y.hom) :
    (h.pushforwardExchange ℓ ε₀ hε₀).app (dualizingComplex ℓ Y) ≫
        (boundedConstructibleLowerStar ℓ (CondensedRing.toPoint Y')).map (h.dualizingMap ℓ) ≫
          trace ℓ Y' =
      (traitPointSpecialization ε₀ ℓ).map (trace ℓ Y) ≫
        inv (traitPointSpecializationUnit ε₀ ℓ) := by
  by_cases hY : Nonempty Y.left
  · have : Surjective N.ε := by
      have : Subsingleton (Spec (.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
      have : Surjective (traitGenericPointToSpec k' ≫ ι) :=
        ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
      exact MorphismProperty.of_isPullback hgen.flip this
    have : Nonempty N.generic := ⟨(N.ε.surjective (Classical.arbitrary Y.left)).choose⟩
    have := epi_of_nonempty_of_field g
    obtain rfl : ε₀ = traitGenericPointToSpec k' ≫ ι := by
      rw [← cancel_epi g, hε₀, hgen.w]
    cast_proofs h.pushforwardExchange_app_comp_map_dualizingMap_comp_trace ℓ hgen
  · have : IsEmpty Y.left := not_nonempty_iff.mp hY
    have hS : IsZero ((traitPointSpecialization ε₀ ℓ).obj
        ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint Y)).obj
          (dualizingComplex ℓ Y))) := by
      refine IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _ ?_
      exact L(((traitModelOfPoint ε₀).i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_isZero
        (R(((traitModelOfPoint ε₀).j)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map_isZero
          (L(((traitModelOfPoint ε₀).ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_isZero
            (R(((CondensedRing.toPoint Y).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map_isZero
              (isZero_derivedCategory_of_isEmpty' _ _))))
    exact hS.eq_of_src _ _

end IsTraitModelOfGenericBase

variable (k' : Type u) [Field k'] (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Existence of the dualizing maps of nearby cycles over generic bases** (blueprint
`prose-E-15`): the dualizing map `θ_Y = β_{a_Y}(A)` of blueprint
`prose-E-15` (5) for separated models of finite type over the trait, the
exceptional adjoint of the compact-support exchange `ν_{a_Y}` (built from a relative
compactification over the trait), with its characterising properties: for proper models,
`ν_a = χ_a⁻¹` gives the trace property (`prose-E-15`), and the composition law
`sec-Base-change-for-nearby-cycles` (4) for an open immersion followed by the structure morphism
gives open restriction. This is the generic-base version of
`NearbyCyclesModel.nonempty_nearbyDualizingData` (the case of a base field). -/
theorem nonempty_nearbyDualizingDataOfGenericBase :
    Nonempty (NearbyDualizingDataOfGenericBase k' ℓ) :=
  ⟨{ θ := fun h ↦ h.dualizingMap ℓ
     pushforwardExchange_comp_map_θ_comp_trace := fun h _ hgen ε₀ hε₀ ↦
       h.pushforwardExchange_app_comp_map_dualizingMap_comp_trace_of_comp_eq ℓ hgen ε₀ hε₀
     map_θ_comp_dualizingComplexUpperStarIso := fun hM hN j _ j' _ φ _ hφ hq hg ↦
       IsTraitModelOfGenericBase.map_dualizingMap_comp_dualizingComplexUpperStarIso ℓ hM hN j j'
         φ hφ hq hg }⟩

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
