/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.SpecializationCriterion
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteEtaleAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Explicit preservation for the exceptional inverse image

This file records the preservation statements for the exceptional inverse image `Rf^!` in the
cases where it is explicit:

- `AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_leftDerivedUpperStar`
  (`proposition-six-operations-dctf--1`): the pullback preserves bounded constructibility and the
  Tor amplitude interval;
- `AlgebraicGeometry.Etale.preservation_rightDerivedUpperShriek_of_isOpenImmersion` and
  `AlgebraicGeometry.Etale.preservation_rightDerivedUpperShriek_of_isFinite_of_etale`
  (`theorem-f-shriek-finite-coefficients`): for an open immersion or a finite étale `f`,
  `Rf^! ≅ f^*` preserves the constructible intervals and the Tor amplitude, and commutes with the
  reduction of coefficients `K ↦ K ⊗ᴸ (Λ/J)`;
- `AlgebraicGeometry.Etale.preservation_rightDerivedUpperShriek_of_smoothOfRelativeDimension`
  (`theorem-f-shriek-finite-coefficients`): for `f` smooth of pure relative dimension `d`, `Rf^!`
  shifts the constructible interval and the Tor amplitude by `-2d`.

The reduction of coefficients along `Λ → B = Λ/J` is `AlgebraicGeometry.Etale.reductionModIdeal`,
`K ↦ K ⊗ᴸ (Λ/J)_X`, read in `D(X_ét, Λ)` (for `Λ = A_{E,n}` and `J = ϖ^m` this is the finite
reduction `K ↦ K_m` of the adic formalism).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### The pullback -/

/-- Blueprint `proposition-six-operations-dctf--1`: Pullback preserves finite Tor amplitude.

Let `f : X ⟶ Y` be a morphism of schemes and `K` a bounded constructible complex on `Y_ét` with
Tor amplitude in `[a, b]`. Then `Lf^* K` is bounded constructible, with homology concentrated in
`[a, b]` if `K` is, and has Tor amplitude in `[a, b]`; consequently `Lf^*` carries `Dctf(Y, Λ)`
into `Dctf(X, Λ)` (`AlgebraicGeometry.Etale.constructibleFiniteTor_leftDerivedUpperStar`). The
pullback of a bounded flat model is a bounded flat model in the same degrees. -/
theorem boundedConstructible_and_torAmplitudeIn_leftDerivedUpperStar {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a b : ℤ) {K : DerivedCategoryModule Λ Y}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) Y K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ∧
      (_root_.DerivedCategory.homologyConcentratedIn a b K →
        _root_.DerivedCategory.homologyConcentratedIn a b
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  ⟨boundedConstructible_leftDerivedUpperStar _ f hK, fun h ↦
    homologyConcentratedIn_of_iso _ ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app K).symm
      (((f)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj h),
    torAmplitudeIn_leftDerivedUpperStar _ f a b hKt⟩

/-! ### Open immersions and finite étale morphisms -/

variable [Finite Λ]

/-- If the exceptional inverse image along `f` is the pullback, it preserves the constructible
intervals and the Tor amplitude, and it commutes with the reduction of coefficients; on
`Dctf` both sides of the comparison are bounded constructible. -/
theorem preservation_of_iso_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : DerivedCategoryModule Λ Y ⥤ DerivedCategoryModule Λ X)
    (e : F ≅ L((f)^*[ModuleCat.{u + 1} Λ])) (J : Ideal Λ) :
    (∀ (a b : ℤ) (K : DerivedCategoryModule Λ Y),
      boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
        _root_.DerivedCategory.homologyConcentratedIn a b K →
          boundedConstructible (ModuleCat.{u + 1} Λ) X (F.obj K) ∧
            _root_.DerivedCategory.homologyConcentratedIn a b (F.obj K)) ∧
    (∀ (a b : ℤ) (K : DerivedCategoryModule Λ Y),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b (F.obj K)) ∧
    (∀ K : DerivedCategoryModule Λ Y,
      Nonempty ((reductionModIdeal Λ X J).obj (F.obj K) ≅
        F.obj ((reductionModIdeal Λ Y J).obj K))) ∧
    (∀ K : DerivedCategoryModule Λ Y, constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
      boundedConstructible (ModuleCat.{u + 1} Λ) X ((reductionModIdeal Λ X J).obj (F.obj K)) ∧
        boundedConstructible (ModuleCat.{u + 1} Λ) X
          (F.obj ((reductionModIdeal Λ Y J).obj K))) := by
  have : IsNoetherianRing Λ := inferInstance
  have hred (Z : Scheme.{u}) {N : DerivedCategoryModule Λ Z}
      (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z N) :
      boundedConstructible (ModuleCat.{u + 1} Λ) Z ((reductionModIdeal Λ Z J).obj N) := by
    obtain ⟨hNb, hNt⟩ := hN
    obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) Z
    have : Module.Finite Λ (ModuleCat.of Λ (Λ ⧸ J)) :=
      inferInstanceAs (Module.Finite Λ (Λ ⧸ J))
    have := Scheme.isConstructibleSheaf_constantSheaf (X := Z) (ModuleCat.of Λ (Λ ⧸ J))
    exact (boundedConstructible _ Z).prop_of_iso ((β.app _).app N)
      (boundedConstructible_tensor Λ Z (boundedConstructible_singleFunctor_obj _ 0) hNb hNt)
  have hF (K : DerivedCategoryModule Λ Y) (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (F.obj K) := by
    obtain ⟨hb, c, d, hcd⟩ := constructibleFiniteTor_leftDerivedUpperStar _ f hK
    exact ⟨(boundedConstructible _ X).prop_of_iso (e.app K).symm hb, c, d,
      (torAmplitudeIn _ X c d).prop_of_iso (e.app K).symm hcd⟩
  refine ⟨fun a b K hK hab ↦ ?_, fun a b K hKt ↦ ?_, fun K ↦ ?_, fun K hK ↦ ?_⟩
  · refine ⟨(boundedConstructible _ X).prop_of_iso (e.app K).symm
      (boundedConstructible_leftDerivedUpperStar _ f hK), ?_⟩
    exact homologyConcentratedIn_of_iso _
      (((leftDerivedUpperStarIsoMapDerivedCategory _ f).app K).symm ≪≫ (e.app K).symm)
      (((f)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hab)
  · exact (torAmplitudeIn _ X a b).prop_of_iso (e.app K).symm
      (torAmplitudeIn_leftDerivedUpperStar _ f a b hKt)
  · exact ⟨(reductionModIdeal Λ X J).mapIso (e.app K) ≪≫
      ((leftDerivedUpperStarReductionModIdealIso Λ J f).app K).symm ≪≫ (e.app _).symm⟩
  · exact ⟨hred X (hF K hK), (boundedConstructible _ X).prop_of_iso
      ((reductionModIdeal Λ X J).mapIso (e.app K) ≪≫
        ((leftDerivedUpperStarReductionModIdealIso Λ J f).app K).symm ≪≫ (e.app _).symm)
      (hred X (hF K hK))⟩

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Preservation in the open and finite etale
cases.

Open immersion case. Let `f : U ⟶ Y` be a quasi-compact open immersion and `Λ` a finite ring. The
exceptional inverse image `Rf^! ≅ f^*` satisfies `Rf^! D_c^[a, b](Y, Λ) ⊆ D_c^[a, b](U, Λ)` and
preserves Tor amplitude in `[a, b]`; for every quotient `B = Λ/J` the coefficient comparison
`(Rf^! K) ⊗ᴸ B ≅ Rf^!(K ⊗ᴸ B)` is an isomorphism, and for `K ∈ Dctf(Y, Λ)` both sides are bounded
constructible. No bound depends on `Λ`. -/
theorem preservation_rightDerivedUpperShriek_of_isOpenImmersion {U Y : Scheme.{u}} (f : U ⟶ Y)
    [IsOpenImmersion f] [HasCompactification f] [QuasiCompact f] (J : Ideal Λ) :
    (∀ (a b : ℤ) (K : DerivedCategoryModule Λ Y),
      boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
        _root_.DerivedCategory.homologyConcentratedIn a b K →
          boundedConstructible (ModuleCat.{u + 1} Λ) U ((R(f)^![Λ]).obj K) ∧
            _root_.DerivedCategory.homologyConcentratedIn a b
              ((R(f)^![Λ]).obj K)) ∧
    (∀ (a b : ℤ) (K : DerivedCategoryModule Λ Y),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b ((R(f)^![Λ]).obj K)) ∧
    (∀ K : DerivedCategoryModule Λ Y,
      Nonempty ((reductionModIdeal Λ U J).obj ((R(f)^![Λ]).obj K) ≅
        (R(f)^![Λ]).obj ((reductionModIdeal Λ Y J).obj K))) ∧
    (∀ K : DerivedCategoryModule Λ Y, constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
      boundedConstructible (ModuleCat.{u + 1} Λ) U
          ((reductionModIdeal Λ U J).obj ((R(f)^![Λ]).obj K)) ∧
        boundedConstructible (ModuleCat.{u + 1} Λ) U
          ((R(f)^![Λ]).obj ((reductionModIdeal Λ Y J).obj K))) :=
  preservation_of_iso_leftDerivedUpperStar Λ f _
    (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ f ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory _ f).symm) J

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Preservation in the open and finite etale
cases.

Finite étale case. Let `f : V ⟶ X` be finite étale and `Λ` a finite ring. The exceptional
inverse image `Rf^! ≅ f^*` (`lemma-affine-space-etale-localization--4`) satisfies
`Rf^! D_c^[a, b](X, Λ) ⊆ D_c^[a, b](V, Λ)` and preserves Tor amplitude in `[a, b]`; for every
quotient `B = Λ/J` the coefficient comparison `(Rf^! K) ⊗ᴸ B ≅ Rf^!(K ⊗ᴸ B)` is an isomorphism,
and for `K ∈ Dctf(X, Λ)` both sides are bounded constructible. No bound depends on `Λ`. -/
theorem preservation_rightDerivedUpperShriek_of_isFinite_of_etale {V X : Scheme.{u}}
    (f : V ⟶ X) [IsFinite f] [_root_.AlgebraicGeometry.Etale f] [HasCompactification f]
    (J : Ideal Λ) :
    (∀ (a b : ℤ) (K : DerivedCategoryModule Λ X),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        _root_.DerivedCategory.homologyConcentratedIn a b K →
          boundedConstructible (ModuleCat.{u + 1} Λ) V ((R(f)^![Λ]).obj K) ∧
            _root_.DerivedCategory.homologyConcentratedIn a b
              ((R(f)^![Λ]).obj K)) ∧
    (∀ (a b : ℤ) (K : DerivedCategoryModule Λ X),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) V a b ((R(f)^![Λ]).obj K)) ∧
    (∀ K : DerivedCategoryModule Λ X,
      Nonempty ((reductionModIdeal Λ V J).obj ((R(f)^![Λ]).obj K) ≅
        (R(f)^![Λ]).obj ((reductionModIdeal Λ X J).obj K))) ∧
    (∀ K : DerivedCategoryModule Λ X, constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      boundedConstructible (ModuleCat.{u + 1} Λ) V
          ((reductionModIdeal Λ V J).obj ((R(f)^![Λ]).obj K)) ∧
        boundedConstructible (ModuleCat.{u + 1} Λ) V
          ((R(f)^![Λ]).obj ((reductionModIdeal Λ X J).obj K))) :=
  preservation_of_iso_leftDerivedUpperStar Λ f _
    (rightDerivedUpperShriekIsoOfIsFiniteOfEtale _ f ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory _ f).symm) J

/-! ### Smooth morphisms -/

/-- For `f` smooth of pure relative dimension `d`, `Rf^! K ≅ (Lf^* K ⊗ᴸ L[0])⟦2d⟧` for a flat
constructible locally constant sheaf `L` of free rank-one modules
(`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`). -/
lemma exists_flat_rightDerivedUpperShriek_iso_tensor_shift {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf L ∧
      ObjectProperty.flat L ∧ ∀ K : DerivedCategoryModule Λ Y,
        Nonempty ((R(f)^![Λ]).obj K ≅
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj L))⟦(2 * d : ℤ)⟧) := by
  have : HasInvertibleExponent Λ X := .of_hom f
  obtain ⟨L, _, hLs, ⟨eω⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ f d
  obtain ⟨hLc, hLf⟩ := isConstructibleSheaf_and_flat_of_sheafFiber_iso Λ L hLs
  refine ⟨L, hLc, hLf, fun K ↦ ?_⟩
  obtain ⟨t⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex Λ f d K
  exact ⟨t.symm ≪≫ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj _).mapIso eω ≪≫
    ((((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj _).commShiftIso (2 * d : ℤ)).app _)⟩

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Smooth morphisms satisfy the preservation
clauses.

Let `f : X ⟶ Y` be smooth of pure relative dimension `d`, admitting a compactification, and `Λ`
a finite ring whose exponent is invertible on `Y`. Then `f` satisfies the two preservation
clauses of exceptional-adjoint admissibility with `c_f^- = c_f^+ = -2d`:

1. constructibility: if `L ∈ D_c^[a, b](Y, Λ)` then `Rf^! L ∈ D_c^[a - 2d, b - 2d](X, Λ)`;
2. finite Tor amplitude: if `K` has Tor amplitude in `[a, b]`, then `Rf^! K` has Tor amplitude in
   `[a - 2d, b - 2d]`; in particular `Rf^!` carries `Dctf(Y, Λ)` into `Dctf(X, Λ)`.

By purity `Rf^! K ≅ Lf^* K ⊗ᴸ ω_f` with `ω_f ≅ L[2d]` for a locally constant sheaf `L` of free
rank-one `Λ`-modules (`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`); tensoring
with the flat constructible `L` changes neither the constructible interval nor the Tor amplitude,
and the shift moves both by `-2d`. -/
theorem preservation_rightDerivedUpperShriek_of_smoothOfRelativeDimension {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    (∀ (a b : ℤ) (K : DerivedCategoryModule Λ Y),
      boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
        _root_.DerivedCategory.homologyConcentratedIn a b K →
          boundedConstructible (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj K) ∧
            _root_.DerivedCategory.homologyConcentratedIn (a - 2 * d) (b - 2 * d)
              ((R(f)^![Λ]).obj K)) ∧
    (∀ (a b : ℤ) (K : DerivedCategoryModule Λ Y),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * d) (b - 2 * d)
          ((R(f)^![Λ]).obj K)) ∧
    (∀ K : DerivedCategoryModule Λ Y, constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj K)) := by
  have : IsNoetherianRing Λ := inferInstance
  obtain ⟨L, hLc, hLf, e⟩ := exists_flat_rightDerivedUpperShriek_iso_tensor_shift Λ f d
  have hL₀ := torAmplitudeIn_singleFunctor_zero_of_flat _ L hLf
  have hbc (K : DerivedCategoryModule Λ Y)
      (hK : boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
      boundedConstructible (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj K) :=
    (boundedConstructible _ X).prop_of_iso (e K).some.symm ((boundedConstructible _ X).le_shift _ _
      (boundedConstructible_tensor Λ X (boundedConstructible_leftDerivedUpperStar _ f hK)
        (boundedConstructible_singleFunctor_obj L 0) ⟨0, 0, hL₀⟩))
  have hta (a b : ℤ) (K : DerivedCategoryModule Λ Y)
      (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * d) (b - 2 * d)
        ((R(f)^![Λ]).obj K) := by
    have h : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) := by
      simpa using torAmplitudeIn_tensor _ X a b 0 0
        (torAmplitudeIn_leftDerivedUpperStar _ f a b hKt) hL₀
    exact (torAmplitudeIn _ X _ _).prop_of_iso (e K).some.symm (torAmplitudeIn_shift _ h (2 * d))
  refine ⟨fun a b K hK hab ↦ ⟨hbc K hK, ?_⟩, hta, fun K hK ↦ ?_⟩
  · have hab' : _root_.DerivedCategory.homologyConcentratedIn a b
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
      homologyConcentratedIn_of_iso _
        ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app K).symm
        (((f)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hab)
    have h₁ : _root_.DerivedCategory.homologyConcentratedIn a b
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) := by
      have h :=
        _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right hab' hL₀
      rw [add_zero, add_zero] at h
      exact h
    obtain ⟨g, l⟩ := h₁
    exact homologyConcentratedIn_of_iso _ (e K).some.symm
      ⟨_root_.DerivedCategory.TStructure.t.isGE_shift _ a (2 * d) (a - 2 * d),
        _root_.DerivedCategory.TStructure.t.isLE_shift _ b (2 * d) (b - 2 * d)⟩
  · obtain ⟨hK, a, b, hKt⟩ := hK
    exact ⟨hbc K hK, _, _, hta a b K hKt⟩

end Etale

end AlgebraicGeometry
