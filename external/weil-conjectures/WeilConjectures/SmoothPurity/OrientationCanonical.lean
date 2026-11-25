/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation
public import WeilConjectures.SmoothPurity.IntegralTateTwistExtendScalars
public import WeilConjectures.SmoothPurity.UpperShriekUnitDualizable

/-!
# Orientations of smooth morphisms with `ℚ̄_ℓ`-coefficients

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type which is smooth of pure
relative dimension `d`. An *orientation* of `f` is an isomorphism
`γ_f : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. This file provides:

- `ProEtale.CondensedRing.nonempty_iso_tateTwist_upperShriekUnit`: an orientation exists. It is
  the extension of scalars along `𝒪 ⟶ ℚ̄_ℓ`, `𝒪 = ℤ_ℓ` the integers of the smallest finite
  subextension `ℚ_ℓ` of `ℚ̄_ℓ`, of the non-canonical integral isomorphism
  `𝒪_X(d)[2d] ≅ Rf^! 𝒪_Y` (`ProEtale.CondensedRing.nonempty_iso_integralTateTwist_upperShriekUnit`).
- `ProEtale.CondensedRing.IsCanonicalSmoothOrientation`: the property of a morphism
  `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` of being the *canonical* orientation (blueprint
  `definition-trace-map`, `prose-09-24`): the extension of scalars of an integral morphism
  `φ₀ : 𝒪_X(d)[2d] ⟶ Rf^! 𝒪_Y` whose reductions modulo `ℓⁿ`, `n ≥ 1`, read on the small étale
  site, are the inverses of the canonical finite orientations `Rf^! Λ_Y ≅ Λ_X(d)[2d]`,
  `Λ = ℤ ⧸ ℓⁿ` (`Etale.dualizingComplexTwistShiftIso`, blueprint
  `proposition-relative-dualizing-complex--1`, built from the fundamental class of the diagonal).
- `ProEtale.CondensedRing.smoothOrientationOfSmooth`: the canonical orientation if there is one,
  and otherwise the non-canonical one; it is an isomorphism
  (`ProEtale.CondensedRing.isIso_smoothOrientationOfSmooth`).

## The canonical orientation

The canonical finite orientations are compatible with the reductions `ℤ ⧸ ℓⁿ⁺¹ ⟶ ℤ ⧸ ℓⁿ` (SGA 4,
Exposé XVIII; blueprint `proposition-compatibility-purity-change-coefficients`, formalised in the
étale setting up to the compatibilities of the constituents of the construction in
`Etale.SupportedCoefficientChange.map_dualizingComplexTwistShiftIso`). A compatible family of
morphisms of reductions into the derived complete complex `Rf^! 𝒪_Y` lifts uniquely to a
morphism `φ₀` (`ProEtale.existsUnique_derivedReduction_map_eq`), so the canonical orientation
exists and is unique, and `IsCanonicalSmoothOrientation` determines it. The existence of the
compatible lift is not formalised yet, which is why `smoothOrientationOfSmooth` falls back to a
non-canonical orientation when no morphism satisfying `IsCanonicalSmoothOrientation` is known to
exist; mathematically this case does not occur.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]

/-- The reduction modulo `ℓⁿ` of bounded constructible `𝒪_E`-complexes commutes with the shifts:
`red_n (K[m]) ≅ (red_n K)[m]`, read in the ambient derived categories, where the derived
extension of scalars commutes with the shifts. -/
noncomputable def boundedConstructibleIntegersModPowReductionShiftIso
    (K : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧) (m : ℤ) :
    (boundedConstructibleIntegersModPowReduction X ℓ E n).obj ((shiftFunctor _ m).obj K) ≅
      (shiftFunctor _ m).obj ((boundedConstructibleIntegersModPowReduction X ℓ E n).obj K) :=
  let ι := (boundedConstructible
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)).ι
  let ιn := (boundedConstructible (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).ι
  let Lred := (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).app _ ≪≫
      Lred.mapIso ((ι.commShiftIso m).app K) ≪≫ (Lred.commShiftIso m).app (ι.obj K) ≪≫
      (shiftFunctor _ m).mapIso
        ((boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).app K).symm ≪≫
      ((ιn.commShiftIso m).app _).symm)

end Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)

/-- The **extension of scalars** to `ℚ̄_ℓ` of a morphism `φ₀ : 𝒪_{E,X}(d)[2d] ⟶ Rf^! 𝒪_{E,Y}`:
the morphism `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` obtained by applying the extension of scalars `T`
along `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` and the comparisons `T(𝒪_{E,X}(d)[2d]) ≅ ℚ̄_ℓ,X(d)[2d]`
(`extendScalarsIntegralTateTwistBoundedConstructibleIso`) and `T(Rf^! 𝒪_{E,Y}) ≅ Rf^! ℚ̄_ℓ,Y`
(`integersToPadicAlgClUpperShriekUnitIso`). -/
noncomputable def extendScalarsIntegralOrientation
    (φ₀ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (extendScalarsIntegralTateTwistBoundedConstructibleIso ℓ E X d (2 * d)).inv ≫
    (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E).map φ₀ ≫
    (integersToPadicAlgClUpperShriekUnitIso ℓ E f).hom

/-- The extension of scalars of an isomorphism is an isomorphism. -/
instance isIso_extendScalarsIntegralOrientation
    (φ₀ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) [IsIso φ₀] :
    IsIso (extendScalarsIntegralOrientation ℓ E f d φ₀) := by
  rw [extendScalarsIntegralOrientation]
  infer_instance

/-- **The relative dualizing complex of a smooth morphism is a shifted Tate twist**, with
`ℚ̄_ℓ`-coefficients: `ℚ̄_ℓ,X(d)[2d] ≅ Rf^! ℚ̄_ℓ,Y` for `f` smooth of pure relative dimension `d`.
The isomorphism is the extension of scalars of the non-canonical integral isomorphism
`𝒪_X(d)[2d] ≅ Rf^! 𝒪_Y`, `𝒪 = ℤ_ℓ` (`nonempty_iso_integralTateTwist_upperShriekUnit`). -/
theorem nonempty_iso_tateTwist_upperShriekUnit [SmoothOfRelativeDimension d f.left] :
    Nonempty (boundedConstructibleTateTwist ℓ X d (2 * d) ≅
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  obtain ⟨e⟩ := nonempty_iso_integralTateTwist_upperShriekUnit (ℓ := ℓ) (E := E.1) f d
  exact ⟨asIso (extendScalarsIntegralOrientation ℓ E f d e.hom)⟩

/-- The **canonical finite orientation**, read on the small étale site: modulo `ℓⁿ`, the
reductions of the shifted integral Tate twist `𝒪_{E,X}(d)[2d]` and of the integral relative
dualizing complex `Rf^! 𝒪_{E,Y}` are identified, through the canonical comparisons
`etaleReductionIntegralTateTwistIso`, `etaleReductionUpperShriekIso` and `etaleReductionUnitIso`,
with `Λ_X(d)[2d]` and `Rf^! Λ_Y`, `Λ = 𝒪_E ⧸ ℓⁿ`, and the isomorphism is the inverse of the
orientation `Rf^! Λ_Y ≅ Λ_X(d)[2d]` of the diagonal argument (`Etale.dualizingComplexTwistShiftIso`,
for the Kummer classes of `μ_{ℓⁿ} ⊗ Λ`, blueprint `proposition-relative-dualizing-complex--1`). -/
noncomputable def etaleReductionSmoothOrientationIso (n : ℕ) [SmoothOfRelativeDimension d f.left] :
    (shiftFunctor _ (2 * d : ℤ)).obj ((finiteEtaleReading ℓ E.1 n X).obj
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
          (integralTateTwistBoundedConstructible ℓ E.1 X.hom d))) ≅
      (finiteEtaleReading ℓ E.1 n X).obj
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
          ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))) :=
  haveI := HasCompactification.of_over f
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 n) X.left :=
    HasInvertibleExponent.of_hom X.hom
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 n) Y.left :=
    HasInvertibleExponent.of_hom Y.hom
  (shiftFunctor _ (2 * d : ℤ)).mapIso
      (etaleReductionIntegralTateTwistIso ℓ E.1 n X d ≪≫ (λ_ _).symm) ≪≫
    (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 n) f.left d
      Y.hom).symm ≪≫
    ((etaleReductionUpperShriekIso ℓ E.1 n f).app (𝟙_ _) ≪≫
      (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E.1 n) f.left).mapIso
        (etaleReductionUnitIso ℓ E.1 n Y)).symm

/-- A morphism `φ₀ : 𝒪_{E,X}(d)[2d] ⟶ Rf^! 𝒪_{E,Y}` **lifts the canonical finite orientations**
if for every `n ≥ 1` its reduction modulo `ℓⁿ`, read on the small étale site, is the canonical
finite orientation `etaleReductionSmoothOrientationIso` (through the commutation of the
reduction and the étale reading with the shift). Such a lift is unique: a morphism into the
derived complete complex `Rf^! 𝒪_{E,Y}` is determined by its reductions
(`ProEtale.existsUnique_derivedReduction_map_eq`), which are determined by their étale readings,
the reading being fully faithful. -/
def IsIntegralSmoothOrientation [SmoothOfRelativeDimension d f.left]
    (φ₀ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) : Prop :=
  ∀ n : ℕ, (finiteEtaleReading ℓ E.1 (n + 1) X).map
      ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 (n + 1)).map φ₀) =
    (finiteEtaleReading ℓ E.1 (n + 1) X).map
        (boundedConstructibleIntegersModPowReductionShiftIso ℓ E.1 (n + 1) X.left _
          (2 * d : ℤ)).hom ≫
      ((finiteEtaleReading ℓ E.1 (n + 1) X).commShiftIso (2 * d : ℤ)).hom.app _ ≫
      (etaleReductionSmoothOrientationIso ℓ E f d (n + 1)).hom

/-- Blueprint `definition-trace-map`, `prose-09-24`: a morphism
`φ : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` is the **canonical orientation** of `f` (smooth of pure relative
dimension `d`) if it is the extension of scalars (`extendScalarsIntegralOrientation`) of a
morphism `φ₀ : 𝒪_X(d)[2d] ⟶ Rf^! 𝒪_Y`, `𝒪 = ℤ_ℓ` the integers of the smallest finite
subextension `ℚ_ℓ` of `ℚ̄_ℓ`, lifting the canonical finite orientations
(`IsIntegralSmoothOrientation`, built from `Etale.dualizingComplexTwistShiftIso`).

The canonical finite orientations are compatible with the reductions `ℤ ⧸ ℓⁿ⁺¹ ⟶ ℤ ⧸ ℓⁿ`
(SGA 4, Exposé XVIII; blueprint `proposition-compatibility-purity-change-coefficients`) and
therefore lift, uniquely, to `φ₀` (`ProEtale.existsUnique_derivedReduction_map_eq`); hence a
morphism with this property exists and is unique. Only uniqueness is used implicitly, the existence
of the lift is not formalised. -/
def IsCanonicalSmoothOrientation [SmoothOfRelativeDimension d f.left]
    (φ : boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) : Prop :=
  ∃ φ₀, IsIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀ ∧
    extendScalarsIntegralOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀ = φ

/-- The **orientation** `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` of a morphism `f` smooth of pure relative
dimension `d`: the canonical orientation (`IsCanonicalSmoothOrientation`) when an isomorphism with
this property is known to exist, and otherwise a non-canonical isomorphism
(`nonempty_iso_tateTwist_upperShriekUnit`). Mathematically the canonical orientation always
exists and is an isomorphism (SGA 4, Exposé XVIII); its existence is not formalised. -/
noncomputable def smoothOrientationOfSmooth [SmoothOfRelativeDimension d f.left] :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) := by
  classical
  exact if h : ∃ φ, IsIso φ ∧ IsCanonicalSmoothOrientation ℓ f d φ then h.choose
    else (Classical.choice (nonempty_iso_tateTwist_upperShriekUnit ℓ f d)).hom

/-- The orientation of a smooth morphism is an isomorphism. -/
instance isIso_smoothOrientationOfSmooth [SmoothOfRelativeDimension d f.left] :
    IsIso (smoothOrientationOfSmooth ℓ f d) := by
  classical
  rw [smoothOrientationOfSmooth]
  split_ifs with h
  · exact h.choose_spec.1
  · infer_instance

/-- If an isomorphism which is a canonical orientation exists, the orientation
`smoothOrientationOfSmooth` is canonical. -/
theorem isCanonicalSmoothOrientation_smoothOrientationOfSmooth
    [SmoothOfRelativeDimension d f.left]
    (h : ∃ φ, IsIso φ ∧ IsCanonicalSmoothOrientation ℓ f d φ) :
    IsCanonicalSmoothOrientation ℓ f d (smoothOrientationOfSmooth ℓ f d) := by
  classical
  rw [smoothOrientationOfSmooth, dite_eq_left h]
  exact h.choose_spec.2

end AlgebraicGeometry.ProEtale.CondensedRing
