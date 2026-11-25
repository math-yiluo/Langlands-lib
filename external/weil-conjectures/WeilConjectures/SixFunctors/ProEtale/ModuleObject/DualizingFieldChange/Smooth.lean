/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Iso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedUpperShriekFieldExtension
public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.TateTwist.Pullback
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Differentials

/-!

# Base change of dualizing complexes along field extensions, embedded case

Let `L/F` be a field extension, `X` a proper `F`-scheme with base change `X' = X ×_F L` and
`φ : π^* ω_X ⟶ ω_{X'}` the comparison of the dualizing complexes
(`ProEtale.CondensedRing.dualizingComplexBaseChange`). If `X` admits a closed immersion
`i : X ⟶ P` into an `F`-scheme `P` smooth of pure relative dimension `d` (for instance a
projective space, `AlgebraicGeometry.ProjectiveSpace.smoothOfRelativeDimension`), then `φ` is an
isomorphism
(`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_isClosedImmersion_of_tateTwistIso`),
given the pullback of the Tate twists `π_P^* ℚ̄_ℓ(d)[2d] ≅ ℚ̄_ℓ(d)[2d]`.

By `ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_iso` it suffices to find some
isomorphism `π^* ω_X ≅ ω_{X'}`. It is the composite
```
π^* ω_X ≅ π^* Ri^! ω_P ≅ π^* Ri^! ℚ̄_ℓ(d)[2d] ≅ Ri'^! π_P^* ℚ̄_ℓ(d)[2d] ≅ Ri'^! ℚ̄_ℓ(d)[2d]
  ≅ Ri'^! ω_{P'} ≅ ω_{X'}
```
of the composition isomorphisms of the exceptional inverse images
(`ProEtale.CondensedRing.upperShriekDualizingComplexIso`), smooth purity on `P` and on `P'`
(`ProEtale.CondensedRing.isIso_smoothPurityMap`, an input of the smooth purity section), the
commutation of `Ri^!` with the field extension
(`ProEtale.CondensedRing.nonempty_iso_upperShriek_closedImmersion_of_fieldExtension`) and the
pullback of the Tate twists.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ ℓ)]
  {X P : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {X' P' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {i : X ⟶ P} {i' : X' ⟶ P'} [IsClosedImmersion i.left] [IsClosedImmersion i'.left]
  {πP : P'.left ⟶ P.left} {π : X'.left ⟶ X.left}

/-- **The dualizing complexes of an embedded scheme and of its base change are isomorphic**: for a
closed immersion `i : X ⟶ P` into an `F`-scheme smooth of pure relative dimension `d`, its base
change `i' : X' ⟶ P'` along a field extension `L/F`, and an isomorphism of the pulled back Tate
twist `π_P^* ℚ̄_ℓ(d)[2d] ≅ ℚ̄_ℓ(d)[2d]`, there is an isomorphism `π^* ω_X ≅ ω_{X'}`. -/
theorem nonempty_iso_dualizingComplex_of_isClosedImmersion (d : ℕ)
    [SmoothOfRelativeDimension d (toPoint P).left] [SmoothOfRelativeDimension d (toPoint P').left]
    (hP : IsPullback πP P'.hom P.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sq : IsPullback π i'.left i.left πP)
    (eT : (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP).obj
        (boundedConstructibleTateTwist ℓ P d (2 * d)) ≅
      boundedConstructibleTateTwist ℓ P' d (2 * d)) :
    Nonempty ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π).obj
        (dualizingComplex ℓ X) ≅ dualizingComplex ℓ X') := by
  obtain ⟨β⟩ := nonempty_iso_upperShriek_closedImmersion_of_fieldExtension ℓ hP sq
    (boundedConstructibleTateTwist ℓ P d (2 * d))
  have ωP : boundedConstructibleTateTwist ℓ P d (2 * d) ≅ dualizingComplex ℓ P :=
    asIso (smoothPurityMap ℓ (toPoint P) d)
  have ωP' : boundedConstructibleTateTwist ℓ P' d (2 * d) ≅ dualizingComplex ℓ P' :=
    asIso (smoothPurityMap ℓ (toPoint P') d)
  exact ⟨(boundedConstructibleUpperStarOfMap ℓ π).mapIso
      ((upperShriekDualizingComplexIso ℓ i).symm ≪≫
        (boundedConstructibleUpperShriek ℓ i).mapIso ωP.symm) ≪≫ β ≪≫
    (boundedConstructibleUpperShriek ℓ i').mapIso (eT ≪≫ ωP') ≪≫
    upperShriekDualizingComplexIso ℓ i'⟩

/-- **Base change of dualizing complexes along a field extension, embedded case**: for a proper
`F`-scheme `X` with a closed immersion into an `F`-scheme `P` smooth of pure relative dimension
`d`, and its base change along a field extension `L/F`, the comparison
`φ : π^* ω_X ⟶ ω_{X'}` of the dualizing complexes is an isomorphism, given the pullback
`π_P^* ℚ̄_ℓ(d)[2d] ≅ ℚ̄_ℓ(d)[2d]` of the Tate twists. -/
theorem isIso_dualizingComplexBaseChange_of_isClosedImmersion_of_tateTwistIso
    [IsProper (toPoint X).left]
    [IsProper (toPoint X').left]
    (e : (boundedConstructibleUpperStarOfMap ℓ (X := point F) (Y := point L)
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e]
    (sqX : IsPullback π (toPoint X').left (toPoint X).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (d : ℕ) [SmoothOfRelativeDimension d (toPoint P).left]
    [SmoothOfRelativeDimension d (toPoint P').left]
    (hP : IsPullback πP P'.hom P.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sq : IsPullback π i'.left i.left πP)
    (eT : (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP).obj
        (boundedConstructibleTateTwist ℓ P d (2 * d)) ≅
      boundedConstructibleTateTwist ℓ P' d (2 * d)) :
    IsIso (dualizingComplexBaseChange ℓ e sqX) :=
  isIso_dualizingComplexBaseChange_of_iso ℓ e sqX
    (nonempty_iso_dualizingComplex_of_isClosedImmersion ℓ d hP sq eT).some

/-- **The pullback of the shifted Tate twists across fields**: for `P` over `F` and `P'` over `L`,
quasi-compact and quasi-separated, and any `πP : P' ⟶ P`,
`πP^* ℚ̄_ℓ(d)[n] ≅ ℚ̄_ℓ(d)[n]` on bounded constructible complexes
(`ProEtale.upperStarTateTwistDerivedIso`). -/
noncomputable def boundedConstructibleUpperStarOfMapTateTwistIso (πP : P'.left ⟶ P.left)
    (d n : ℤ) :
    (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP).obj
        (boundedConstructibleTateTwist ℓ P d n) ≅
      boundedConstructibleTateTwist ℓ P' d n :=
  have : NeZero (ℓ : F) := neZero_natCast_of_ringChar_ne ℓ
  have := QuasiCompact.compactSpace_of_compactSpace P.hom
  have := QuasiCompact.compactSpace_of_compactSpace P'.hom
  have := quasiSeparatedSpace_of_quasiSeparated P.hom
  have := quasiSeparatedSpace_of_quasiSeparated P'.hom
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (((πP)^*⟦Profinite.padicAlgClRingObj ℓ⟧.leftDerivedFunctor.commShiftIso n).app _ ≪≫
      (shiftFunctor _ n).mapIso
        (ProEtale.upperStarTateTwistDerivedIso ℓ πP P.hom d))

/-- **Base change of dualizing complexes along a field extension, embedded case**: for a proper
`F`-scheme `X` with a closed immersion into an `F`-scheme `P` smooth of pure relative dimension
`d`, and its base change along a field extension `L/F`, the comparison
`φ : π^* ω_X ⟶ ω_{X'}` of the dualizing complexes is an isomorphism. -/
theorem isIso_dualizingComplexBaseChange_of_isClosedImmersion_of_smooth
    [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    (e : (boundedConstructibleUpperStarOfMap ℓ (X := point F) (Y := point L)
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e]
    (sqX : IsPullback π (toPoint X').left (toPoint X).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (d : ℕ) [SmoothOfRelativeDimension d (toPoint P).left]
    [SmoothOfRelativeDimension d (toPoint P').left]
    (hP : IsPullback πP P'.hom P.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sq : IsPullback π i'.left i.left πP) :
    IsIso (dualizingComplexBaseChange ℓ e sqX) :=
  isIso_dualizingComplexBaseChange_of_isClosedImmersion_of_tateTwistIso ℓ e sqX d hP sq
    (boundedConstructibleUpperStarOfMapTateTwistIso ℓ πP d (2 * d))

section Projective

variable {X : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {X' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom] {π : X'.left ⟶ X.left}

/-- **Base change of dualizing complexes along a field extension, projective case**: for a closed
`F`-subscheme `X` of a projective space `ℙⁿ_F` and its base change `X'` along a field extension
`L/F`, the comparison `φ : π^* ω_X ⟶ ω_{X'}` of the dualizing complexes is an isomorphism. -/
theorem isIso_dualizingComplexBaseChange_of_projectiveSpace
    [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    (e : (boundedConstructibleUpperStarOfMap ℓ (X := point F) (Y := point L)
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e]
    (sqX : IsPullback π (toPoint X').left (toPoint X).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (n : ℕ) (c : X.left ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of F))) [IsClosedImmersion c]
    (hc : c ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of F)) ↘ Spec (.of F) = X.hom) :
    IsIso (dualizingComplexBaseChange ℓ e sqX) := by
  let πs := Spec.map (CommRingCat.ofHom (algebraMap F L))
  let P : Over (Spec (.of F)) := Over.mk (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of F)) ↘ _)
  let P' : Over (Spec (.of L)) := Over.mk (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of L)) ↘ _)
  have : IsProper P.hom := inferInstanceAs (IsProper (ℙ(ULift.{u} (Fin (n + 1)); _) ↘ _))
  have : IsProper P'.hom := inferInstanceAs (IsProper (ℙ(ULift.{u} (Fin (n + 1)); _) ↘ _))
  let πP : P'.left ⟶ P.left := ProjectiveSpace.map _ πs
  have hP : IsPullback πP P'.hom P.hom πs := ProjectiveSpace.isPullback_map _ πs
  have hX : IsPullback π X'.hom X.hom πs := by simpa using sqX
  let c' : X'.left ⟶ P'.left := hP.lift (π ≫ c) X'.hom (by
    rw [Category.assoc]
    change π ≫ c ≫ P.hom = _
    simp only [P, Over.mk_hom, hc, hX.w])
  have hc'₁ : c' ≫ πP = π ≫ c := hP.lift_fst _ _ _
  have hc'₂ : c' ≫ P'.hom = X'.hom := hP.lift_snd _ _ _
  have sq : IsPullback π c' c πP := by
    refine IsPullback.of_bot ?_ hc'₁.symm hP
    rw [hc'₂]
    exact hc ▸ hX
  have : IsClosedImmersion c' := MorphismProperty.of_isPullback sq inferInstance
  let i : X ⟶ P := Over.homMk c hc
  let i' : X' ⟶ P' := Over.homMk c' hc'₂
  have : IsClosedImmersion i.left := ‹IsClosedImmersion c›
  have : IsClosedImmersion i'.left := ‹IsClosedImmersion c'›
  have : SmoothOfRelativeDimension n (toPoint P).left := by
    rw [toPoint_left]; exact ProjectiveSpace.smoothOfRelativeDimension _ _ (by simp)
  have : SmoothOfRelativeDimension n (toPoint P').left := by
    rw [toPoint_left]; exact ProjectiveSpace.smoothOfRelativeDimension _ _ (by simp)
  exact isIso_dualizingComplexBaseChange_of_isClosedImmersion_of_smooth ℓ (i := i) (i' := i') e sqX
    n hP sq

end Projective

end AlgebraicGeometry.ProEtale.CondensedRing
