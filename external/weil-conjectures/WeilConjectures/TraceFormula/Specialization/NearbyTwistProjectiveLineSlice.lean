/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.TateTwist.TateModuleTrivialization
public import WeilConjectures.TateTwist.UpperStarExtendScalars
public import WeilConjectures.TateTwist.Pullback
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityTwistCompositionSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFiniteSupport
public import WeilConjectures.TraceFormula.Specialization.NearbyTwistProjectiveLine
public import WeilConjectures.TraceFormula.Specialization.TraitChangeTrait
public import WeilConjectures.TraceFormula.Specialization.TraitModelGenericPoint

/-!

# The twist equation of the projective line along its slice

Let `S = Spec k'⟦t⟧`, `K` a field extension of `k'` and `x ∈ K`. The generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`AlgebraicGeometry.traitSlice`) followed by the affine chart
`𝔸¹_S ⟶ ℙ¹_S` is the *slice of the projective line*
(`NearbyCyclesModel.projectiveLineSlice`). It is a morphism of models `s_P : P'' ⟶ ℙ¹_S`
(`NearbyCyclesModel.projectiveLineSliceHom`) from the slice trait `P'' = Spec K⟦t⟧`, a trait
model of the point `Spec Frac K⟦t⟧` over the generic base `(Frac K⟦t⟧, 𝟙)`
(`NearbyCyclesModel.sliceTraitPointModel`), to `ℙ¹_S`
(`NearbyCyclesModel.projectiveLineModel`), over
(`NearbyCyclesModel.projectiveLineModel`), over
the slices `c_P : Spec Frac K⟦t⟧ ⟶ ℙ¹_η` and `p_P : Spec K ⟶ ℙ¹_{k'}` of the generic and special
fibres. These are the generic slice `σ_η` and the point `x` of `𝔸¹`, followed by the affine chart
(`NearbyCyclesModel.projectiveLineGenericSlice_eq`,
`NearbyCyclesModel.projectiveLineSpecialSlice_eq`).

These are the inputs `P''`, `s_P` of `NearbyCyclesModel.exists_twist_of_slice_of_composition_law`
for `P = ℙ¹_S`, and the hypothesis on `P` of that lemma, the *twist equation of `θ_{ℙ¹_S}` along
`s_P`*, holds (`NearbyCyclesModel.exists_twist_projectiveLineSlice`), by
`NearbyCyclesModel.exists_twist_of_isIso'`:

* `θ_{ℙ¹_S}` is invertible
  (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_projectiveLineModel`), and so is
  `θ_{P''}` (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_sliceTraitPointModel`, the
  smooth case in relative dimension `0`);
* the pullback exchange `α_{s_P}` is invertible at `ω_{ℙ¹_η}`
  (`NearbyCyclesModel.isIso_boundedConstructiblePullbackExchangeOfMap_projectiveLineSliceHom_app`):
  the specialization units of `ℙ¹_S` and of `P''` are invertible, and `ω_{ℙ¹_η} ≅ ℚ̄_ℓ(1)[2]` is a
  finite direct sum of shifts of the unit, being pulled back from the separably closed point
  `Spec k'` (`NearbyCyclesModel.nonempty_shiftDecomposition_dualizingComplex_projectiveLine`);
* an identification `u_P : c_P^* ω_{ℙ¹_η} ≅ ω ⊗ ℚ̄_ℓ(0)[2]`
  (`NearbyCyclesModel.nonempty_upperStarOfMap_projectiveLineGenericSlice_dualizingComplex_iso`),
  from smooth purity and the triviality of `ℚ̄_ℓ(1)` over the separably closed field `K`
  (`NearbyCyclesModel.nonempty_tateTwistDerived_one_iso_zero`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.ShiftDecomposition

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] {E E' P : C}

/-- A decomposition of `P` into shifts of `E` is one into shifts of any `E' ≅ E`. -/
noncomputable def ofIsoSummand (D : ShiftDecomposition E P) (e : E ≅ E') :
    ShiftDecomposition E' P where
  ι := D.ι
  fintype := D.fintype
  decEq := D.decEq
  deg := D.deg
  incl j := (shiftFunctor C (D.deg j)).map e.inv ≫ D.incl j
  proj j := D.proj j ≫ (shiftFunctor C (D.deg j)).map e.hom
  total := by simp [D.total]
  incl_proj_self j := by simp [reassoc_of% (D.incl_proj_self j)]
  incl_proj_of_ne j j' h := by simp [reassoc_of% (D.incl_proj_of_ne j j' h)]

end CategoryTheory.ShiftDecomposition

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme ProjectiveSpace

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

-- A field is henselian via `Field.henselian`; the separably closed instance gives a second,
-- non-syntactically equal path to `IsDomain (PowerSeries k')`, hence to the field structure on
-- `FractionRing (PowerSeries k')`, whose unification unfolds `ProjectiveSpace`.
attribute [-instance] AlgebraicGeometry.Scheme.isStrictlyHenselianLocalRing_of_isSepClosed

namespace NearbyCyclesModel

/-- The slice trait `Spec K⟦t⟧` as a trait model of the point `Spec Frac K⟦t⟧` over the generic
base `(Frac K⟦t⟧, 𝟙)`. -/
noncomputable abbrev sliceTraitPointModel (K : Type u) [Field K] :
    NearbyCyclesModel (point (FractionRing (PowerSeries K))).left (point K).left :=
  traitModelOfGenericBase (FractionRing (PowerSeries K))
    (𝟙 (Spec (.of (FractionRing (PowerSeries K)))))

section Slice

variable {k' K : Type u} [Field k'] [Field K] [Algebra k' K] (x : K)

/-- The identification `𝔸(ULift (Fin 1); S) ≅ 𝔸(PUnit; S)` of the two presentations of the
affine line, relabelling the single coordinate. -/
noncomputable abbrev affineLineReindexIso (S : Scheme.{u}) :
    𝔸(ULift.{u} (Fin 1); S) ≅ 𝔸(PUnit.{u + 1}; S) :=
  AffineSpace.reindexIso S (Equiv.ofUnique PUnit.{u + 1} (ULift.{u} (Fin 1)))

/-- The slice of the projective line `Spec K⟦t⟧ ⟶ 𝔸¹_S ⟶ ℙ¹_S`: the generic slice followed by
the affine chart. -/
noncomputable def projectiveLineSlice : trait K ⟶ ProjectiveLine (trait k') :=
  traitSlice x ≫ (affineLineReindexIso (trait k')).hom ≫ ProjectiveLine.affineChart (trait k')

/-- The slice of the projective line lies over the trait map. -/
@[reassoc (attr := simp)]
lemma projectiveLineSlice_over :
    projectiveLineSlice x ≫ ProjectiveLine (trait k') ↘ trait k' = traitMap k' K := by
  rw [projectiveLineSlice, Category.assoc, Category.assoc, ProjectiveLine.affineChart_over,
    AffineSpace.reindexIso_hom, AffineSpace.reindex_over, traitSlice_over]

/-- The slice `c_P : Spec Frac K⟦t⟧ ⟶ ℙ¹_η` of the generic fibre of the projective line. -/
noncomputable def projectiveLineGenericSlice :
    Spec (.of (FractionRing (PowerSeries K))) ⟶
      ProjectiveLine (Spec (.of (FractionRing (PowerSeries k')))) :=
  (isPullback_map (ULift.{u} (Fin 2)) (traitGenericSpec k')).lift
    (traitGenericSpec K ≫ projectiveLineSlice x) (traitGenericSpecMap k' K) (by
      rw [Category.assoc, projectiveLineSlice_over, traitGenericSpec_traitMap])

@[reassoc (attr := simp)]
lemma projectiveLineGenericSlice_map :
    projectiveLineGenericSlice (k' := k') x ≫ ProjectiveSpace.map _ (traitGenericSpec k') =
      traitGenericSpec K ≫ projectiveLineSlice x :=
  (isPullback_map _ _).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma projectiveLineGenericSlice_over :
    projectiveLineGenericSlice (k' := k') x ≫
        ProjectiveLine (Spec (.of (FractionRing (PowerSeries k')))) ↘
          Spec (.of (FractionRing (PowerSeries k'))) =
      traitGenericSpecMap k' K :=
  (isPullback_map _ _).lift_snd _ _ _

/-- The slice `p_P : Spec K ⟶ ℙ¹_{k'}` of the special fibre of the projective line. -/
noncomputable def projectiveLineSpecialSlice :
    Spec (.of K) ⟶ ProjectiveLine (Spec (.of k')) :=
  (isPullback_map (ULift.{u} (Fin 2)) (traitClosedPoint k')).lift
    (traitClosedPoint K ≫ projectiveLineSlice x) (Spec.map (CommRingCat.ofHom (algebraMap k' K)))
    (by rw [Category.assoc, projectiveLineSlice_over, traitClosedPoint_traitMap])

@[reassoc (attr := simp)]
lemma projectiveLineSpecialSlice_map :
    projectiveLineSpecialSlice (k' := k') x ≫ ProjectiveSpace.map _ (traitClosedPoint k') =
      traitClosedPoint K ≫ projectiveLineSlice x :=
  (isPullback_map _ _).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma projectiveLineSpecialSlice_over :
    projectiveLineSpecialSlice (k' := k') x ≫ ProjectiveLine (Spec (.of k')) ↘ Spec (.of k') =
      Spec.map (CommRingCat.ofHom (algebraMap k' K)) :=
  (isPullback_map _ _).lift_snd _ _ _

/-- The slice `Spec Ω_K ⟶ ℙ¹_Ω` of the geometric generic fibre of the projective line. -/
noncomputable def projectiveLineGeometricSlice :
    Spec (.of (traitGenericField K)) ⟶ ProjectiveLine (Spec (.of (traitGenericField k'))) :=
  (isPullback_map (ULift.{u} (Fin 2)) (traitGenericPoint k')).lift
    (traitGenericPoint K ≫ projectiveLineSlice x) (traitGenericPointMap k' K) (by
      rw [Category.assoc, projectiveLineSlice_over, traitGenericPoint_traitMap])

@[reassoc (attr := simp)]
lemma projectiveLineGeometricSlice_map :
    projectiveLineGeometricSlice (k' := k') x ≫ ProjectiveSpace.map _ (traitGenericPoint k') =
      traitGenericPoint K ≫ projectiveLineSlice x :=
  (isPullback_map _ _).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma projectiveLineGeometricSlice_over :
    projectiveLineGeometricSlice (k' := k') x ≫
        ProjectiveLine (Spec (.of (traitGenericField k'))) ↘ Spec (.of (traitGenericField k')) =
      traitGenericPointMap k' K :=
  (isPullback_map _ _).lift_snd _ _ _

omit [Algebra k' K] in
/-- The affine chart `𝔸¹ ⟶ ℙ¹` commutes with base change. -/
@[reassoc]
lemma affineChart_map {S T : Scheme.{u}} (f : S ⟶ T) :
    ProjectiveLine.affineChart S ≫ ProjectiveSpace.map _ f =
      AffineSpace.map PUnit.{u + 1} f ≫ ProjectiveLine.affineChart T := by
  rw [ProjectiveLine.affineChart_eq_homOfSections S, homOfSections_map,
    ProjectiveLine.affineChart_eq_homOfSections T, comp_homOfSections]
  refine homOfSections_congr (AffineSpace.map_over f).symm ?_
  rw [ProjectiveLine.appTop_pairSections, map_one, AffineSpace.map_appTop_coord]

omit [Algebra k' K] in
/-- The identification `𝔸(ULift (Fin 1); -) ≅ 𝔸(PUnit; -)` commutes with base change. -/
@[reassoc]
lemma affineLineReindexIso_hom_map {S T : Scheme.{u}} (f : S ⟶ T) :
    (affineLineReindexIso S).hom ≫ AffineSpace.map PUnit.{u + 1} f =
      AffineSpace.map (ULift.{u} (Fin 1)) f ≫ (affineLineReindexIso T).hom := by
  rw [AffineSpace.reindexIso_hom, AffineSpace.reindexIso_hom, AffineSpace.map_reindex]

/-- **The generic slice of `ℙ¹` factors through the affine chart**: `c_P` is the generic slice
`σ_η : Spec Frac K⟦t⟧ ⟶ 𝔸¹_η` (`AlgebraicGeometry.traitGenericSlice`) followed by the affine
chart. -/
lemma projectiveLineGenericSlice_eq :
    projectiveLineGenericSlice (k' := k') x =
      traitGenericSlice x ≫ (affineLineReindexIso _).hom ≫ ProjectiveLine.affineChart _ := by
  refine (isPullback_map (ULift.{u} (Fin 2)) (traitGenericSpec k')).hom_ext ?_ ?_
  · rw [projectiveLineGenericSlice_map, Category.assoc, Category.assoc, affineChart_map,
      affineLineReindexIso_hom_map_assoc, traitGenericSlice_map_assoc, projectiveLineSlice]
  · rw [projectiveLineGenericSlice_over, Category.assoc, Category.assoc,
      ProjectiveLine.affineChart_over, AffineSpace.reindexIso_hom, AffineSpace.reindex_over,
      traitGenericSlice_over]

/-- **The special slice of `ℙ¹` factors through the affine chart**: `p_P` is the point
`x : Spec K ⟶ 𝔸¹_{k'}` (`AlgebraicGeometry.traitSlicePoint`) followed by the affine chart. -/
lemma projectiveLineSpecialSlice_eq :
    projectiveLineSpecialSlice (k' := k') x =
      traitSlicePoint x ≫ (affineLineReindexIso _).hom ≫ ProjectiveLine.affineChart _ := by
  refine (isPullback_map (ULift.{u} (Fin 2)) (traitClosedPoint k')).hom_ext ?_ ?_
  · rw [projectiveLineSpecialSlice_map, Category.assoc, Category.assoc, affineChart_map,
      affineLineReindexIso_hom_map_assoc, ← traitClosedPoint_traitSlice_assoc,
      projectiveLineSlice]
  · rw [projectiveLineSpecialSlice_over, Category.assoc, Category.assoc,
      ProjectiveLine.affineChart_over, AffineSpace.reindexIso_hom, AffineSpace.reindex_over,
      traitSlicePoint_over]

/-- **The slice of the projective line as a morphism of models** `s_P : P'' ⟶ ℙ¹_S`: from the
slice trait `Spec K⟦t⟧`, as a model of the point `Spec Frac K⟦t⟧` over the generic base
(`NearbyCyclesModel.sliceTraitPointModel`), to the projective line over the trait, over
the slices `c_P` and `p_P` of the generic and special fibres. -/
noncomputable def projectiveLineSliceHom :
    (sliceTraitPointModel K).Hom
      (projectiveLineModel k') (projectiveLineGenericSlice x) (projectiveLineSpecialSlice x) where
  total := projectiveLineSlice x
  generic := projectiveLineGeometricSlice x
  comm_j := projectiveLineGeometricSlice_map x
  comm_i := projectiveLineSpecialSlice_map x
  comm_ε := by
    refine (isPullback_map (ULift.{u} (Fin 2)) (traitGenericSpec k')).hom_ext ?_ ?_
    · change projectiveLineGeometricSlice x ≫ ProjectiveSpace.map _ (traitGenericPointToSpec k') ≫
          ProjectiveSpace.map _ (traitGenericSpec k') =
        (traitGenericPointToSpec K ≫ 𝟙 _) ≫ projectiveLineGenericSlice x ≫
          ProjectiveSpace.map _ (traitGenericSpec k')
      rw [← ProjectiveSpace.map_comp, traitGenericPointToSpec_traitGenericSpec,
        projectiveLineGeometricSlice_map, projectiveLineGenericSlice_map, Category.comp_id,
        traitGenericPointToSpec_traitGenericSpec_assoc]
    · change projectiveLineGeometricSlice x ≫ ProjectiveSpace.map _ (traitGenericPointToSpec k') ≫
          ProjectiveLine (Spec (.of (FractionRing (PowerSeries k')))) ↘
            Spec (.of (FractionRing (PowerSeries k'))) =
        (traitGenericPointToSpec K ≫ 𝟙 _) ≫ projectiveLineGenericSlice x ≫
          ProjectiveLine (Spec (.of (FractionRing (PowerSeries k')))) ↘
            Spec (.of (FractionRing (PowerSeries k')))
      rw [ProjectiveSpace.map_over, projectiveLineGeometricSlice_over_assoc,
        projectiveLineGenericSlice_over, Category.comp_id,
        traitGenericPointToSpec_traitGenericSpecMap]

end Slice

section TwistEquation

/-- **The Tate twist `ℚ̄_ℓ(1)` is trivial over a separably closed field**: for a scheme `X` over a
separably closed field `K` in which `ℓ` is invertible, `ℚ̄_ℓ,X(1) ≅ ℚ̄_ℓ,X(0)`: a compatible
system of primitive `ℓⁿ`-th roots of unity of `K` (`IsSepClosed.exists_isPrimitiveRoot_pow_eq`)
trivializes the Tate module (`ProEtale.upperStarMapModTateModuleIsoUnit` along `𝟙 X`). -/
theorem nonempty_tateTwistDerived_one_iso_zero {K : Type u} [Field K] [IsSepClosed K] (ℓ : ℕ)
    [Fact ℓ.Prime] [NeZero (ℓ : K)] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    Nonempty (tateTwistDerived X ℓ ((1 : ℕ) : ℤ) ≅ tateTwistDerived X ℓ 0) := by
  obtain ⟨ζ, hζ, hζ'⟩ := IsSepClosed.exists_isPrimitiveRoot_pow_eq K ℓ
  have : WeaklyEtale (𝟙 X) := MorphismProperty.of_isIso _ _
  let e₁ : tateTwistOne X ℓ ≅ 𝟙_ _ :=
    ((upperStarId (Profinite.padicAlgClRingObj ℓ) X).app _).symm ≪≫
      upperStarExtendScalarsIsoUnit (𝟙 X) (Profinite.padicIntRingObjToPadicAlgCl ℓ)
        (tateModule X ℓ) (upperStarMapModTateModuleIsoUnit (𝟙 X) f ℓ hζ hζ')
  let e₂ : tateTwist X ℓ ((1 : ℕ) : ℤ) ≅ 𝟙_ _ :=
    (λ_ (tateTwistOne X ℓ) ≪≫ e₁ : 𝟙_ _ ⊗ tateTwistOne X ℓ ≅ 𝟙_ _)
  exact ⟨(DerivedCategory.singleFunctor _ 0).mapIso e₂ ≪≫
    DerivedCategory.singleFunctorObjUnitIso _ ≪≫
    (tateTwistDerivedZeroIso ℓ X).symm⟩

variable (K : Type u) [Field K]

/-- The slice trait is a trait model of the point `Spec Frac K⟦t⟧` over the generic base
`(Frac K⟦t⟧, 𝟙)`. -/
theorem isTraitModelOfGenericBase_sliceTraitPointModel :
    (sliceTraitPointModel K).IsTraitModelOfGenericBase (point (FractionRing (PowerSeries K)))
      (𝟙 (Spec (.of (FractionRing (PowerSeries K))))) (𝟙 (trait K))
      (𝟙 (Spec (.of (traitGenericField K)))) :=
  isTraitModelOfGenericBase_traitModelOfGenericBase _ _

/-- The geometric generic fibre of the slice trait is the full base change of the point. -/
lemma isPullback_sliceTraitPointModel_ε :
    IsPullback (sliceTraitPointModel K).ε (𝟙 (Spec (.of (traitGenericField K))))
      (point (FractionRing (PowerSeries K))).hom
      (traitGenericPointToSpec K ≫ 𝟙 (Spec (.of (FractionRing (PowerSeries K))))) := by
  have : IsIso (point (FractionRing (PowerSeries K))).hom := IsIso.id _
  have : IsIso (𝟙 (Spec (.of (traitGenericField K)))) := IsIso.id _
  exact IsPullback.of_vert_isIso ⟨rfl⟩

/-- The structure morphism of the point is proper. -/
instance isProper_toPoint_point (F : Type u) [Field F] : IsProper (toPoint (point F)).left := by
  rw [toPoint_left]
  exact inferInstanceAs (IsProper (𝟙 _))

/-- The structure morphism of the point is smooth of relative dimension `0`. -/
instance smoothOfRelativeDimension_toPoint_point (F : Type u) [Field F] :
    SmoothOfRelativeDimension 0 (toPoint (point F)).left := by
  rw [toPoint_left]
  exact inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 _))

variable {K} {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed K] [Fact (ringChar K).Prime]
  [Fact (ringChar K ≠ ℓ)] [Fact (ringChar (FractionRing (PowerSeries K))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries K)) ≠ ℓ)]

/-- **The dualizing map of the slice trait is an isomorphism**: the trait is smooth and proper of
relative dimension `0` over itself, with full geometric generic fibre
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_of_smooth`). -/
theorem NearbyDualizingDataOfGenericBase.isIso_θ_sliceTraitPointModel
    (DK : NearbyDualizingDataOfGenericBase K ℓ) :
    IsIso (DK.θ (isTraitModelOfGenericBase_sliceTraitPointModel K)) :=
  have : IsProper (𝟙 (trait K)) := inferInstanceAs (IsProper (𝟙 _))
  have : SmoothOfRelativeDimension 0 (𝟙 (trait K)) :=
    HasRingHomProperty.of_isOpenImmersion
      (RingHom.locally_holdsForLocalizationAway
        RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway).containsIdentities
  DK.isIso_θ_of_smooth (isTraitModelOfGenericBase_sliceTraitPointModel K) 0
    (isPullback_sliceTraitPointModel_ε K)

variable {k' : Type u} [Field k'] [Algebra k' K] (x : K) [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries k'))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ)]

omit [Algebra k' K] [IsSepClosed K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries K))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries K)) ≠ ℓ)] in
/-- **The dualizing complex of `ℙ¹_η` is a finite direct sum of shifts of the unit**: by smooth
purity it is `ℚ̄_ℓ(1)[2]`, the pullback of `ℚ̄_ℓ(1)[2]` along `ℙ¹_η ⟶ Spec k'`
(`ProEtale.upperStarTateTwistDerivedIso`), and every bounded constructible
complex on the separably closed point `Spec k'` is a finite direct sum of shifts of the unit
(`nonempty_shiftDecomposition_of_boundedConstructible`). -/
theorem nonempty_shiftDecomposition_dualizingComplex_projectiveLine :
    Nonempty (ShiftDecomposition (𝟙_ _)
      (dualizingComplex ℓ (overProjectiveLine (point (FractionRing (PowerSeries k'))))).obj) := by
  let f : (overProjectiveLine (point (FractionRing (PowerSeries k')))).left ⟶ Spec (.of k') :=
    (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k' (FractionRing (PowerSeries k'))))
  have : NeZero (ℓ : k') := neZero_natCast_of_ringChar_ne ℓ
  have : CompactSpace (overProjectiveLine (point (FractionRing (PowerSeries k')))).left :=
    QuasiCompact.compactSpace_of_compactSpace
      (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom
  have : QuasiSeparatedSpace (overProjectiveLine (point (FractionRing (PowerSeries k')))).left :=
    quasiSeparatedSpace_of_quasiSeparated
      (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom
  obtain ⟨D₀⟩ := nonempty_shiftDecomposition_of_boundedConstructible ℓ (K := k') _
    (boundedConstructibleTateTwist ℓ (point k') ((1 : ℕ) : ℤ) (2 * ((1 : ℕ) : ℤ))).property
  let e : L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
      (boundedConstructibleTateTwist ℓ (point k') ((1 : ℕ) : ℤ) (2 * ((1 : ℕ) : ℤ))).obj ≅
      (dualizingComplex ℓ (overProjectiveLine (point (FractionRing (PowerSeries k'))))).obj :=
    (L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso (2 * ((1 : ℕ) : ℤ))).app _ ≪≫
      (shiftFunctor _ (2 * ((1 : ℕ) : ℤ))).mapIso
        (ProEtale.upperStarTateTwistDerivedIso ℓ f (𝟙 _) _) ≪≫
      (ObjectProperty.ι _).mapIso (asIso (smoothPurityMap ℓ
        (CondensedRing.toPoint (overProjectiveLine (point (FractionRing (PowerSeries k'))))) 1))
  exact ⟨((D₀.map L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).ofIsoSummand
    (leftDerivedUpperStarUnitIso _ f)).ofIso e⟩

omit [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries K))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries K)) ≠ ℓ)] in
/-- **The pullback exchange of the slice of `ℙ¹_S` is invertible at the dualizing complex**: the
specialization units of `ℙ¹_S` (smooth over the trait,
`NearbyCyclesModel.IsTraitModelOver.isIso_unit_of_smooth`) and of the slice trait are invertible,
so the exchange is invertible at every finite direct sum of shifts of the unit
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_shiftDecomposition`), such as `ω_{ℙ¹_η}`
(`NearbyCyclesModel.nonempty_shiftDecomposition_dualizingComplex_projectiveLine`). -/
theorem isIso_pullbackExchange_projectiveLineSliceHom_app :
    IsIso (((projectiveLineSliceHom x).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app
      (dualizingComplex ℓ (overProjectiveLine (point (FractionRing (PowerSeries k'))))).obj) := by
  have : Smooth (ProjectiveLine (trait k') ↘ trait k') := SmoothOfRelativeDimension.smooth 1 _
  have : IsIso ((projectiveLineModel k').unit (Profinite.padicAlgClRingObj ℓ)) :=
    (isTraitModelOfGenericBase_projectiveLineModel k').isTraitModelOver.isIso_unit_of_smooth
  have : IsIso ((sliceTraitPointModel K).unit (Profinite.padicAlgClRingObj ℓ)) := by
    have h : UpperStarInvertsLowerStarUnit (Profinite.padicAlgClRingObj ℓ) (traitGenericPoint K)
        (traitClosedPoint K) :=
      ⟨isIso_upperStar_traitClosedPoint_map_unit_app _ K,
        isZero_upperStar_traitClosedPoint_obj_rightDerived _ K⟩
    exact (sliceTraitPointModel K).isIso_unit_of_upperStarInvertsLowerStarUnit _ h
  exact Hom.isIso_pullbackExchange_app_of_shiftDecomposition _ _
    nonempty_shiftDecomposition_dualizingComplex_projectiveLine

/-- The pullback exchange of the slice of `ℙ¹_S` on bounded constructible complexes is invertible
at the dualizing complex of `ℙ¹_η`
(`NearbyCyclesModel.isIso_pullbackExchange_projectiveLineSliceHom_app`). -/
instance isIso_boundedConstructiblePullbackExchangeOfMap_projectiveLineSliceHom_app :
    IsIso (((projectiveLineSliceHom x).boundedConstructiblePullbackExchangeOfMap ℓ
        ((isTraitModelOfGenericBase_sliceTraitPointModel K).preservesBoundedConstructible
          (ℓ := ℓ))
        ((isTraitModelOfGenericBase_projectiveLineModel k').preservesBoundedConstructible
          (ℓ := ℓ))).app
        (dualizingComplex ℓ (overProjectiveLine (point (FractionRing (PowerSeries k')))))) := by
  have h := isIso_pullbackExchange_projectiveLineSliceHom_app (ℓ := ℓ) (k' := k') x
  have h₂ := Hom.boundedConstructiblePullbackExchangeOfMap_app_hom ℓ
    (X := overProjectiveLine (point (FractionRing (PowerSeries k'))))
    (X' := overProjectiveLine (point k')) (Y := point (FractionRing (PowerSeries K)))
    (Y' := point K) (projectiveLineSliceHom x)
    ((isTraitModelOfGenericBase_sliceTraitPointModel K).preservesBoundedConstructible
      (ℓ := ℓ))
    ((isTraitModelOfGenericBase_projectiveLineModel k').preservesBoundedConstructible (ℓ := ℓ))
    (dualizingComplex ℓ (overProjectiveLine (point (FractionRing (PowerSeries k')))))
  have : IsIso ((ObjectProperty.ι _).map
      (((projectiveLineSliceHom x).boundedConstructiblePullbackExchangeOfMap ℓ
        ((isTraitModelOfGenericBase_sliceTraitPointModel K).preservesBoundedConstructible
          (ℓ := ℓ))
        ((isTraitModelOfGenericBase_projectiveLineModel k').preservesBoundedConstructible
          (ℓ := ℓ))).app
        (dualizingComplex ℓ (overProjectiveLine (point (FractionRing (PowerSeries k'))))))) := by
    rw [ObjectProperty.ι_map, h₂]
    exact h
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar K).Prime] in
/-- **The identification `u_P`**: `c_P^* ω_{ℙ¹_η} ≅ ω_{Frac K⟦t⟧} ⊗ ℚ̄_ℓ(0)[2]`, by smooth purity
`ω_{ℙ¹_η} ≅ ℚ̄_ℓ(1)[2]` and `ω_{Frac K⟦t⟧} ≅ ℚ̄_ℓ`, the pullback of the Tate twists
(`ProEtale.upperStarTateTwistDerivedIso`) and the triviality of
`ℚ̄_ℓ(1)` over the separably closed field `K`
(`NearbyCyclesModel.nonempty_tateTwistDerived_one_iso_zero`). -/
theorem nonempty_upperStarOfMap_projectiveLineGenericSlice_dualizingComplex_iso :
    Nonempty ((boundedConstructibleUpperStarOfMap ℓ
          (X := overProjectiveLine (point (FractionRing (PowerSeries k'))))
          (Y := point (FractionRing (PowerSeries K))) (projectiveLineGenericSlice x)).obj
          (dualizingComplex ℓ (overProjectiveLine (point (FractionRing (PowerSeries k'))))) ≅
        dualizingComplex ℓ (point (FractionRing (PowerSeries K))) ⊗
          boundedConstructibleTateTwist ℓ (point (FractionRing (PowerSeries K))) 0 2) := by
  have : NeZero (ℓ : K) := neZero_natCast_of_ringChar_ne ℓ
  have : NeZero (ℓ : FractionRing (PowerSeries k')) := neZero_natCast_of_ringChar_ne ℓ
  have : CompactSpace (overProjectiveLine (point (FractionRing (PowerSeries k')))).left :=
    QuasiCompact.compactSpace_of_compactSpace
      (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom
  have : QuasiSeparatedSpace (overProjectiveLine (point (FractionRing (PowerSeries k')))).left :=
    quasiSeparatedSpace_of_quasiSeparated
      (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom
  have : CompactSpace (ProjectiveLine (Spec (.of (FractionRing (PowerSeries k'))))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom
  have : QuasiSeparatedSpace (ProjectiveLine (Spec (.of (FractionRing (PowerSeries k'))))) :=
    quasiSeparatedSpace_of_quasiSeparated
      (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom
  obtain ⟨eT⟩ := nonempty_tateTwistDerived_one_iso_zero ℓ (K := K)
    (X := (point (FractionRing (PowerSeries K))).left)
    (Spec.map (CommRingCat.ofHom ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
      (PowerSeries.C (R := K)))))
  -- the pullback of `ℚ̄_ℓ(1)[2]` along `c_P`
  let b₀ : L((projectiveLineGenericSlice (k' := k') x)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        ((shiftFunctor _ (2 * ((1 : ℕ) : ℤ))).obj
          (tateTwistDerived (overProjectiveLine (point (FractionRing (PowerSeries k')))).left ℓ
            ((1 : ℕ) : ℤ))) ≅
      (shiftFunctor _ (2 * ((1 : ℕ) : ℤ))).obj
        (tateTwistDerived (point (FractionRing (PowerSeries K))).left ℓ 0) :=
    (L((projectiveLineGenericSlice (k' := k') x)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso
        (2 * ((1 : ℕ) : ℤ))).app _ ≪≫
      (shiftFunctor _ (2 * ((1 : ℕ) : ℤ))).mapIso
        (ProEtale.upperStarTateTwistDerivedIso ℓ
          (projectiveLineGenericSlice (k' := k') x)
          (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom ((1 : ℕ) : ℤ) ≪≫ eT)
  let b : (boundedConstructibleUpperStarOfMap ℓ
        (X := overProjectiveLine (point (FractionRing (PowerSeries k'))))
        (Y := point (FractionRing (PowerSeries K))) (projectiveLineGenericSlice (k' := k') x)).obj
        (boundedConstructibleTateTwist ℓ
          (overProjectiveLine (point (FractionRing (PowerSeries k')))) ((1 : ℕ) : ℤ)
          (2 * ((1 : ℕ) : ℤ))) ≅
      boundedConstructibleTateTwist ℓ (point (FractionRing (PowerSeries K))) 0
        (2 * ((1 : ℕ) : ℤ)) :=
    ObjectProperty.isoMk _ b₀
  have h₂ : boundedConstructibleTateTwist ℓ (point (FractionRing (PowerSeries K))) 0
      (2 * ((1 : ℕ) : ℤ)) =
        boundedConstructibleTateTwist ℓ (point (FractionRing (PowerSeries K))) 0 2 :=
    rfl
  -- `ω` of the point is the unit
  let a : (boundedConstructibleTateTwist ℓ (point (FractionRing (PowerSeries K))) ((0 : ℕ) : ℤ)
      (2 * ((0 : ℕ) : ℤ))).obj ≅
      (𝟙_ (Dᵇc((point (FractionRing (PowerSeries K))).left)⟦Profinite.padicAlgClRingObj ℓ⟧)).obj :=
    (shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _ ≪≫
      tateTwistDerivedZeroIso ℓ (point (FractionRing (PowerSeries K))).left
  let ω₀ : dualizingComplex ℓ (point (FractionRing (PowerSeries K))) ≅ 𝟙_ _ :=
    (asIso (smoothPurityMap ℓ
      (CondensedRing.toPoint (point (FractionRing (PowerSeries K)))) 0)).symm ≪≫
      ObjectProperty.isoMk _ a
  exact ⟨(boundedConstructibleUpperStarOfMap ℓ
        (X := overProjectiveLine (point (FractionRing (PowerSeries k'))))
        (Y := point (FractionRing (PowerSeries K)))
        (projectiveLineGenericSlice (k' := k') x)).mapIso
      (asIso (smoothPurityMap ℓ (CondensedRing.toPoint
        (overProjectiveLine (point (FractionRing (PowerSeries k'))))) 1)).symm ≪≫
    b ≪≫ eqToIso h₂ ≪≫ (λ_ _).symm ≪≫ whiskerRightIso ω₀.symm _⟩

/-- **The twist equation of `θ_{ℙ¹_S}` along the slice** `s_P : P'' ⟶ ℙ¹_S` (the hypothesis on
`P = ℙ¹_S` of `NearbyCyclesModel.exists_twist_of_slice_of_composition_law`): `θ_{ℙ¹_S}` and
`θ_{P''}` are invertible
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_projectiveLineModel`,
`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_sliceTraitPointModel`), so is the
pullback exchange `α_{s_P}` at the dualizing complex of `ℙ¹_η`
(`NearbyCyclesModel.isIso_boundedConstructiblePullbackExchangeOfMap_projectiveLineSliceHom_app`),
and an identification `u_P : c_P^* ω_{ℙ¹_η} ≅ ω ⊗ ℚ̄_ℓ(0)[2]` exists
(`NearbyCyclesModel.nonempty_upperStarOfMap_projectiveLineGenericSlice_dualizingComplex_iso`), so
`NearbyCyclesModel.exists_twist_of_isIso'` applies. -/
theorem exists_twist_projectiveLineSlice (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase K ℓ) :
    ∃ (uP : (boundedConstructibleUpperStarOfMap ℓ
          (X := overProjectiveLine (point (FractionRing (PowerSeries k'))))
          (Y := point (FractionRing (PowerSeries K))) (projectiveLineGenericSlice x)).obj
          (dualizingComplex ℓ (overProjectiveLine (point (FractionRing (PowerSeries k'))))) ≅
        dualizingComplex ℓ (point (FractionRing (PowerSeries K))) ⊗
          boundedConstructibleTateTwist ℓ (point (FractionRing (PowerSeries K))) 0 2)
      (vP : (boundedConstructibleUpperStarOfMap ℓ (X := overProjectiveLine (point k'))
          (Y := point K) (projectiveLineSpecialSlice x)).obj
          (dualizingComplex ℓ (overProjectiveLine (point k'))) ≅
        dualizingComplex ℓ (point K) ⊗ boundedConstructibleTateTwist ℓ (point K) 0 2),
      (boundedConstructibleUpperStarOfMap ℓ (X := overProjectiveLine (point k')) (Y := point K)
          (projectiveLineSpecialSlice x)).map
          (D.θ (isTraitModelOfGenericBase_projectiveLineModel k')) ≫ vP.hom =
        ((projectiveLineSliceHom x).boundedConstructiblePullbackExchangeOfMap ℓ
            ((isTraitModelOfGenericBase_sliceTraitPointModel K).preservesBoundedConstructible
              (ℓ := ℓ))
            ((isTraitModelOfGenericBase_projectiveLineModel k').preservesBoundedConstructible
              (ℓ := ℓ))).app
            (dualizingComplex ℓ (overProjectiveLine (point (FractionRing (PowerSeries k'))))) ≫
          (boundedConstructibleNearbyCycles
            ((isTraitModelOfGenericBase_sliceTraitPointModel K).preservesBoundedConstructible
              (ℓ := ℓ))).map uP.hom ≫
          ((sliceTraitPointModel K).zeroTwistIso
            ((isTraitModelOfGenericBase_sliceTraitPointModel K).preservesBoundedConstructible
              (ℓ := ℓ))
            (𝟙 (trait K)) 2 (dualizingComplex ℓ (point (FractionRing (PowerSeries K))))).hom ≫
          DK.θ (isTraitModelOfGenericBase_sliceTraitPointModel K) ▷
            boundedConstructibleTateTwist ℓ (point K) 0 2 := by
  have := D.isIso_θ_projectiveLineModel
  have := DK.isIso_θ_sliceTraitPointModel
  obtain ⟨uP⟩ := nonempty_upperStarOfMap_projectiveLineGenericSlice_dualizingComplex_iso (ℓ := ℓ)
    (k' := k') x
  exact exists_twist_of_isIso' _ _ _ _ uP

end TwistEquation

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
