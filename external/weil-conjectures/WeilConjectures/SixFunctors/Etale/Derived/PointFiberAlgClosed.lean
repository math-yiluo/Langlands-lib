/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AlgebraicClosureColimit
public import WeilConjectures.CategoryTheory.FilteredTwoColimitTransport
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiberRational
public import WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension

/-!
# The `ℚ̄_ℓ` stage of the evaluation at a geometric point

The `ℚ̄_ℓ`-coefficient category `Dᵇc(Y, ℚ̄_ℓ)` is the filtered 2-colimit over the finite
subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` of the rational stages `Dᵇc(Y, E)`, along the scalar extensions
`- ⊗_E F`, and blueprint `lemma-perfect-complexes-geometric-point` defines
`Dᵇ_fd(ℚ̄_ℓ) = 2-colim_E Dᵇ_fd(E)`. The evaluation at the geometric point of `s = Spec k`,
`Fib_s : Dᵇc(s, ℚ̄_ℓ) ⥤ Dᵇ_fd(ℚ̄_ℓ)`, is obtained stagewise from the equivalences
`Fib_s : Dᵇc(s, E) ≌ Dᵇ_fd(E)` (`AlgebraicGeometry.Etale.pointFiberRationalEquivalence`), which are
compatible with the scalar extensions, and passed to the colimit.

We work with the formulation of filtered 2-colimits of
`WeilConjectures.CategoryTheory.FilteredTwoColimit`: a cocone of categories with vertex `D` *is*
the filtered 2-colimit if it satisfies (Obj) and (Hom). The vertex `Dᵇ_fd(ℚ̄_ℓ)` is the bounded
derived category of finite-dimensional `ℚ̄_ℓ`-vector spaces, which is the 2-colimit of the
`Dᵇ_fd(E)` (`PadicAlgCl.fdCocone_isFilteredTwoColimit`). The main statement
(`AlgebraicGeometry.Etale.pointFiberCocone_isFilteredTwoColimit`) is that the cocone
`E ↦ (Fib_s ⊗_E ℚ̄_ℓ : Dᵇc(s, E) ⥤ Dᵇ_fd(ℚ̄_ℓ))` is a filtered 2-colimit: `Fib_s` identifies
`Dᵇc(s, ℚ̄_ℓ) = 2-colim_E Dᵇc(s, E)` with `Dᵇ_fd(ℚ̄_ℓ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open Scheme PadicAlgCl

namespace Etale

attribute [local instance] AlgebraicGeometry.Scheme.Etale.essentiallySmall

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [IsSepClosed k]

section Stage

variable (E : FiniteIntermediateField l)

/-- The universe `u + 1` copy `ULift E` of a finite subextension `E` as an algebra over the
universe `u + 1` copy `Shrink 𝒪_E` of its ring of integers. -/
noncomputable instance algebraIntegersShrinkULift :
    Algebra (Shrink.{u + 1} (PadicAlgCl.integers l E.1)) (ULift.{u + 1} E.1) :=
  (ULift.ringEquiv.symm.toRingHom.comp
    (algebraMap (Shrink.{u + 1} (PadicAlgCl.integers l E.1)) E.1)).toAlgebra

instance isFractionRing_integersShrink_uLift :
    IsFractionRing (Shrink.{u + 1} (PadicAlgCl.integers l E.1)) (ULift.{u + 1} E.1) :=
  IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofRingEquiv (f := ULift.ringEquiv.symm) fun _ ↦ rfl)

instance fact_maximalIdealShrink_stage :
    Fact (∃ ϖ ∈ nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E.1)),
      PadicAlgCl.maximalIdealShrink l E.1 = Ideal.span {ϖ}) :=
  ⟨PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{0, u} l E.1⟩

/-- The rational stage `Dᵇc(s, E) = Dᵇc(s, 𝒪_E)[1/ϖ_E]` over `s = Spec k`, for a finite
subextension `E ⊆ ℚ̄_ℓ`. -/
abbrev RationalPointStage : Type _ :=
  Rationalization (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E.1)))
    (DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E.1)
      (Spec (.of k))).FullSubcategory

/-- `Fib_s : Dᵇc(s, E) ≌ Dᵇ_fd(E)` at the stage `E`, for `E` represented by `ULift E`. -/
noncomputable def pointFiberStageEquivalence :
    RationalPointStage l k E ≌ FdStage.{u} l E :=
  pointFiberRationalEquivalence _ _ _ k

end Stage

section BaseChange

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (hφ : φ.Flat)
  (hex : ∀ K : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    ∃ (K' : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')))
      (η : K ⟶ (derivedRestrictScalars φ (Spec (.of k))).obj K'), IsDerivedBaseChange η)

/-- Over a separably closed point, the global sections commute with derived base change:
`RΓ(s, K ⊗ᴸ_Λ Λ') ≅ RΓ(s, K) ⊗_Λ Λ'` for a flat `Λ ⟶ Λ'`. Both sides are left adjoint to
restriction of scalars, transported along the equivalences `D(Γ)`. -/
noncomputable def pointSectionsDerivedBaseChangeIso :
    derivedBaseChange φ (Spec (.of k)) hex ⋙ (pointSections Λ' k).mapDerivedCategory ≅
      (pointSections Λ k).mapDerivedCategory ⋙ ModuleCat.derivedExtendScalars φ hφ := by
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  letI : (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.functor.Additive :=
    additive_sheafSections_obj Λ _
  letI : (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.inverse.Additive :=
    additive_constantSheaf Λ _
  letI : (constantSheafEquivalenceOfIsSepClosed Λ' (k := k)).symm.functor.Additive :=
    additive_sheafSections_obj Λ' _
  letI : (constantSheafEquivalenceOfIsSepClosed Λ' (k := k)).symm.inverse.Additive :=
    additive_constantSheaf Λ' _
  let eE := (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.mapDerivedCategory
  let eF := (constantSheafEquivalenceOfIsSepClosed Λ' (k := k)).symm.mapDerivedCategory
  let adjM :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).mapDerivedCategoryAdjunction
  let κ₀ : derivedRestrictScalars φ (Spec (.of k)) ⋙ eE.functor ≅
      eF.functor ⋙ (ModuleCat.restrictScalars.{u + 1} φ).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫ (Functor.mapDerivedCategoryCompIso
      (constantSheafEquivalenceOfIsSepClosed Λ' (k := k)).symm.functor
      (ModuleCat.restrictScalars.{u + 1} φ)).symm
  let κ : derivedRestrictScalars φ (Spec (.of k)) ≅
      eF.functor ⋙ (ModuleCat.restrictScalars.{u + 1} φ).mapDerivedCategory ⋙ eE.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ eE.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight κ₀ _ ≪≫ Functor.associator _ _ _
  let adj₂ := (eE.toAdjunction.comp adjM).comp eF.symm.toAdjunction
  let δ := ((derivedBaseChangeAdjunction φ _ hex).ofNatIsoRight κ).leftAdjointUniq adj₂
  exact Functor.isoWhiskerRight δ eF.functor ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ eF.counitIso ≪≫ Functor.rightUnitor _

variable {I : Ideal Λ} {I' : Ideal Λ'} [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] [IsAdicComplete I Λ]
  [IsDomain Λ] [IsPrincipalIdealRing Λ] [IsNoetherianRing Λ'] [Finite (Λ' ⧸ I')]
  [IsAdicComplete I' Λ'] [IsDomain Λ'] [IsPrincipalIdealRing Λ']
  [hI : Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})]
  [hI' : Fact (∃ ϖ ∈ nonZeroDivisors Λ', I' = Ideal.span {ϖ})]

include hI hI' hφ in
/-- Over a separably closed point, derived base change along a flat `Λ ⟶ Λ'` carries the
integral stage into the integral stage. -/
lemma boundedConstructibleIntegral_derivedBaseChange_obj
    {L : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.boundedConstructibleIntegral I (Spec (.of k)) L) :
    DerivedCategory.boundedConstructibleIntegral I' (Spec (.of k))
      ((derivedBaseChange φ (Spec (.of k)) hex).obj L) := by
  obtain ⟨ϖ, hϖ, hIϖ⟩ := hI.out
  obtain ⟨ϖ', hϖ', hIϖ'⟩ := hI'.out
  rw [boundedConstructibleIntegral_iff_boundedConstructible hϖ' hIϖ',
    boundedConstructible_iff_boundedFiniteCohomology]
  refine (_root_.DerivedCategory.boundedFiniteCohomology Λ').prop_of_iso
    ((pointSectionsDerivedBaseChangeIso k φ hφ hex).app L).symm ?_
  exact ModuleCat.boundedFiniteCohomology_derivedExtendScalars_obj φ hφ
    ((boundedConstructible_iff_boundedFiniteCohomology L).1
      ((boundedConstructibleIntegral_iff_boundedConstructible hϖ hIϖ L).1 hL))

end BaseChange

section Transition

/-- The universe `u + 1` copy `Shrink 𝒪_E` of the ring of integers of `E`. -/
abbrev StageInt (E : FiniteIntermediateField l) : Type (u + 1) :=
  Shrink.{u + 1} (PadicAlgCl.integers l E.1)

section IntegralPointStage

variable (E : FiniteIntermediateField l)

/-- The integral stage `Dᵇc(s, 𝒪_E)` over `s = Spec k`, for a finite subextension `E ⊆ ℚ̄_ℓ`. -/
abbrev IntegralPointStage : Type _ :=
  (DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E.1)
    (Spec (.of k))).FullSubcategory

/-! The instances below are shortcuts: they keep the instance arguments in the statements about
the integral stages small, which the export of the theorem statements to the `.olean` file
otherwise traverses unshared. -/

noncomputable instance : Category (IntegralPointStage l k E) := inferInstance

noncomputable instance : Preadditive (IntegralPointStage l k E) := inferInstance

noncomputable instance : Linear (StageInt.{u} l E) (IntegralPointStage l k E) := inferInstance

instance : HasZeroObject (IntegralPointStage l k E) := inferInstance

noncomputable instance : HasShift (IntegralPointStage l k E) ℤ := inferInstance

instance (n : ℤ) : (shiftFunctor (IntegralPointStage l k E) n).Additive := inferInstance

noncomputable instance : Pretriangulated (IntegralPointStage l k E) := inferInstance

end IntegralPointStage

variable {l} {E F : FiniteIntermediateField l} (h : E ≤ F)

/-- The inclusion `E ⊆ F` as an algebra structure. -/
@[reducible] noncomputable def stageAlgebra : Algebra E.1 F.1 :=
  (IntermediateField.inclusion (show E.1 ≤ F.1 from h)).toRingHom.toAlgebra

lemma stageTower :
    letI := stageAlgebra h
    IsScalarTower E.1 F.1 (PadicAlgCl l) :=
  letI := stageAlgebra h
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The inclusion `𝒪_E ⟶ 𝒪_F` of the universe `u + 1` copies of the rings of integers. -/
@[irreducible] noncomputable def integersStageMap : StageInt.{u} l E →+* StageInt.{u} l F :=
  letI := stageAlgebra h
  haveI := stageTower h
  PadicAlgCl.integersShrinkMap l E.1 F.1

lemma integersStageMap_eq :
    integersStageMap.{u} h = (letI := stageAlgebra h
      haveI := stageTower h
      PadicAlgCl.integersShrinkMap l E.1 F.1) := by
  unfold integersStageMap; rfl

lemma integersStageMap_nonZeroDivisors_le :
    nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E.1)) ≤
      (nonZeroDivisors _).comap (integersStageMap.{u} h) :=
  letI := stageAlgebra h
  haveI := stageTower h
  fun _ hx ↦ by
    rw [Submonoid.mem_comap, integersStageMap_eq]
    exact PadicAlgCl.integersShrinkMap_mem_nonZeroDivisors l E.1 F.1 hx

lemma flat_integersStageMap : (integersStageMap.{u} h).Flat := by
  rw [integersStageMap_eq]
  let := stageAlgebra h
  have := stageTower h
  obtain ⟨n, b, -, -⟩ := PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap.{0, u} l E.1 F.1
  let := (PadicAlgCl.integersShrinkMap.{0, u} l E.1 F.1).toAlgebra
  have : Module.Free _ _ := Module.Free.of_basis b
  change Module.Flat _ _
  exact Module.Flat.of_free

/-- Restriction of scalars `D(X_ét, 𝒪_F) ⥤ D(X_ét, 𝒪_E)`. -/
noncomputable abbrev stageRestrictScalars (X : Scheme.{u}) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (StageInt.{u} l F))) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (StageInt.{u} l E))) :=
  let φ := integersStageMap.{u} h
  derivedRestrictScalars φ X

lemma exists_isDerivedBaseChange_integersStageMap {X : Scheme.{u}}
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (StageInt.{u} l E)))) :
    ∃ (K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (StageInt.{u} l F))))
      (η : K ⟶ (stageRestrictScalars h X).obj K'), IsDerivedBaseChange η := by
  unfold stageRestrictScalars
  rw [integersStageMap_eq]
  let := stageAlgebra h
  have := stageTower h
  exact exists_isDerivedBaseChange_integersShrinkMap K

/-- The derived base change `K ↦ K ⊗ᴸ_{𝒪_E} 𝒪_F` on `D(s_ét, 𝒪_E)`, left adjoint to restriction
of scalars. -/
noncomputable def stageDerivedBaseChange :
    DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} (StageInt.{u} l E))) ⥤
    DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} (StageInt.{u} l F))) :=
  let φ := integersStageMap.{u} h
  derivedBaseChange φ (Spec (.of k)) (exists_isDerivedBaseChange_integersStageMap h)


noncomputable instance : (stageDerivedBaseChange k h).CommShift ℤ := by
  unfold stageDerivedBaseChange; infer_instance

instance : (stageDerivedBaseChange k h).IsTriangulated := by
  unfold stageDerivedBaseChange; infer_instance

/-- The scalar extension `K ↦ K ⊗ᴸ_{𝒪_E} 𝒪_F` on the integral stages `Dᵇc(s, 𝒪_E)` over
`s = Spec k`. -/
noncomputable def integralStageTransition :
    IntegralPointStage l k E ⥤ IntegralPointStage l k F :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ stageDerivedBaseChange k h)
    fun L ↦ boundedConstructibleIntegral_derivedBaseChange_obj k _ (flat_integersStageMap h) _ L.2

noncomputable instance : (integralStageTransition k h).CommShift ℤ := by
  unfold integralStageTransition; infer_instance

instance : (integralStageTransition k h).IsTriangulated := by
  unfold integralStageTransition; infer_instance

lemma integralStageTransition_map_smul (r : StageInt.{u} l E) {X Y} (f : X ⟶ Y) :
    (integralStageTransition k h).map (r • f) =
      integersStageMap h r • (integralStageTransition k h).map f :=
  ObjectProperty.hom_ext _ (derivedBaseChange_map_smul _ _ _ r f.hom)

/-- The scalar extension `- ⊗_E F : Dᵇc(s, E) ⥤ Dᵇc(s, F)` of blueprint
`proposition-inverting-ell--2` over `s = Spec k`: the functor induced on the
rationalizations by the derived base change along `𝒪_E ⟶ 𝒪_F`. -/
noncomputable def rationalStageTransition : RationalPointStage l k E ⥤ RationalPointStage l k F :=
  Rationalization.mapOfRingHom (R := StageInt.{u} l E) (R' := StageInt.{u} l F)
    (integersStageMap.{u} h) (integersStageMap_nonZeroDivisors_le h) (integralStageTransition k h)
    (integralStageTransition_map_smul k h)

lemma algebraMap_comp_integersStageMap :
    (algebraMap (StageInt.{u} l F) (ULift.{u + 1} F.1)).comp (integersStageMap h) =
      (stageMap l h).comp (algebraMap (StageInt.{u} l E) (ULift.{u + 1} E.1)) := by
  rw [integersStageMap_eq]
  ext x
  simp [PadicAlgCl.integersShrinkMap, stageMap, RingHom.algebraMap_toAlgebra,
    PadicAlgCl.shrinkRingEquiv]
  rfl

end Transition

section Compatibility

/-- Derived extensions of scalars along equal ring morphisms are isomorphic. -/
noncomputable def derivedExtendScalarsCongr {R S : Type (u + 1)} [CommRing R] [CommRing S]
    {f g : R →+* S} (e : f = g) (hf : f.Flat) (hg : g.Flat) :
    ModuleCat.derivedExtendScalars f hf ≅ ModuleCat.derivedExtendScalars g hg := by
  subst e
  exact Iso.refl _

variable {l} {E F : FiniteIntermediateField l} (h : E ≤ F)

/-- The evaluation at the geometric point commutes with the scalar extension `- ⊗_E F`, on the
integral stage: `Γ(s, K ⊗ᴸ 𝒪_F) ⊗_{𝒪_F} F ≅ (Γ(s, K) ⊗_{𝒪_E} E) ⊗_E F`. -/
noncomputable def pointFiberRationalAuxTransitionIso :
    integralStageTransition k h ⋙ pointFiberRationalAux (PadicAlgCl.maximalIdealShrink l F.1)
      (nonZeroDivisors (StageInt.{u} l F)) (ULift.{u + 1} F.1) k ≅
    pointFiberRationalAux (PadicAlgCl.maximalIdealShrink l E.1)
      (nonZeroDivisors (StageInt.{u} l E)) (ULift.{u + 1} E.1) k ⋙ stageDerived l h := by
  let φ := integersStageMap.{u} h
  let aE := algebraMap (StageInt.{u} l E) (ULift.{u + 1} E.1)
  let aF := algebraMap (StageInt.{u} l F) (ULift.{u + 1} F.1)
  have hφ : φ.Flat := flat_integersStageMap h
  have haE : aE.Flat := flat_algebraMap_of_isLocalization (nonZeroDivisors _) _
  have haF : aF.Flat := flat_algebraMap_of_isLocalization (nonZeroDivisors _) _
  let e₁ := pointSectionsDerivedBaseChangeIso k φ hφ (exists_isDerivedBaseChange_integersStageMap h)
  let e₂ : ModuleCat.derivedExtendScalars φ hφ ⋙ ModuleCat.derivedExtendScalars aF haF ≅
      ModuleCat.derivedExtendScalars aE haE ⋙ stageDerived l h :=
    (ModuleCat.derivedExtendScalarsComp φ aF hφ haF (hφ.comp haF)).symm ≪≫
      derivedExtendScalarsCongr (algebraMap_comp_integersStageMap h) _
        (haE.comp (flat_of_field _)) ≪≫
      ModuleCat.derivedExtendScalarsComp aE (stageMap l h) haE (flat_of_field _) _
  exact Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _)
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁ _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm

/-- `- ⊗_E F` on the rational stages is induced by `- ⊗ᴸ 𝒪_F` on the integral stages. -/
noncomputable def rationalStageTransitionFac :
    Rationalization.Q (R := StageInt.{u} l E) (nonZeroDivisors _)
        (DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E.1)
          (Spec (.of k))).FullSubcategory ⋙ rationalStageTransition k h ≅
      integralStageTransition k h ⋙ Rationalization.Q (R := StageInt.{u} l F) (nonZeroDivisors _)
        (DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l F.1)
          (Spec (.of k))).FullSubcategory := by
  unfold rationalStageTransition
  exact Localization.Lifting.iso _
    (Rationalization.W (R := StageInt.{u} l E) (nonZeroDivisors _) _) _ _

/-- The evaluation at the geometric point commutes with the scalar extension `- ⊗_E F`:
`Fib_s(K ⊗_E F) ≅ Fib_s(K) ⊗_E F` for `K ∈ Dᵇc(s, E)`. -/
noncomputable def pointFiberStageTransitionIso :
    rationalStageTransition k h ⋙ (pointFiberStageEquivalence l k F).functor ≅
      (pointFiberStageEquivalence l k E).functor ⋙ fdTransition l h := by
  let ME := nonZeroDivisors (StageInt.{u} l E)
  let CE := (DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E.1)
    (Spec (.of k))).FullSubcategory
  let MF := nonZeroDivisors (StageInt.{u} l F)
  let ΦE := pointFiberRationalAux (PadicAlgCl.maximalIdealShrink l E.1) ME (ULift.{u + 1} E.1) k
  let ΦF := pointFiberRationalAux (PadicAlgCl.maximalIdealShrink l F.1) MF (ULift.{u + 1} F.1) k
  let HE := pointFiberRationalToDerived (PadicAlgCl.maximalIdealShrink l E.1) ME
    (ULift.{u + 1} E.1) k
  let HF := pointFiberRationalToDerived (PadicAlgCl.maximalIdealShrink l F.1) MF
    (ULift.{u + 1} F.1) k
  letI : Localization.Lifting (Rationalization.Q ME CE) (Rationalization.W ME CE)
      (integralStageTransition k h ⋙ ΦF) (rationalStageTransition k h ⋙ HF) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rationalStageTransitionFac k h) HF ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Rationalization.liftFac MF (ULift.{u + 1} F.1) ΦF
        (pointFiberRationalAux_map_smul_id _ MF _ k))⟩
  letI : Localization.Lifting (Rationalization.Q ME CE) (Rationalization.W ME CE)
      (ΦE ⋙ stageDerived l h) (HE ⋙ stageDerived l h) :=
    ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      (Rationalization.liftFac ME (ULift.{u + 1} E.1) ΦE
        (pointFiberRationalAux_map_smul_id _ ME _ k)) _⟩
  let β := Localization.liftNatIso (Rationalization.Q ME CE) (Rationalization.W ME CE)
    (integralStageTransition k h ⋙ ΦF) (ΦE ⋙ stageDerived l h)
    (rationalStageTransition k h ⋙ HF) (HE ⋙ stageDerived l h)
    (pointFiberRationalAuxTransitionIso k h)
  -- Build the isomorphism after composing with the inclusion `Dᵇ_fd(F) ⥤ D(F)` and pull it back
  -- along the fully faithful whiskering, so that no comparison of components is needed.
  let γF : (pointFiberStageEquivalence l k F).functor ⋙
      (_root_.DerivedCategory.boundedFiniteCohomology _).ι ≅ HF :=
    ObjectProperty.liftCompιIso _ _ _
  let γE : (pointFiberStageEquivalence l k E).functor ⋙
      (_root_.DerivedCategory.boundedFiniteCohomology _).ι ≅ HE :=
    ObjectProperty.liftCompιIso _ _ _
  let δ : fdTransition l h ⋙ (_root_.DerivedCategory.boundedFiniteCohomology _).ι ≅
      (_root_.DerivedCategory.boundedFiniteCohomology _).ι ⋙ stageDerived l h :=
    ObjectProperty.liftCompιIso _ _ _
  exact ((_root_.DerivedCategory.boundedFiniteCohomology _).fullyFaithfulι.whiskeringRight
    _).preimageIso (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ γF ≪≫ β ≪≫
      Functor.isoWhiskerRight γE.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ δ.symm ≪≫ (Functor.associator _ _ _).symm)

end Compatibility

section Colimit

/-- The cocone of categories `E ↦ (Fib_s ⊗_E ℚ̄_ℓ : Dᵇc(s, E) ⥤ Dᵇ_fd(ℚ̄_ℓ))` over the finite
subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, with the scalar extensions `- ⊗_E F` as transition functors:
the evaluation at the geometric point taken stagewise, followed by extension of scalars to
`ℚ̄_ℓ`. -/
noncomputable def pointFiberCocone :
    CategoryCocone (fun E : FiniteIntermediateField l ↦ RationalPointStage.{u} l k E)
      (FdAlgCl.{u} l) :=
  (fdCocone l).transport (fun h ↦ rationalStageTransition k h)
    (fun E ↦ (pointFiberStageEquivalence l k E).functor) (fun h ↦ pointFiberStageTransitionIso k h)

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finite coefficient categories over a point
(stage `ℚ̄_ℓ`).

At the algebraically closed coefficient `ℚ̄_ℓ`, `Dᵇc(s, ℚ̄_ℓ)` is the filtered 2-colimit
`2-colim_E Dᵇc(s, E)` over the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` along the scalar extensions
`- ⊗_E F`, and `Dᵇ_fd(ℚ̄_ℓ) = 2-colim_E Dᵇ_fd(E)` is the bounded derived category of
finite-dimensional `ℚ̄_ℓ`-vector spaces (`PadicAlgCl.fdCocone_isFilteredTwoColimit`). The evaluation
at the geometric point of `s = Spec k`, obtained stagewise from the equivalences
`Fib_s : Dᵇc(s, E) ≌ Dᵇ_fd(E)` (`AlgebraicGeometry.Etale.pointFiberStageEquivalence`), which commute
with the scalar extensions (`AlgebraicGeometry.Etale.pointFiberStageTransitionIso`), and passed to
the colimit, identifies `2-colim_E Dᵇc(s, E)` with `Dᵇ_fd(ℚ̄_ℓ)`: the cocone `E ↦ Fib_s ⊗_E ℚ̄_ℓ`
with vertex `Dᵇ_fd(ℚ̄_ℓ)` is a filtered 2-colimit, i.e. `Fib_s : Dᵇc(s, ℚ̄_ℓ) ≌ Dᵇ_fd(ℚ̄_ℓ)`. -/
theorem pointFiberCocone_isFilteredTwoColimit : (pointFiberCocone l k).IsFilteredTwoColimit :=
  (fdCocone_isFilteredTwoColimit l).transport

end Colimit

end Etale

end AlgebraicGeometry
