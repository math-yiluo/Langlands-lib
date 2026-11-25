/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIso
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterTower
public import WeilConjectures.CategoryTheory.Center.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperStarMapModLimits
public import WeilConjectures.SixFunctors.ProEtale.UpperStarPreservesLimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import WeilConjectures.CategoryTheory.DerivedCategory.ProductsMapDerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# The action of a uniformizer on `𝒪_E`-complexes

Let `C` be a closed symmetric monoidal Grothendieck abelian category, `R` a commutative algebra
object and `r` an endomorphism of the regular `R`-module. The action `r_M : M ⟶ M` of `r` on the
`R`-modules `M` is an element of the center of `Mod_R(C)` (`CategoryTheory.Mod.regularEndCenter`),
hence induces an element of the center of the derived category `D(Mod_R(C))`. When
`0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, a complex `K` has vanishing derived reduction
`S ⊗ᴸ_R K` if and only if `r` acts invertibly on `K`
(`CategoryTheory.Mod.isZero_leftDerivedFunctor_extendScalars_iff_isIso`): this is the reduction
triangle `K --r--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]`, whose first map we identify with the central action.

For `𝒪_{E,X}`-module objects on `X_proét` and a uniformizer `ϖ` of `𝒪_E`, this yields the
central action `ProEtale.derivedUniformizer` of `ϖ` on `D(X)`, characterizing the complexes with
vanishing first derived reduction (`ProEtale.isZero_derivedReduction_iff_isIso`). The pullback
of module objects commutes with the action of `ϖ`
(`ProEtale.CondensedRing.upperStar_map_padicIntegersCenter_app`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory.Mod

variable {C : Type*} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]

/-- The action `r_M : M ⟶ M` of an endomorphism `r` of the regular `R`-module on the `R`-modules
`M`, as an element of the center of `Mod_R(C)`. -/
noncomputable def regularEndCenter (r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)) : CatCenter (Mod C R) where
  asHom.app M := regularEndSMul r M
  asHom.naturality _ _ g := (regularEndSMul_naturality r g).symm

omit [MonoidalPreadditive C] in
@[simp]
lemma regularEndCenter_app (r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)) (M : Mod C R) :
    (regularEndCenter r).app M = regularEndSMul r M :=
  rfl

variable {r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)} [Abelian.HasFunctorialFlatResolution C]

/-- **The reduction triangle modulo `r`**, with first map the central action of `r`: if
`0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, then for every `K ∈ D(Mod_R(C))` there is a
distinguished triangle `K --r--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]`. -/
theorem exists_distinguished_regularEndCenter_derivedExtendScalars (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (K : DerivedCategory (Mod C R)) :
    ∃ (g : K ⟶ (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K))
      (h : (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K) ⟶
        K⟦(1 : ℤ)⟧),
      Triangle.mk ((regularEndCenter r).derivedCategory.app K) g h ∈
        distTriang (DerivedCategory (Mod C R)) := by
  have := hφ.mono_f
  obtain ⟨P, π, _, hflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have hS := shortExact_regularEndSMulComplex w hφ P
    (fun n ↦ mono_regularEndSMul_of_flat (P.X n) (hflat n))
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  let e₁ : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let e₃ : DerivedCategory.Q.obj
      (((extendScalars φ ⋙ comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K) :=
    ((comap φ).mapDerivedCategoryFactors.app
        (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso
        ((DerivedCategory.quotientCompQhIso (Mod C S)).app
            (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso
        (asIso ((extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P))).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso ((extendScalars φ).leftDerivedFunctor.mapIso
        ((DerivedCategory.quotientCompQhIso (Mod C R)).app P ≪≫ e₁))
  have ha : (regularEndCenter r).derivedCategory.app K =
      e₁.inv ≫ DerivedCategory.Q.map (regularEndSMulComplex r P) ≫ e₁.hom := by
    rw [CatCenter.app_eq_of_iso _ e₁, CatCenter.derivedCategory_app_Q_obj]
    rfl
  refine ⟨e₁.inv ≫ DerivedCategory.Q.map (extendUnitComplexHom φ P) ≫ e₃.hom,
    e₃.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e₁.hom⟦(1 : ℤ)⟧', ?_⟩
  rw [ha]
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ e₁ e₁ e₃ ?_ ?_ ?_).symm
  · simp [DerivedCategory.triangleOfSES]
  · simp [DerivedCategory.triangleOfSES]
  · simp [DerivedCategory.triangleOfSES]

/-- If `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, the derived reduction `S ⊗ᴸ_R K` of a
complex `K` of `R`-modules vanishes if and only if `r` acts invertibly on `K`. -/
theorem isZero_leftDerivedFunctor_extendScalars_iff_isIso (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (K : DerivedCategory (Mod C R)) :
    IsZero ((extendScalars φ).leftDerivedFunctor.obj K) ↔
      IsIso ((regularEndCenter r).derivedCategory.app K) := by
  obtain ⟨g, h, hT⟩ := exists_distinguished_regularEndCenter_derivedExtendScalars w hφ K
  refine Iff.trans ?_ (Triangle.isZero₃_iff_isIso₁ _ hT)
  refine ⟨fun hK ↦ (comap (D := C) φ).mapDerivedCategory.map_isZero hK, fun hK ↦ ?_⟩
  have h₀ : IsZero ((comap (D := C) φ).mapDerivedCategory.obj 0) :=
    (comap (D := C) φ).mapDerivedCategory.map_isZero (isZero_zero _)
  have : IsIso ((comap (D := C) φ).mapDerivedCategory.map
      (0 : (extendScalars φ).leftDerivedFunctor.obj K ⟶ 0)) :=
    isIso_of_source_target_iso_zero _ hK.isoZero h₀.isoZero
  have := isIso_of_reflects_iso (0 : (extendScalars φ).leftDerivedFunctor.obj K ⟶ 0)
    (comap (D := C) φ).mapDerivedCategory
  exact (isZero_zero _).of_iso (asIso (0 : (extendScalars φ).leftDerivedFunctor.obj K ⟶ 0))

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (ϖ : PadicAlgCl.integers ℓ E)

/-- The action of a constant `ϖ ∈ 𝒪_E` on `𝒪_{E,X}`-module objects, as an element of the center
of the category of `𝒪_{E,X}`-module objects. -/
noncomputable abbrev padicIntegersCenter :
    CatCenter (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :=
  Mod.regularEndCenter (padicIntegersRegularEndOfAlgebra X ℓ E ϖ)

/-- The action of a constant `ϖ ∈ 𝒪_E` on the derived category `D(X)` of `𝒪_{E,X}`-module
objects, as an element of its center. -/
noncomputable abbrev derivedUniformizer :
    CatCenter (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :=
  (padicIntegersCenter X ℓ E ϖ).derivedCategory

variable {X ℓ E}

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The first derived reduction of a complex vanishes if and only if its derived extension of
scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` vanishes. -/
lemma isZero_derivedReduction_iff
    (Z : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    IsZero ((derivedReduction X ℓ E).obj Z) ↔
      IsZero ((L(Mod.extendScalars (padicIntegersToResidueField X ℓ E))).obj Z) := by
  refine ⟨fun h ↦ ?_, fun h ↦ (residueFieldModuleSheaf X ℓ E).mapDerivedCategory.map_isZero h⟩
  have := (Mod.derivedExtendMapDerivedCategoryAdjunction
    (padicIntegersToResidueField X ℓ E)).isLeftAdjoint
  have h₀ : IsZero ((Mod.extendScalars
      (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj 0) :=
    (Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map_isZero
      (isZero_zero _)
  have := isIso_leftDerivedFunctor_map_of_isIso_derivedReduction_map X ℓ E (0 : Z ⟶ 0)
    (isIso_of_source_target_iso_zero _ h.isoZero
      ((residueFieldModuleSheaf X ℓ E).mapDerivedCategory.map_isZero h₀).isoZero)
  exact h₀.of_iso (asIso
    ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map (0 : Z ⟶ 0)))

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- For a uniformizer `ϖ` of `𝒪_E`, the first derived reduction of a complex `Z` vanishes if
and only if `ϖ` acts invertibly on `Z`. -/
lemma isZero_derivedReduction_iff_isIso {ϖ : PadicAlgCl.integers ℓ E}
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ})
    (Z : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    IsZero ((derivedReduction X ℓ E).obj Z) ↔ IsIso ((derivedUniformizer X ℓ E ϖ).app Z) := by
  rw [isZero_derivedReduction_iff]
  exact Mod.isZero_leftDerivedFunctor_extendScalars_iff_isIso _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) Z

/-! ### Compatibility of the action of `ϖ` with the pullback -/

namespace CondensedRing

variable (ℓ E) {Y : Scheme.{u}} (f : X ⟶ Y)

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The pushforward of module objects commutes with the action of `ϖ`. -/
lemma lowerStar_map_padicIntegersCenter_app
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :
    (f)_*⟦Profinite.padicIntegersRingObj ℓ E⟧.map ((padicIntegersCenter X ℓ E ϖ).app M) =
      (padicIntegersCenter Y ℓ E ϖ).app ((f)_*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M) :=
  Mod.hom_ext _ _ (lowerStar_map_regularEndSMul ℓ E ϖ f M)

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- **The pullback of module objects commutes with the action of `ϖ`**, by adjunction from the
pushforward. -/
lemma upperStar_map_padicIntegersCenter_app
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y)) :
    (f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.map ((padicIntegersCenter Y ℓ E ϖ).app M) =
      (padicIntegersCenter X ℓ E ϖ).app ((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M) :=
  (upperStarLowerStarAdjunction _ f).map_catCenter_app
    (lowerStar_map_padicIntegersCenter_app ℓ E ϖ f) M

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The levelwise pullback of complexes of module objects commutes with the action of `ϖ` on the
derived categories. -/
lemma mapDerivedCategory_upperStar_map_derivedUniformizer_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y))) :
    ((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).mapDerivedCategory.map
        ((derivedUniformizer Y ℓ E ϖ).app K) =
      (derivedUniformizer X ℓ E ϖ).app
        (((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).mapDerivedCategory.obj K) :=
  CatCenter.mapDerivedCategory_map_derivedCategory_app _
    (upperStar_map_padicIntegersCenter_app ℓ E ϖ f) K

end CondensedRing

/-! ### Countable products -/

/-- **Countable products of abelian pro-étale sheaves are exact**, the pro-étale topos being
replete. -/
instance hasExactLimitsOfShape_discrete_nat_ab (X : Scheme.{u}) :
    HasExactLimitsOfShape (Discrete ℕ) (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  have := Abelian.hasFiniteBiproducts (C := Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
  have := lim_preservesEpimorphisms_of_epi_π_app_zero
    (Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat (S := X))
  hasExactLimitsOfShape_of_preservesEpi _ _

/-- Countable products of module objects over a ring object of abelian pro-étale sheaves are
exact, since they are so on the underlying sheaves. -/
instance hasExactLimitsOfShape_discrete_nat_mod (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasExactLimitsOfShape (Discrete ℕ) (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  HasExactLimitsOfShape.domain_of_functor _ (Mod.forget R)

/-- The derived category of `𝒪_{E,X}`-module objects has countable products. -/
instance hasCountableProducts_derivedCategory_padicIntegers (X : Scheme.{u}) :
    HasCountableProducts (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :=
  have := CountableAB4Star.of_hasExactLimitsOfShape_nat
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
  derivedCategory_hasCountableProducts _

variable {W X : Scheme.{u}} (f : W ⟶ X) [CompactSpace W] [QuasiSeparatedSpace W] [CompactSpace X]
  [QuasiSeparatedSpace X]

/-- The pullback of abelian pro-étale sheaves along a morphism of quasi-compact quasi-separated
schemes preserves countable products. -/
instance preservesLimitsOfShape_discrete_nat_upperStar_ab :
    PreservesLimitsOfShape (Discrete ℕ) ((f)^*[Ab.{u + 1}]) :=
  have := preservesLimitsOfSize_upperStar_ab f
  preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{u + 1}) _

/-- The pullback of `𝒪_E`-module objects along a morphism of quasi-compact quasi-separated schemes
preserves countable products. -/
instance preservesLimitsOfShape_discrete_nat_upperStar_padicIntegers :
    PreservesLimitsOfShape (Discrete ℕ) ((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧) := by
  unfold CondensedRing.upperStar
  infer_instance

/-- The levelwise pullback of complexes of `𝒪_E`-module objects along a morphism of quasi-compact
quasi-separated schemes preserves countable products. -/
instance preservesLimitsOfShape_discrete_nat_mapDerivedCategory_upperStar_padicIntegers :
    PreservesLimitsOfShape (Discrete ℕ)
      ((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).mapDerivedCategory :=
  Functor.preservesLimitsOfShape_discrete_mapDerivedCategory _

end AlgebraicGeometry.ProEtale
