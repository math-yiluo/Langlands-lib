/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.PadicAlgClRetraction

/-!

# The derived extension of scalars `ℚ̄_ℓ,X ⊗ᴸ_{E_X} -` is faithful

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` and `X` a scheme. This file proves
that the derived extension of scalars `T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} -` is faithful
(`AlgebraicGeometry.ProEtale.faithful_derivedExtendScalarsToPadicAlgCl`).

The argument is general: if `φ : R ⟶ S` is a morphism of commutative ring objects with an
`R`-linear retraction `ρ : S ⟶ R`, then the derived extension of scalars `L(S ⊗_R -)` is
faithful (`CategoryTheory.Mod.faithful_leftDerivedFunctor_extendScalars_of_retraction`).
Indeed, the retractions `S ⊗_R M ⟶ M`, `s ⊗ m ↦ ρ(s) m`, of the units `M ⟶ S ⊗_R M`
(`CategoryTheory.Mod.extendScalarsRetraction`) are natural in `M`, so the unit of the levelwise
adjunction on complexes is a split monomorphism. The unit of the derived adjunction
`L(S ⊗_R -) ⊣ D(comap φ)`, followed by the counit of the derived functor, is the image of this
levelwise unit (`CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh`),
so every unit component of the derived adjunction is a monomorphism, and a left adjoint whose
unit components are monomorphisms is faithful.

For `E_X ⟶ ℚ̄_ℓ,X`, the retraction is the image under `p_X^*` of the retraction `ℚ̲̄_ℓ ⟶ E̲` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.PadicAlgClRetraction`.

-/

@[expose] public section

universe v u' u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod

section Retraction

variable {C : Type u'} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]
  (ρ : S ⟶ R)

/-- The retraction of the unit `K ⟶ comap φ (S ⊗_R K)` of the levelwise extension-restriction
adjunction on complexes, induced by an `R`-linear map `ρ : S ⟶ R`. -/
noncomputable def extendScalarsRetractionComplex (hl : φ ▷ S ≫ μ[S] ≫ ρ = R ◁ ρ ≫ μ[R])
    (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R]) (K : CochainComplex (Mod C R) ℤ) :
    ((comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶ K where
  f n := (extendScalarsRetraction φ ρ hl hr).app (K.X n)
  comm' i j _ := ((extendScalarsRetraction φ ρ hl hr).naturality (K.d i j)).symm

omit [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj S] in
/-- If `ρ : S ⟶ R` is an `R`-linear retraction of `φ : R ⟶ S`, the unit of the levelwise
extension-restriction adjunction on complexes is a split monomorphism. -/
lemma extendRestrictAdjunction_mapHomologicalComplex_unit_app_comp_retraction
    (hρ : φ ≫ ρ = 𝟙 R) (hl : φ ▷ S ≫ μ[S] ≫ ρ = R ◁ ρ ≫ μ[R])
    (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R]) (K : CochainComplex (Mod C R) ℤ) :
    ((extendRestrictAdjunction φ).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K ≫
      extendScalarsRetractionComplex φ ρ hl hr K = 𝟙 K := by
  ext n : 1
  exact NatTrans.congr_app (extendRestrictAdjunction_unit_comp_extendScalarsRetraction φ ρ hρ hl hr)
    (K.X n)

/-- If `ρ : S ⟶ R` is an `R`-linear retraction of `φ : R ⟶ S`, every unit component of the
derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` on the image of a complex is a monomorphism. -/
lemma mono_derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh (hρ : φ ≫ ρ = 𝟙 R)
    (hl : φ ▷ S ≫ μ[S] ≫ ρ = R ◁ ρ ≫ μ[R]) (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R])
    (K : CochainComplex (Mod C R) ℤ) :
    Mono ((derivedExtendMapDerivedCategoryAdjunction φ).unit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) := by
  have : IsSplitMono (((extendRestrictAdjunction φ).mapHomotopyCategory
      (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ _).obj K)) := by
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    exact IsSplitMono.mk' ⟨(HomotopyCategory.quotient _ _).map
      (extendScalarsRetractionComplex φ ρ hl hr K), by
        rw [← Functor.map_comp,
          extendRestrictAdjunction_mapHomologicalComplex_unit_app_comp_retraction φ ρ hρ hl hr]
        exact (HomotopyCategory.quotient _ _).map_id K⟩
  have : Mono ((derivedExtendMapDerivedCategoryAdjunction φ).unit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) ≫
      (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj K))) := by
    rw [derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh]
    infer_instance
  exact mono_of_mono _
    ((comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj K)))

/-- If `φ : R ⟶ S` has an `R`-linear retraction `ρ : S ⟶ R`, the derived extension of scalars
`S ⊗ᴸ_R -` is faithful: every unit component of the derived adjunction
`S ⊗ᴸ_R - ⊣ D(comap φ)` is a monomorphism. -/
lemma faithful_leftDerivedFunctor_extendScalars_of_retraction (hρ : φ ≫ ρ = 𝟙 R)
    (hl : φ ▷ S ≫ μ[S] ≫ ρ = R ◁ ρ ≫ μ[R]) (hr : S ◁ φ ≫ μ[S] ≫ ρ = ρ ▷ R ≫ μ[R]) :
    (L(extendScalars φ)).Faithful := by
  have (K : DerivedCategory (Mod C R)) :
      Mono ((derivedExtendMapDerivedCategoryAdjunction φ).unit.app K) := by
    let e := DerivedCategory.Qh.objObjPreimageIso K
    have : Mono ((derivedExtendMapDerivedCategoryAdjunction φ).unit.app
        (DerivedCategory.Qh.obj (DerivedCategory.Qh.objPreimage K))) :=
      mono_derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh φ ρ hρ hl hr
        (DerivedCategory.Qh.objPreimage K).as
    have h := (derivedExtendMapDerivedCategoryAdjunction φ).unit.naturality e.hom
    have : Mono (e.hom ≫ (derivedExtendMapDerivedCategoryAdjunction φ).unit.app K) := by
      rw [← Functor.id_map e.hom, h]
      infer_instance
    exact (mono_comp_iff_of_isIso e.hom _).1 this
  exact (derivedExtendMapDerivedCategoryAdjunction φ).faithful_L_of_mono_unit_app

end Retraction

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- The retraction `ρ : ℚ̄_ℓ,X ⟶ E_X` of the inclusion `E_X ⟶ ℚ̄_ℓ,X`: the image under `p_X^*` of
the retraction `ℚ̲̄_ℓ ⟶ E̲` (`Profinite.padicAlgClRetraction`). -/
noncomputable abbrev padicAlgClRetraction : padicAlgClRingObj X ℓ ⟶ padicSubfieldRingObj X ℓ E :=
  (upperStarFromPoint X).map (Profinite.padicAlgClRetraction ℓ E)

/-- The map `ρ : ℚ̄_ℓ,X ⟶ E_X` is a retraction of the inclusion `E_X ⟶ ℚ̄_ℓ,X`. -/
@[reassoc (attr := simp)]
lemma padicSubfieldRingObjToPadicAlgCl_comp_padicAlgClRetraction :
    padicSubfieldRingObjToPadicAlgCl X ℓ E ≫ padicAlgClRetraction X ℓ E = 𝟙 _ := by
  rw [← Functor.map_comp, Profinite.padicSubfieldRingObjToPadicAlgCl_comp_padicAlgClRetraction,
    CategoryTheory.Functor.map_id]

/-- **`ℚ̄_ℓ,X ⊗ᴸ_{E_X} -` is faithful**: the derived extension of scalars along the inclusion
`E_X ⟶ ℚ̄_ℓ,X` is faithful, since this inclusion has the `E_X`-linear retraction
`ProEtale.padicAlgClRetraction`. -/
instance faithful_derivedExtendScalarsToPadicAlgCl :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).Faithful :=
  Mod.faithful_leftDerivedFunctor_extendScalars_of_retraction _ (padicAlgClRetraction X ℓ E)
    (padicSubfieldRingObjToPadicAlgCl_comp_padicAlgClRetraction X ℓ E)
    (Functor.LaxMonoidal.map_whiskerRight_comp_mul_comp_map (upperStarFromPoint X) _ _
      (Profinite.padicSubfieldRingObjToPadicAlgCl_whiskerRight_comp_mul_comp_padicAlgClRetraction
        ℓ E))
    (Functor.LaxMonoidal.map_whiskerLeft_comp_mul_comp_map (upperStarFromPoint X) _ _
      (Profinite.whiskerLeft_padicSubfieldRingObjToPadicAlgCl_comp_mul_comp_padicAlgClRetraction
        ℓ E))

end AlgebraicGeometry.ProEtale
