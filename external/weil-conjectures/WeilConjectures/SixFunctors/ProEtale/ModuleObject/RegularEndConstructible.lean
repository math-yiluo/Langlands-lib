/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueInputsAcyclic

/-!
# Reduction modulo a regular endomorphism and constructibility

Let `C` be a closed symmetric monoidal Grothendieck abelian category, `φ : R ⟶ S` a morphism of
commutative algebra objects and `r` an endomorphism of the regular `R`-module such that
`0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact (for instance `r` the multiplication by a
uniformizer of `𝒪_E` and `S = 𝔽_E`). This file generalises the results of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible` from
the multiplication by an integer to `r`:

* `CategoryTheory.Mod.isIso_extendRestrictAdjunction_counit_app_of_regularEnd`: for every
  `S`-module `N`, the counit `S ⊗_R N ⟶ N` is an isomorphism;
* `CategoryTheory.Mod.IsFinitelyPresented.of_comap_of_regularEnd`: an `S`-module whose
  restriction of scalars is finitely presented is finitely presented;
* `CategoryTheory.Mod.exists_distinguished_regularEndSMul_derivedExtendScalars`: the reduction
  triangle `K --r--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]`;
* `AlgebraicGeometry.ProEtale.IsConstructibleModuleObject.of_comap_of_regularLift`: on the
  pro-étale site, when `r` is the multiplication by a global section, an `S`-module whose
  restriction of scalars is constructible is constructible.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory

namespace Mod

/-- On the regular module of a commutative algebra object, the multiplication by a global section
`σ` as an endomorphism of the regular module is the action of `σ`. -/
lemma regularLift_regular_hom_eq_globalSmul {C : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] {R : C} [MonObj R] [IsCommMonObj R] (σ : 𝟙_ C ⟶ R) :
    (regularLift (regular R) σ).hom = globalSmul σ (regular R) := by
  have key : (λ_ R).inv ≫ σ ▷ R ≫ μ[R] = (ρ_ R).inv ≫ R ◁ σ ≫ μ[R] := by
    conv_lhs => rw [← IsCommMonObj.mul_comm R]
    rw [BraidedCategory.braiding_naturality_left_assoc, leftUnitor_inv_braiding_assoc]
  exact key.symm

variable {C : Type*} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]
  {r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)}

/-- If `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, then the counit `S ⊗_R N ⟶ N` of the
adjunction between extension and restriction of scalars is an isomorphism for every `S`-module
`N`: `S ⊗_R N = N ⧸ r N = N`. -/
theorem isIso_extendRestrictAdjunction_counit_app_of_regularEnd (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (N : Mod C S) :
    IsIso ((extendRestrictAdjunction φ).counit.app N) := by
  obtain ⟨hex, _⟩ := exact_regularEndSMul_extendUnit w hφ ((comap φ).obj N)
  have : Mono (extendUnit φ ((comap φ).obj N)) := hex.mono_g (regularEndSMul_comap_eq_zero w N)
  have : IsIso (extendUnit φ ((comap φ).obj N)) := isIso_of_mono_of_epi _
  have h := (extendRestrictAdjunction φ).right_triangle_components N
  rw [extendRestrictAdjunction_unit_app] at h
  have : IsIso ((comap φ).map ((extendRestrictAdjunction φ).counit.app N)) := by
    rw [IsIso.eq_inv_of_hom_inv_id h]
    infer_instance
  have : IsIso ((forget S).map ((extendRestrictAdjunction φ).counit.app N)) :=
    inferInstanceAs (IsIso ((forget R).map
      ((comap φ).map ((extendRestrictAdjunction φ).counit.app N))))
  exact isIso_of_reflects_iso _ (forget S)

/-- If `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, an `S`-module whose restriction of scalars
is a finitely presented `R`-module is finitely presented. -/
lemma IsFinitelyPresented.of_comap_of_regularEnd (r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R))
    (w : r.hom ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact) {N : Mod C S}
    (h : IsFinitelyPresented R ((CategoryTheory.Mod.comap φ).obj N)) : IsFinitelyPresented S N :=
  have := isIso_extendRestrictAdjunction_counit_app_of_regularEnd w hφ N
  (IsFinitelyPresented.map (extendScalars φ) (extendScalarsObjRegularIso φ) h).of_iso
    (asIso ((extendRestrictAdjunction φ).counit.app N))

variable [Abelian.HasFunctorialFlatResolution C]

/-- **The reduction triangle modulo `r`**: if `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, then
for every `K ∈ D(Mod_R(C))` there is a distinguished triangle `K ⟶ K ⟶ S ⊗ᴸ_R K ⟶ K[1]` (the
first map being the action of `r`), where the derived extension of scalars `S ⊗ᴸ_R K` is regarded
as a complex of `R`-modules. -/
theorem exists_distinguished_regularEndSMul_derivedExtendScalars (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (K : DerivedCategory (Mod C R)) :
    ∃ (a : K ⟶ K)
      (g : K ⟶ (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K))
      (h : (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K) ⟶
        K⟦(1 : ℤ)⟧),
      Triangle.mk a g h ∈ distTriang (DerivedCategory (Mod C R)) := by
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
  refine ⟨e₁.inv ≫ DerivedCategory.Q.map (regularEndSMulComplex r P) ≫ e₁.hom,
    e₁.inv ≫ DerivedCategory.Q.map (extendUnitComplexHom φ P) ≫ e₃.hom,
    e₃.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e₁.hom⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ e₁ e₁ e₃ ?_ ?_ ?_).symm
  · simp [DerivedCategory.triangleOfSES]
  · simp [DerivedCategory.triangleOfSES]
  · simp [DerivedCategory.triangleOfSES]

end Mod

/-- The image under a lax monoidal functor `F` of the multiplication by a global section `σ` on
the regular module `R` is the multiplication by the global section `ε ≫ F σ` on `F R`. -/
lemma Functor.map_regularLift_regular_hom {C D : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] [Category* D] [MonoidalCategory D] [BraidedCategory D] (F : C ⥤ D)
    [F.LaxMonoidal] {R : C} [MonObj R] [IsCommMonObj R] [IsCommMonObj (F.obj R)]
    (σ : 𝟙_ C ⟶ R) :
    (Mod.regularLift (Mod.regular (F.obj R)) (Functor.LaxMonoidal.ε F ≫ F.map σ)).hom =
      F.map (Mod.regularLift (Mod.regular R) σ).hom := by
  rw [Mod.regularLift_regular_hom_eq_globalSmul, Mod.regularLift_regular_hom_eq_globalSmul,
    Mod.globalSmul_regular_obj]

/-- An exact lax monoidal functor preserves the short exactness of
`0 ⟶ R --σ--> R --φ--> S ⟶ 0`, for the multiplication by a global section `σ`. -/
lemma Functor.shortExact_regularLift_map {C D : Type*} [Category* C] [Abelian C]
    [MonoidalCategory C] [BraidedCategory C] [Category* D] [Abelian D] [MonoidalCategory D]
    [BraidedCategory D] (F : C ⥤ D) [F.LaxMonoidal] [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {R S : C} [MonObj R] [IsCommMonObj R] [IsCommMonObj (F.obj R)]
    {φ : R ⟶ S} {σ : 𝟙_ C ⟶ R} (w : (Mod.regularLift (Mod.regular R) σ).hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) :
    (ShortComplex.mk (Mod.regularLift (Mod.regular (F.obj R))
      (Functor.LaxMonoidal.ε F ≫ F.map σ)).hom (F.map φ)
      (by rw [F.map_regularLift_regular_hom, ← F.map_comp, w, F.map_zero])).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := (ShortComplex.mk _ _ w).map F) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp [F.map_regularLift_regular_hom]) (by simp))
    (hφ.map_of_exact F)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
  [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]
  {σ : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ R}

/-- If `0 ⟶ R --σ--> R --φ--> S ⟶ 0` is short exact for the multiplication by a global section
`σ`, an `S`-module whose restriction of scalars is a pro-étale locally finitely presented
`R`-module is pro-étale locally finitely presented. -/
lemma IsLocallyFinitelyPresented.of_comap_of_regularLift
    (w : (Mod.regularLift (Mod.regular R) σ).hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact)
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFinitelyPresented R ((Mod.comap φ).obj N)) :
    IsLocallyFinitelyPresented S N := by
  obtain ⟨𝒰, h⟩ := h
  refine ⟨𝒰, fun i ↦ ?_⟩
  exact Mod.IsFinitelyPresented.of_comap_of_regularEnd _ _
    ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).shortExact_regularLift_map w hφ)
    ((h i).of_iso (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapModComapIso φ).app N))

/-- If `0 ⟶ R --σ--> R --φ--> S ⟶ 0` is short exact for the multiplication by a global section
`σ`, an `S`-module whose restriction of scalars is a constructible `R`-module is
constructible. -/
lemma IsConstructibleModuleObject.of_comap_of_regularLift
    (w : (Mod.regularLift (Mod.regular R) σ).hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact)
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsConstructibleModuleObject R ((Mod.comap φ).obj N)) :
    IsConstructibleModuleObject S N := by
  obtain ⟨𝒮, h⟩ := h
  refine ⟨𝒮, fun a ↦ ?_⟩
  exact IsLocallyFinitelyPresented.of_comap_of_regularLift _
    ((ProEtale.upperStar Ab.{u + 1} (𝒮.immersion a)).shortExact_regularLift_map w hφ)
    ((h a).of_iso (((ProEtale.upperStar Ab.{u + 1} (𝒮.immersion a)).mapModComapIso φ).app N))

end AlgebraicGeometry.ProEtale
