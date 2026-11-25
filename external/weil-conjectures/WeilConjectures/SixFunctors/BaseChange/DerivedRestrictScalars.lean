/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

/-!
# Restriction of scalars and the derived base change map

Let `φ : Λ →+* Λ'` be a morphism of commutative rings and consider a commutative square of
schemes `g' ≫ f = f' ≫ g`. Restriction of scalars along `φ` is exact and conservative, and it
commutes with the pullbacks (`AlgebraicGeometry.Etale.isIso_upperStarRestrictScalars`), the
pushforwards and the derived pushforwards on `D⁺`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`). Moreover it carries the
underived base change map over `Λ'` to the one over `Λ`
(`AlgebraicGeometry.Etale.baseChangeMap_app_restrictScalars`). This file proves these
compatibilities on bounded below complexes, together with the general change of coefficients
criterion `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_mapDerivedCategoryPlus_iff`.
From them `WeilConjectures.SixFunctors.BaseChange.DerivedRestrictScalars.IsIso` deduces that for
an object `K ∈ D⁺(X_ét, Λ')`, the derived base change map over `Λ` is an isomorphism at `res K` if
and only if the derived base change map over `Λ'` is one at `K`.

The criterion represents `K` by a bounded below complex `I` of injective objects. The derived
base change maps at `I` and at `R I` are computed by the underived base change maps followed by
the units of the derived pushforwards (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app`),
since the terms of `I` are `f_*`-acyclic, and so are those of `R I` (for restriction of scalars,
`AlgebraicGeometry.Etale.rightAcyclic_lowerStar_restrictScalars_obj`). It is proved for an
arbitrary exact change of coefficients `R` sending injectives to `f_*`-acyclics; proving it over
abstract coefficient categories keeps the kernel from unfolding the concrete pullback and
pushforward functors.

This is the change of coefficients in the proof of the proper base change theorem (blueprint
`proposition-proper-base-change-etale-site--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

section Generic

namespace CategoryTheory

/-- The first half of the diagram chase
`CategoryTheory.isIso_map_comp_iff_of_reflectsIsomorphisms`: a composite `Q(b) ≫ v` is an
isomorphism if and only if `p₁ ≫ u₁` is one, when their images under a functor `R` reflecting
isomorphisms agree up to isomorphisms. -/
lemma isIso_map_comp_iff_isIso_comp_of_reflectsIsomorphisms {𝒟₁ 𝒟₂ ℋ : Type*} [Category* 𝒟₁]
    [Category* 𝒟₂] [Category* ℋ] (R : 𝒟₁ ⥤ 𝒟₂)
    (hR : ∀ {M N : 𝒟₁} (x : M ⟶ N), IsIso (R.map x) ↔ IsIso x) (Q : ℋ ⥤ 𝒟₂)
    {A₁ B₁ C₁ : 𝒟₁} (p₁ : A₁ ⟶ B₁) (u₁ : B₁ ⟶ C₁) {H₃ H₄ : ℋ} {C' V : 𝒟₂}
    (c : R.obj C₁ ⟶ C') [IsIso c] (e₁ : R.obj B₁ ⟶ Q.obj H₃) [IsIso e₁]
    (v : Q.obj H₃ ⟶ V) (w : V ⟶ C') [IsIso w] (hu : R.map u₁ ≫ c = e₁ ≫ v ≫ w)
    (e₀ : R.obj A₁ ⟶ Q.obj H₄) [IsIso e₀] (b : H₄ ⟶ H₃)
    (hp : R.map p₁ ≫ e₁ = e₀ ≫ Q.map b) :
    IsIso (Q.map b ≫ v) ↔ IsIso (p₁ ≫ u₁) := by
  have eq₁ : R.map (p₁ ≫ u₁) ≫ c = e₀ ≫ (Q.map b ≫ v) ≫ w := by
    rw [R.map_comp, Category.assoc, hu, ← Category.assoc, hp]
    simp only [Category.assoc]
  rw [← hR (p₁ ≫ u₁), ← isIso_comp_right_iff (R.map (p₁ ≫ u₁)) c, eq₁,
    isIso_comp_left_iff e₀, isIso_comp_right_iff _ w]

/-- The second half of the diagram chase
`CategoryTheory.isIso_map_comp_iff_of_reflectsIsomorphisms`: a composite `Q(a₂) ≫ u₂` is an
isomorphism if and only if `Q(b) ≫ v` is one, when both are related by a commutative diagram
whose remaining sides are isomorphisms. -/
lemma isIso_map_comp_iff_isIso_map_comp {𝒟 ℋ : Type*} [Category* 𝒟] [Category* ℋ]
    (Q : ℋ ⥤ 𝒟) {H₁ H₂ H₃ H₄ : ℋ} (a₂ : H₁ ⟶ H₂) {C₂ V : 𝒟} (u₂ : Q.obj H₂ ⟶ C₂)
    (b : H₄ ⟶ H₃) (v : Q.obj H₃ ⟶ V) (σ : H₁ ⟶ H₄) [IsIso (Q.map σ)] (τ : H₂ ⟶ H₃)
    (ha : a₂ ≫ τ = σ ≫ b) (z : C₂ ⟶ V) [IsIso z] (ht : Q.map τ ≫ v = u₂ ≫ z) :
    IsIso (Q.map a₂ ≫ u₂) ↔ IsIso (Q.map b ≫ v) := by
  have eq₂ : Q.map σ ≫ Q.map b ≫ v = (Q.map a₂ ≫ u₂) ≫ z := by
    rw [← Q.map_comp_assoc, ← ha, Q.map_comp, Category.assoc, ht, Category.assoc]
  rw [← isIso_comp_left_iff (Q.map σ) (Q.map b ≫ v), eq₂, isIso_comp_right_iff _ z]

/-- A diagram chase deciding when a composite `Q(a₂) ≫ u₂` is an isomorphism, by comparing it
with a composite `p₁ ≫ u₁` through a functor `R` reflecting isomorphisms. In the application `R`
is a change of coefficients on derived categories, `a₂` and `p₁` come from base change maps and
`u₂`, `u₁` are units of derived functors; all the comparison data are isomorphisms. -/
lemma isIso_map_comp_iff_of_reflectsIsomorphisms {𝒟₁ 𝒟₂ ℋ : Type*} [Category* 𝒟₁]
    [Category* 𝒟₂] [Category* ℋ] (R : 𝒟₁ ⥤ 𝒟₂)
    (hR : ∀ {M N : 𝒟₁} (x : M ⟶ N), IsIso (R.map x) ↔ IsIso x) (Q : ℋ ⥤ 𝒟₂)
    {A₁ B₁ C₁ : 𝒟₁} (p₁ : A₁ ⟶ B₁) (u₁ : B₁ ⟶ C₁)
    {H₁ H₂ H₃ H₄ : ℋ} (a₂ : H₁ ⟶ H₂) {C₂ C' V : 𝒟₂} (u₂ : Q.obj H₂ ⟶ C₂)
    (c : R.obj C₁ ⟶ C') [IsIso c] (e₁ : R.obj B₁ ⟶ Q.obj H₃) [IsIso e₁]
    (v : Q.obj H₃ ⟶ V) (w : V ⟶ C') [IsIso w] (hu : R.map u₁ ≫ c = e₁ ≫ v ≫ w)
    (e₀ : R.obj A₁ ⟶ Q.obj H₄) [IsIso e₀] (b : H₄ ⟶ H₃)
    (hp : R.map p₁ ≫ e₁ = e₀ ≫ Q.map b) (σ : H₁ ⟶ H₄) [IsIso (Q.map σ)] (τ : H₂ ⟶ H₃)
    (ha : a₂ ≫ τ = σ ≫ b) (z : C₂ ⟶ V) [IsIso z] (ht : Q.map τ ≫ v = u₂ ≫ z) :
    IsIso (Q.map a₂ ≫ u₂) ↔ IsIso (p₁ ≫ u₁) :=
  (isIso_map_comp_iff_isIso_map_comp Q a₂ u₂ b v σ τ ha z ht).trans
    (isIso_map_comp_iff_isIso_comp_of_reflectsIsomorphisms R hR Q p₁ u₁ c e₁ v w hu e₀ b hp)

end CategoryTheory

namespace CategoryTheory.NatTrans

variable {C D E X : Type*} [Category* C] [Category* D] [Category* E] [Category* X]
  [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive X]

/-- In the ambient homotopy category, a component of `NatTrans.mapHomotopyCategoryPlus τ`
followed by the image under `H` of a component of `NatTrans.mapHomotopyCategoryPlus σ` is
induced by the corresponding morphism of cochain complexes. -/
lemma ι_map_mapHomotopyCategoryPlus_app_comp_map_mapHomotopyCategoryPlus_app
    {L : C ⥤ D} {F : D ⥤ E} {U : D ⥤ X} {H : X ⥤ E} {U' : C ⥤ X}
    [L.Additive] [F.Additive] [U.Additive] [H.Additive] [U'.Additive]
    (τ : F ⟶ U ⋙ H) (σ : L ⋙ U ⟶ U') (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.ι E).map ((NatTrans.mapHomotopyCategoryPlus τ).app
        (L.mapHomotopyCategoryPlus.obj K) ≫
      H.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus σ).app K)) =
    (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj.as) ≫
        (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex σ (ComplexShape.up ℤ)).app K.obj.as)) := by
  obtain ⟨⟨K⟩, hK⟩ := K
  rw [Functor.map_comp, ι_map_mapHomotopyCategoryPlus_app]
  have e : (HomotopyCategory.Plus.ι E).map (H.mapHomotopyCategoryPlus.map
      ((NatTrans.mapHomotopyCategoryPlus σ).app ⟨⟨K⟩, hK⟩)) =
      (H.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.Plus.ι X).map ((NatTrans.mapHomotopyCategoryPlus σ).app ⟨⟨K⟩, hK⟩)) :=
    rfl
  rw [e, ι_map_mapHomotopyCategoryPlus_app]
  exact ((HomotopyCategory.quotient E (ComplexShape.up ℤ)).map_comp _ _).symm

end CategoryTheory.NatTrans

end Generic

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Generic

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

omit [HasSmallSiteSheafify A] in
/-- At a bounded below complex `K` at which the unit `f_* K ⟶ R⁺f_* K` is an isomorphism (for
instance a complex of injectives), the derived base change map is an isomorphism if and only if
the underived base change map `g^* f_* K ⟶ f'_* g'^* K` followed by the unit
`f'_* g'^* K ⟶ R⁺f'_* (g'^* K)` is one. -/
lemma isIso_derivedBaseChangeMapPlus_app_Qh_obj_iff (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A))
    [IsIso ((f)_*[A].rightDerivedFunctorPlusUnith.app K)] :
    IsIso ((derivedBaseChangeMapPlus A sq).app (DerivedCategory.Plus.Qh.obj K)) ↔
      IsIso (DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap A sq)).app K) ≫
        (f')_*[A].rightDerivedFunctorPlusUnith.app
          (((g')^*[A]).mapHomotopyCategoryPlus.obj K)) := by
  rw [← isIso_comp_left_iff (((g)^*[A]).mapDerivedCategoryPlus.map
    ((f)_*[A].rightDerivedFunctorPlusUnith.app K)), derivedBaseChangeMapPlus_fac_app,
    isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff]

end Generic

section ChangeOfCoefficients

variable {A₁ A₂ : Type*} [Category.{u + 1} A₁] [Abelian A₁] [IsGrothendieckAbelian.{u + 1} A₁]
  [Category.{u + 1} A₂] [Abelian A₂] [IsGrothendieckAbelian.{u + 1} A₂]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **Change of coefficients for the derived base change map.** Let
`R : Sheaf X_ét A₁ ⥤ Sheaf X_ét A₂` be an exact functor sending injective sheaves to
`f_*`-acyclic ones, such that on every bounded below complex `K` the underived part
`g^* f_* K ⟶ f'_* g'^* K ⟶ R⁺f'_*(g'^* K)` of the derived base change map for `A₂` at `R K` is
an isomorphism if and only if the one for `A₁` at `K` is one. Then for `K ∈ D⁺(X_ét, A₁)`,
the derived base change map for `A₂` is an isomorphism at `R K` if and only if the one for `A₁`
is an isomorphism at `K`. -/
theorem isIso_derivedBaseChangeMapPlus_app_mapDerivedCategoryPlus_iff
    (R : Sheaf X.smallEtaleTopology A₁ ⥤ Sheaf X.smallEtaleTopology A₂) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (sq : CommSq g' f' f g)
    (hR : ∀ (J : Sheaf X.smallEtaleTopology A₁) [Injective J], ((f)_*[A₂]).rightAcyclic (R.obj J))
    (h : ∀ K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A₁),
      IsIso (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
            (baseChangeMap A₂ sq)).app (R.mapHomotopyCategoryPlus.obj K)) ≫
          (f')_*[A₂].rightDerivedFunctorPlusUnith.app
            (((g')^*[A₂]).mapHomotopyCategoryPlus.obj (R.mapHomotopyCategoryPlus.obj K))) ↔
        IsIso (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
            (baseChangeMap A₁ sq)).app K) ≫
          (f')_*[A₁].rightDerivedFunctorPlusUnith.app
            (((g')^*[A₁]).mapHomotopyCategoryPlus.obj K)))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A₁)) :
    IsIso ((derivedBaseChangeMapPlus A₂ sq).app (R.mapDerivedCategoryPlus.obj K)) ↔
      IsIso ((derivedBaseChangeMapPlus A₁ sq).app K) := by
  let C := Sheaf X.smallEtaleTopology A₁
  obtain ⟨K₀, ⟨eK⟩⟩ : ∃ K₀ : HomotopyCategory.Plus C,
      Nonempty (DerivedCategory.Plus.Qh.obj K₀ ≅ K) :=
    ⟨_, ⟨DerivedCategory.Plus.Qh.objObjPreimageIso K⟩⟩
  obtain ⟨M, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K₀
  obtain ⟨a, _⟩ := M.2
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective M a
  let T' := (InjectiveObject.ι C).mapCochainComplexPlus.obj T
  have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hi)
  let e : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj T') ≅ K :=
    (asIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i))).symm ≪≫ eK
  rw [← NatTrans.isIso_app_iff_of_iso _ e,
    ← NatTrans.isIso_app_iff_of_iso _ (R.mapDerivedCategoryPlus.mapIso e),
    NatTrans.isIso_app_iff_of_iso _
      (show R.mapDerivedCategoryPlus.obj
          (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj T')) ≅
          DerivedCategory.Plus.Qh.obj
            (R.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient C).obj T')) from
        R.mapDerivedCategoryPlusFactorsh.app ((HomotopyCategory.Plus.quotient C).obj T'))]
  set K' := (HomotopyCategory.Plus.quotient C).obj T'
  have : IsIso (((f)_*[A₁]).rightDerivedFunctorPlusUnith.app K') :=
    ((f)_*[A₁]).isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic T'
      fun n ↦ have : Injective (T'.obj.X n) := (T.obj.X n).2
        Functor.rightAcyclic_of_injective _
  let LT : CochainComplex.Plus (Sheaf X.smallEtaleTopology A₂) :=
    ⟨(R.mapHomotopyCategoryPlus.obj K').obj.as,
      (HomotopyCategory.plus_quotient_obj_iff _).1 (R.mapHomotopyCategoryPlus.obj K').property⟩
  have : IsIso (((f)_*[A₂]).rightDerivedFunctorPlusUnith.app (R.mapHomotopyCategoryPlus.obj K')) :=
    ((f)_*[A₂]).isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic LT
      fun n ↦ have : Injective (T'.obj.X n) := (T.obj.X n).2
        hR (T'.obj.X n)
  rw [isIso_derivedBaseChangeMapPlus_app_Qh_obj_iff, isIso_derivedBaseChangeMapPlus_app_Qh_obj_iff]
  exact h K'

end ChangeOfCoefficients

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- Restriction of scalars of étale sheaves reflects isomorphisms: it is computed sectionwise,
and restriction of scalars of modules reflects isomorphisms. -/
instance (X : Scheme.{u}) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).ReflectsIsomorphisms where
  reflects {A B} a h := by
    have (U : X.Etaleᵒᵖ) : IsIso (a.hom.app U) := by
      have : IsIso ((ModuleCat.restrictScalars.{u + 1} φ).map (a.hom.app U)) :=
        inferInstanceAs (IsIso (((sheafToPresheaf _ _).map
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).map a)).app U))
      exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars.{u + 1} φ)
    have : ∀ U, IsIso (((sheafToPresheaf _ _).map a).app U) := this
    have : IsIso ((sheafToPresheaf _ _).map a) := NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- Restriction of scalars on the bounded below derived categories reflects isomorphisms: it
commutes with the cohomology sheaves, and restriction of scalars of sheaves reflects
isomorphisms. -/
lemma isIso_restrictScalars_mapDerivedCategoryPlus_map_iff {X : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    (a : K ⟶ L) :
    IsIso ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.map a) ↔
      IsIso a := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [DerivedCategory.Plus.isIso_iff] at h ⊢
  intro n
  have := h n
  have : IsIso ((Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map a)) := by
    exact (NatIso.isIso_map_iff
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusHomologyFunctorIso n)
      a).2 this
  exact isIso_of_reflects_iso _ (Sheaf.restrictScalars X.smallEtaleTopology φ)

section BaseChange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The restriction of scalars of the unit `f_* M ⟶ R⁺f_* M` over `Λ'`, followed by the
comparison `res(R⁺f_* M) ≅ R⁺f_*(res M)`, is the unit over `Λ` at `res M`. -/
lemma restrictScalars_map_rightDerivedFunctorPlusUnit_app (f : X ⟶ Y)
    (M : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        (((f)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlusUnith.app M) ≫
      (rightDerivedLowerStarRestrictScalars φ f).app (DerivedCategory.Plus.Qh.obj M) =
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlusFactorsh.hom.app
        (((f)_*[ModuleCat.{u + 1} Λ']).mapHomotopyCategoryPlus.obj M) ≫
      ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomotopyCategoryPlus.obj M) ≫
      ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusFactorsh.inv.app
          M) := by
  have := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (lowerStarCompRestrictScalarsIso φ f).hom) M
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, lowerStarCompRestrictScalarsIso,
    Iso.refl_hom, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id] at this
  refine this.trans ?_
  erw [Category.id_comp, Category.id_comp, Category.id_comp]

/-- The compatibility `AlgebraicGeometry.Etale.baseChangeMap_app_restrictScalars` of the base
change maps with restriction of scalars, applied degreewise to a bounded below complex. -/
lemma mapHomotopyCategoryPlus_baseChangeMap_restrictScalars (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (NatTrans.mapHomotopyCategoryPlus (baseChangeMap (ModuleCat.{u + 1} Λ) sq)).app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomotopyCategoryPlus.obj K) ≫
      ((f')_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (upperStarRestrictScalars φ g')).app K) =
    (NatTrans.mapHomotopyCategoryPlus (upperStarRestrictScalars φ g)).app
        (((f)_*[ModuleCat.{u + 1} Λ']).mapHomotopyCategoryPlus.obj K) ≫
      (Sheaf.restrictScalars Y'.smallEtaleTopology φ).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap (ModuleCat.{u + 1} Λ') sq)).app K) := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app_comp_map_mapHomotopyCategoryPlus_app,
    NatTrans.ι_map_mapHomotopyCategoryPlus_app_comp_map_mapHomotopyCategoryPlus_app]
  congr 1
  exact HomologicalComplex.hom_ext _ _ fun n ↦
    baseChangeMap_app_restrictScalars φ sq (K.obj.as.X n)

end BaseChange

end Etale

end AlgebraicGeometry
