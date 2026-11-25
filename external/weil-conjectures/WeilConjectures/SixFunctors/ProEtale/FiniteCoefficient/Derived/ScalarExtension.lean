/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIsomorphisms
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-!
# Extension of scalars and the projection map of `Rg_*` on the pro-étale site

Let `S` be a finite free algebra over a Noetherian ring `R`, for instance the ring of integers
`𝒪_{E'}` of a finite extension `E'/E` of `ℓ`-adic fields over `𝒪_E`. Extension of scalars
`N = S ⊗_R - : D(X_proét, R) ⥤ D(X_proét, S)` commutes with the derived pullbacks `Lg^*`, with the
derived tensor products and with the derived direct images `Rg_*`, and it carries the projection
map `Rg_* M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^* L)` over `R` to the one over `S`.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app`:
  the base change map `N (Rg_* M) ⟶ Rg_* (N M)` is invertible. Restriction of scalars `U` is
  conservative, and `U N M` is the sum of copies of `M` indexed by a basis of `S`, on which `U` of
  the base change map is the iterated mate of the commutation of `N` with `Lg^*`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_extendScalars`:
  the transport of the projection formula for `Rg_*` along extension of scalars.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u})

/-- Restriction of scalars of pro-étale sheaves preserves finite colimits: it is the sheafified
postcomposition with restriction of scalars, which is left adjoint to coextension of scalars. -/
instance preservesFiniteColimits_sheafComposeRestrictScalars :
    PreservesFiniteColimits (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)) := by
  have hadj := ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
    hadj.rightAdjoint_preservesLimits
  have : (Scheme.ProEt.topology X).HasSheafCompose
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction (Scheme.ProEt.topology X) hadj).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

/-- Restriction of scalars of pro-étale sheaves reflects isomorphisms, isomorphisms of sheaves
being detected on sections. -/
instance reflectsIsomorphisms_sheafComposeRestrictScalars :
    (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)).ReflectsIsomorphisms where
  reflects {F G} f hf := by
    have : IsIso ((sheafToPresheaf _ _).map ((sheafCompose (Scheme.ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} φ)).map f)) := inferInstance
    have : IsIso f.hom := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro U
      have : IsIso ((ModuleCat.restrictScalars.{u + 1} φ).map (f.hom.app U)) :=
        NatIso.isIso_app_of_isIso
          ((sheafToPresheaf _ _).map ((sheafCompose (Scheme.ProEt.topology X)
            (ModuleCat.restrictScalars.{u + 1} φ)).map f)) U
      have : IsIso ((forget (ModuleCat R)).map
          ((ModuleCat.restrictScalars.{u + 1} φ).map (f.hom.app U))) := inferInstance
      have : IsIso ((forget (ModuleCat S)).map (f.hom.app U)) := this
      exact isIso_of_reflects_iso _ (forget (ModuleCat S))
    have : IsIso ((sheafToPresheaf _ _).map f) := this
    exact isIso_of_reflects_iso f (sheafToPresheaf _ _)

section Linear

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type*) [Ring Λ] [Linear Λ A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pushforward `g_*` on pro-étale sheaves with values in a `Λ`-linear category is
`Λ`-linear: it acts on morphisms by whiskering. -/
instance linear_lowerStar : (g)_*[A].Linear Λ where

/-- The pullback `g^*` on pro-étale sheaves with values in a `Λ`-linear category is `Λ`-linear,
being left adjoint to the `Λ`-linear pushforward. -/
instance linear_upperStar : (g)^*[A].Linear Λ :=
  (upperStarLowerStarAdjunction A g).left_adjoint_linear

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived pullback `Lg^*` on pro-étale sheaves is `Λ`-linear: it is isomorphic to the
functor `D(g^*)` induced by the `Λ`-linear exact functor `g^*`. -/
instance linear_leftDerivedUpperStar : (L((g)^*[A])).Linear Λ :=
  Functor.linear_of_iso Λ ((g)^*[A]).leftDerivedFunctorIsoMapDerivedCategory.symm

/-- The derived pushforward `Rg_*` on pro-étale sheaves is `Λ`-linear, being right adjoint to the
`Λ`-linear `Lg^*`. -/
instance linear_rightDerivedLowerStar : (R((g)_*[A])).Linear Λ :=
  (derivedUpperStarLowerStarAdjunction A g).right_adjoint_linear

end Linear

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]
  (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] [ProEtale.UpperStarPreservesFlat B]
  {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  (E_Y : Sheaf (Scheme.ProEt.topology Y) A ⥤ Sheaf (Scheme.ProEt.topology Y) B) [E_Y.Additive]
  [PreservesFiniteLimits E_Y] [PreservesFiniteColimits E_Y] [E_Y.PreservesFlat]
  [E_Y.IsLeftAdjoint] [E_Y.Monoidal]
  (E_Z : Sheaf (Scheme.ProEt.topology Z) A ⥤ Sheaf (Scheme.ProEt.topology Z) B) [E_Z.Additive]
  [PreservesFiniteLimits E_Z] [PreservesFiniteColimits E_Z] [E_Z.PreservesFlat]
  [E_Z.IsLeftAdjoint] [E_Z.Monoidal]
  (τ : E_Y ⋙ (g)^*[B] ≅ (g)^*[A] ⋙ E_Z) [NatTrans.IsMonoidal τ.hom]

/-- For exact monoidal functors `E` between pro-étale sheaves with coefficients in `A` and in `B`
commuting monoidally with the pullbacks `g^*`, the tensor comparisons of `Lg^*` and of `LE` are
compatible with the derived commutation isomorphism `LE ⋙ Lg^* ≅ Lg^* ⋙ LE`. -/
lemma comparisonCompatible_leftDerivedFunctorCompNatIso :
    Adjunction.ComparisonCompatible
      (Functor.leftDerivedFunctorCompNatIso (ProEtale.upperStar A g) E_Z E_Y
        (ProEtale.upperStar B g) τ)
      (leftDerivedUpperStarTensorComparison _ g) (leftDerivedUpperStarTensorComparison _ g)
      (asIso E_Z.leftDerivedTensorComparison) (asIso E_Y.leftDerivedTensorComparison) := by
  intro a b
  rw [leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison,
    leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison,
    asIso_hom, asIso_hom,
    Functor.map_leftDerivedTensorComparison_comp_eq_of_iso _ _ _ _ τ,
    MonoidalCategory.tensorHom_def]
  rfl

end General

section ScalarExtension

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- Restriction of scalars preserves pro-étale sheaves, being a right adjoint. -/
instance hasSheafCompose_restrictScalars (φ : R →+* S) :
    (Scheme.ProEt.topology X).HasSheafCompose (ModuleCat.restrictScalars.{u + 1} φ) :=
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.restrictScalars.{u + 1} φ) :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).rightAdjoint_preservesLimits
  hasSheafCompose_of_preservesLimitsOfSize _

/-- Restriction of scalars of pro-étale sheaves preserves limits, being a right adjoint. -/
instance preservesLimits_sheafComposeRestrictScalars (φ : R →+* S) :
    PreservesLimits (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)) :=
  (sheafExtendScalarsAdjunction φ X).rightAdjoint_preservesLimits

/-- Extension of scalars along a flat algebra is exact on pro-étale sheaves. -/
instance preservesFiniteLimits_sheafExtendScalars_algebraMap [Module.Flat R S] :
    PreservesFiniteLimits (sheafExtendScalars (algebraMap R S) X) :=
  preservesFiniteLimits_sheafExtendScalars X (RingHom.flat_algebraMap_iff.2 inferInstance)

variable [Module.Flat R S]

/-- The adjunction `L(S ⊗_R -) ⊣ D(res)` on the derived categories of pro-étale sheaves induced
by extension and restriction of scalars, both of which are exact. -/
noncomputable def derivedSheafExtendScalarsAdjunction :
    L(sheafExtendScalars (algebraMap R S) X) ⊣
      D(sheafCompose (Scheme.ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))) :=
  (sheafExtendScalarsAdjunction (algebraMap R S) X).mapDerivedCategoryAdjunction.ofNatIsoLeft
    (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorIsoMapDerivedCategory.symm

variable {X}

local notation "𝐅" => sheafExtendScalars (algebraMap R S) X
set_option hygiene false in
local notation "𝐀" => sheafExtendScalarsAdjunction (algebraMap R S) X
set_option hygiene false in
local notation "𝐆" => sheafCompose (Scheme.ProEt.topology X)
  (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- Let `c : ι → S` be finitely many scalars such that, for every pro-étale sheaf `F` of
`R`-modules, the maps `F ⟶ res (S ⊗_R F)` given by the unit of extension of scalars followed by
multiplication by the `c i` exhibit `res (S ⊗_R F)` as a sum of copies of `F`. Then the same holds
for the unit of the induced adjunction on derived categories, at every object. -/
theorem isIso_biproductDesc_mapDerivedCategoryAdjunction_unit {ι : Type} [Finite ι] (c : ι → S)
    (h : ∀ F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R),
      IsIso (biproduct.desc fun i ↦ (sheafExtendScalarsAdjunction (algebraMap R S) X).unit.app F ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map (c i • 𝟙 _)))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) :
    IsIso (biproduct.desc fun i ↦
      (sheafExtendScalarsAdjunction (algebraMap R S) X).mapDerivedCategoryAdjunction.unit.app M ≫
        D(sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map (c i • 𝟙 _)) := by
  -- the statement for complexes, degreewise
  have hC (K : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) ℤ) :
      IsIso (biproduct.desc fun i ↦ ((𝐀).mapHomologicalComplex _).unit.app K ≫
        ((𝐆).mapHomologicalComplex _).map (c i • 𝟙 _)) := by
    have (n : ℤ) : IsIso ((biproduct.desc fun i ↦ ((𝐀).mapHomologicalComplex _).unit.app K ≫
        ((𝐆).mapHomologicalComplex _).map (c i • 𝟙 _)).f n) := by
      have e : (fun i ↦ (HomologicalComplex.eval _ _ n).map
          (((𝐀).mapHomologicalComplex _).unit.app K ≫
            ((𝐆).mapHomologicalComplex _).map (c i • 𝟙 _))) =
          fun i ↦ (𝐀).unit.app (K.X n) ≫ (𝐆).map (c i • 𝟙 _) := by
        ext i
        simp only [HomologicalComplex.eval_map, HomologicalComplex.comp_f,
          Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
          HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
        rfl
      have : IsIso (biproduct.desc fun i ↦ (HomologicalComplex.eval _ _ n).map
          (((𝐀).mapHomologicalComplex _).unit.app K ≫
            ((𝐆).mapHomologicalComplex _).map (c i • 𝟙 _))) := by
        rw [e]
        exact h (K.X n)
      exact (Functor.isIso_map_biproductDesc (HomologicalComplex.eval _ _ n) _).2 this
    exact HomologicalComplex.Hom.isIso_of_components _
  -- the statement on the image of a complex
  have hQ (K : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) ℤ) :
      IsIso (biproduct.desc fun i ↦ (𝐀).mapDerivedCategoryAdjunction.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) ≫
        (𝐆).mapDerivedCategory.map (c i • 𝟙 _)) := by
    have := hC K
    have := Functor.isIso_biproductDesc_map
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun i ↦ ((𝐀).mapHomologicalComplex _).unit.app K ≫
        ((𝐆).mapHomologicalComplex _).map (c i • 𝟙 _))
    refine isIso_biproductDesc_of_iso _ (fun i ↦
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
        (((𝐀).mapHomologicalComplex _).unit.app K ≫
          ((𝐆).mapHomologicalComplex _).map (c i • 𝟙 _))) (Iso.refl _)
      ((𝐆).mapDerivedCategory.mapIso ((𝐅).mapDerivedCategoryFactorsh.app _) ≪≫
        (𝐆).mapDerivedCategoryFactorsh.app _) (fun i ↦ ?_) this
    have hfac := (𝐀).mapDerivedCategoryAdjunction_unit_app_fac
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hfac
    have e₁ : (c i • 𝟙 ((𝐅).mapDerivedCategory.obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)))) ≫
        (𝐅).mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
        (𝐅).mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            (c i • 𝟙 (((𝐅).mapHomologicalComplex _).obj K))) := by
      erw [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_smul,
        CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul, Category.id_comp]
      erw [Category.comp_id]
    have e₂ := (𝐆).mapDerivedCategoryFactorsh.hom.naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (c i • 𝟙 (((𝐅).mapHomologicalComplex _).obj K)))
    simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at e₂
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.refl_hom, Category.id_comp,
      Category.assoc, Functor.comp_map, Functor.map_comp]
    rw [← reassoc_of% hfac, ← (𝐆).mapDerivedCategory.map_comp_assoc, e₁,
      (𝐆).mapDerivedCategory.map_comp_assoc]
    congr 2
  -- every object is isomorphic to the image of a complex
  let e := DerivedCategory.Qh.objObjPreimageIso M
  refine isIso_biproductDesc_of_iso _ _ e.symm
    ((𝐅.mapDerivedCategory ⋙ (𝐆).mapDerivedCategory).mapIso e.symm) (fun i ↦ ?_)
    (hQ (DerivedCategory.Qh.objPreimage M).as)
  have hu := (𝐀).mapDerivedCategoryAdjunction.unit.naturality
    e.inv
  simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, Functor.comp_map] at hu
  simp only [Functor.comp_obj, Functor.mapIso_hom, Iso.symm_hom, Functor.comp_map,
    Category.assoc, ← (𝐆).mapDerivedCategory.map_comp]
  rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id ((𝐅).mapDerivedCategory.map e.inv),
    ← Linear.comp_smul, (𝐆).mapDerivedCategory.map_comp]
  erw [reassoc_of% hu]
  rfl

/-- For a basis `b` of the finite free `R`-algebra `S` and `M` in `D(X_proét, R)`, the maps
`M ⟶ U N M` obtained from the unit of `N = L(S ⊗_R -) ⊣ U = D(res)` by multiplication with the
`b i` exhibit `U N M` as a sum of copies of `M`. -/
theorem isIso_biproductDesc_derivedSheafExtendScalarsAdjunction_unit [Module.Finite R S]
    [Module.Free R S] {ι : Type} [Finite ι]
    (b : Module.Basis ι R S)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) :
    IsIso (biproduct.desc fun i ↦ (derivedSheafExtendScalarsAdjunction X).unit.app M ≫
      D(sheafCompose (Scheme.ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map ((b i : S) • 𝟙 _)) := by
  have h := isIso_biproductDesc_mapDerivedCategoryAdjunction_unit (fun i ↦ (b i : S))
    (isIso_biproductDesc_sheafExtendScalarsAdjunction_unit b) M
  refine isIso_biproductDesc_of_iso _ _ (Iso.refl _)
    ((𝐆).mapDerivedCategory.mapIso
      ((𝐅).leftDerivedFunctorIsoMapDerivedCategory.app M)) (fun i ↦ ?_) h
  have e : (𝐅).leftDerivedFunctorIsoMapDerivedCategory.inv.app M ≫ ((b i : S) • 𝟙 _) ≫
      (𝐅).leftDerivedFunctorIsoMapDerivedCategory.hom.app M = (b i : S) • 𝟙 _ := by
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.inv_hom_id_app]
  simp only [derivedSheafExtendScalarsAdjunction, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.refl_hom,
    Category.id_comp, Category.assoc, ← Functor.map_comp, e]

variable [Module.Finite R S] [Module.Free R S]
  [Nontrivial R] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The isomorphism `L(S ⊗_R -) ⋙ Lg^* ≅ Lg^* ⋙ L(S ⊗_R -)` of derived functors
`D(Y_proét, R) ⥤ D(Z_proét, S)`, obtained by deriving the isomorphism
`g^* (S ⊗_R F) ≅ S ⊗_R g^* F` of `AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso`. -/
noncomputable abbrev leftDerivedSheafExtendScalarsCompUpperStarIso :
    L(sheafExtendScalars (algebraMap R S) Y) ⋙ L((g)^*[ModuleCat.{u + 1} S]) ≅
      L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) Z) :=
  Functor.leftDerivedFunctorCompNatIso (ProEtale.upperStar _ g)
    (sheafExtendScalars (algebraMap R S) Z) (sheafExtendScalars (algebraMap R S) Y)
    (ProEtale.upperStar _ g) (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g)

/-- **Extension of scalars commutes with `Rg_*`.** For a finite free algebra `S` over a
Noetherian ring `R`, the base change map `L(S ⊗_R -) (Rg_* M) ⟶ Rg_* (L(S ⊗_R -) M)`, the mate of
`AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsCompUpperStarIso`, is an isomorphism.

Restriction of scalars `U` is conservative, and for a basis `b` of `S` the maps `M ⟶ U N M`
given by the unit and the multiplications by the `b i` exhibit `U N M` as a sum of copies of
`M`; the base change map commutes with these multiplications, both sides being `S`-linear, so
`CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_biproductDesc` applies. -/
theorem isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))) :
    IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedSheafExtendScalarsCompUpperStarIso (R := R) (S := S) g).hom).app M) := by
  let b := Module.finBasis R S
  have := isIso_biproductDesc_derivedSheafExtendScalarsAdjunction_unit b M
  have := isIso_biproductDesc_derivedSheafExtendScalarsAdjunction_unit b
    ((R((g)_*[ModuleCat.{u + 1} R])).obj M)
  refine Adjunction.isIso_mateEquiv_app_of_isIso_biproductDesc _ _ _
    (derivedSheafExtendScalarsAdjunction (R := R) (S := S) Y)
    (derivedSheafExtendScalarsAdjunction (R := R) (S := S) Z) M
    (fun i ↦ (b i : S) • 𝟙 _) (fun i ↦ (b i : S) • 𝟙 _) fun i ↦ ?_
  rw [Linear.smul_comp, Category.id_comp, Functor.map_smul, CategoryTheory.Functor.map_id,
    Linear.comp_smul]
  simp

variable [IsNoetherianRing R] [IsNoetherianRing S]

omit [Module.Finite R S] [Module.Free R S] [Nontrivial R] in
/-- The tensor comparisons of `Lg^*` over `R` and over `S` and those of `L(S ⊗_R -)` are
compatible with `AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsCompUpperStarIso`. -/
lemma comparisonCompatible_leftDerivedSheafExtendScalarsCompUpperStarIso :
    Adjunction.ComparisonCompatible
      (leftDerivedSheafExtendScalarsCompUpperStarIso (R := R) (S := S) g)
      (leftDerivedUpperStarTensorComparison _ g) (leftDerivedUpperStarTensorComparison _ g)
      (asIso (sheafExtendScalars (algebraMap R S) Z).leftDerivedTensorComparison)
      (asIso (sheafExtendScalars (algebraMap R S) Y).leftDerivedTensorComparison) :=
  comparisonCompatible_leftDerivedFunctorCompNatIso _ _ g _ _
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g)

/-- **Extension of scalars carries the projection map of `Rg_*` over `R` to the one over `S`.**
Let `S` be a finite free algebra over a Noetherian ring `R`, both Noetherian, and let
`N = L(S ⊗_R -)`. If the projection map `Rg_* M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^* L)` of pro-étale complexes
of `R`-modules is an isomorphism, so is the projection map over `S` at `(N M, N L)`. -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_extendScalars
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R)))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
    [IsIso (((rightDerivedLowerStarProjectionMap _ g).app M).app L)] :
    IsIso (((rightDerivedLowerStarProjectionMap _ g).app
      ((L(sheafExtendScalars (algebraMap R S) Z)).obj M)).app
        ((L(sheafExtendScalars (algebraMap R S) Y)).obj L)) :=
  have : IsIso ((((derivedUpperStarLowerStarAdjunction _ g).rightAdjointProjectionMap
      (leftDerivedUpperStarTensorComparison _ g)).app M).app L) :=
    inferInstanceAs (IsIso (((rightDerivedLowerStarProjectionMap _ g).app M).app L))
  have := isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app (S := S) g M
  have := isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app (S := S) g
    ((derivedTensor _ Z).obj M |>.obj ((L((g)^*[ModuleCat.{u + 1} R])).obj L))
  Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv
    (derivedUpperStarLowerStarAdjunction _ g) (derivedUpperStarLowerStarAdjunction _ g)
    (comparisonCompatible_leftDerivedSheafExtendScalarsCompUpperStarIso g) M L

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Extension of scalars commutes with extension by zero along an open immersion `j`:
`S ⊗_R j_! F ≅ j_! (S ⊗_R F)`. Both sides are left adjoint to the two equal composites of
restriction of scalars and restriction along `j`, and the isomorphism is the conjugate of the
identity. -/
noncomputable def openImmersionLowerShriekCompSheafExtendScalarsIso :
    (j)_!open[ModuleCat.{u + 1} R] ⋙ sheafExtendScalars (algebraMap R S) X ≅
      sheafExtendScalars (algebraMap R S) U ⋙ (j)_!open[ModuleCat.{u + 1} S] :=
  ((conjugateIsoEquiv
    ((openImmersionLowerShriekAdjunction _ j).comp (sheafExtendScalarsAdjunction _ X))
    ((sheafExtendScalarsAdjunction _ U).comp (openImmersionLowerShriekAdjunction _ j))).symm
      (Iso.refl _)).symm

end OpenImmersion

/-- **Extension of scalars carries the projection formula for `Rf_!` over `R` to the one over
`S`.** Let `S` be a finite free algebra over a Noetherian ring `R`, both Noetherian, and let
`c = (X ⟶[i] Z ⟶[g] Y)` be a compactification of `f : X ⟶ Y`. If the projection map
`(Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)` over `R` is an isomorphism, so is the one over `S` at the
scalar extensions `(L(S ⊗_R -) K, L(S ⊗_R -) L)`: on the open part this is the commutation of
extension of scalars with `i_!`, and on the proper part it is
`AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_extendScalars`. -/
theorem hasProjectionFormulaOfCompactification_extendScalars {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
    (h : HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} R) c K L) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} S) c
      ((L(sheafExtendScalars (algebraMap R S) X)).obj K)
      ((L(sheafExtendScalars (algebraMap R S) Y)).obj L) := by
  rw [HasProjectionFormulaOfCompactification, projectionMapOfCompactification_app_app] at h ⊢
  have h' := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ _ h
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_extendScalars (S := S) c.g
    (D((c.i)_!open[ModuleCat.{u + 1} R]).obj K) L
  -- `i_! (S ⊗_R K) ≅ S ⊗_R (i_! K)`
  let e : D((c.i)_!open[ModuleCat.{u + 1} S]).obj
      ((L(sheafExtendScalars (algebraMap R S) X)).obj K) ≅
      (L(sheafExtendScalars (algebraMap R S) c.Z)).obj
        (D((c.i)_!open[ModuleCat.{u + 1} R]).obj K) :=
    D((c.i)_!open[ModuleCat.{u + 1} S]).mapIso
        ((sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorIsoMapDerivedCategory.app K) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekCompSheafExtendScalarsIso (R := R) (S := S) c.i).symm ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).app K ≪≫
      ((sheafExtendScalars (algebraMap R S) c.Z).leftDerivedFunctorIsoMapDerivedCategory.app
        _).symm
  have := NatTrans.isIso_app_app_of_iso
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} S) c.g) e.symm
    (Iso.refl ((L(sheafExtendScalars (algebraMap R S) Y)).obj L))
  infer_instance

end ScalarExtension

end AlgebraicGeometry.ProEtale
