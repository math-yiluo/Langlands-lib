/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension

/-!
# The unbounded derived base change map is computed by the underived one

For a commutative square of schemes `g' ≫ f = f' ≫ g`, the derived base change map
`Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` on the unbounded derived categories
(`AlgebraicGeometry.Etale.derivedBaseChangeMap`) is computed on a complex `M` of sheaves on `X`
by the levelwise underived base change map `g^* f_* M ⟶ f'_* g'^* M`
(`AlgebraicGeometry.Etale.baseChangeMap`), read through the units `f_* M ⟶ Rf_* M` and
`f'_* (g'^* M) ⟶ Rf'_* (g'^* M)` of the right derived functors and the counits of the derived
pullbacks (`AlgebraicGeometry.Etale.derivedBaseChangeMap_app_fac`). In particular `Ex_*` is an
isomorphism at `M` as soon as the underived base change map is an isomorphism and both units are
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_isIso`): for instance if `M` is
K-injective and `g'^* M` is a complex of `f'_*`-acyclic sheaves on which `Rf'_*` is computed
termwise.

This is the unbounded counterpart of `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The square isomorphism `g^* ⋙ f'^* ≅ f^* ⋙ g'^*` of a commutative square
(`AlgebraicGeometry.Etale.squareUpperStarIso`), induced on the homotopy categories. -/
noncomputable def squareUpperStarHomotopy (sq : CommSq g' f' f g) :
    TwoSquare ((g)^*[A].mapHomotopyCategory (.up ℤ)) ((f)^*[A].mapHomotopyCategory (.up ℤ))
      ((f')^*[A].mapHomotopyCategory (.up ℤ)) ((g')^*[A].mapHomotopyCategory (.up ℤ)) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).hom ≫
    NatTrans.mapHomotopyCategory (squareUpperStarIso A sq).hom _ ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).inv

/-- On the image of a complex `M`, `AlgebraicGeometry.Etale.squareUpperStarHomotopy` is the square
isomorphism `AlgebraicGeometry.Etale.squareUpperStarIso` applied degreewise. -/
lemma squareUpperStarHomotopy_app_quotient_obj (sq : CommSq g' f' f g)
    (M : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ) :
    (squareUpperStarHomotopy A sq).app ((HomotopyCategory.quotient _ _).obj M) =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (squareUpperStarIso A sq).hom _).app M) := by
  have h (F : Sheaf Y.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A)
      (G : Sheaf X.smallEtaleTopology A ⥤ Sheaf X'.smallEtaleTopology A) [F.Additive]
      [G.Additive] :
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ _).obj M) = 𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app
      ((HomotopyCategory.quotient _ _).obj M)), Iso.hom_inv_id_app,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
  simp only [squareUpperStarHomotopy, NatTrans.comp_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app, h, Category.id_comp, Category.comp_id]
  rfl

/-- The mate of `AlgebraicGeometry.Etale.squareUpperStarHomotopy` with respect to the adjunctions
induced on the homotopy categories is the base change map
`AlgebraicGeometry.Etale.baseChangeMap`, applied degreewise. -/
lemma mateEquiv_squareUpperStarHomotopy_app_quotient_obj (sq : CommSq g' f' f g)
    (M : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    (mateEquiv ((upperStarLowerStarAdjunction A f).mapHomotopyCategory (.up ℤ))
        ((upperStarLowerStarAdjunction A f').mapHomotopyCategory (.up ℤ))
        (squareUpperStarHomotopy A sq)).app ((HomotopyCategory.quotient _ _).obj M) =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (baseChangeMap A sq) _).app M) := by
  have hmate (K : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
      (mateEquiv ((upperStarLowerStarAdjunction A f).mapHomotopyCategory (.up ℤ))
        ((upperStarLowerStarAdjunction A f').mapHomotopyCategory (.up ℤ))
        (squareUpperStarHomotopy A sq)).app K =
      ((upperStarLowerStarAdjunction A f').mapHomotopyCategory (.up ℤ)).unit.app _ ≫
        ((f')_*[A].mapHomotopyCategory (.up ℤ)).map
          ((squareUpperStarHomotopy A sq).app _) ≫
        ((f')_*[A].mapHomotopyCategory (.up ℤ)).map (((g')^*[A].mapHomotopyCategory (.up ℤ)).map
          (((upperStarLowerStarAdjunction A f).mapHomotopyCategory (.up ℤ)).counit.app K)) := by
    simp [mateEquiv_apply]
  have hbc (F : Sheaf X.smallEtaleTopology A) : (baseChangeMap A sq).app F =
      (upperStarLowerStarAdjunction A f').unit.app _ ≫
        (f')_*[A].map ((squareUpperStarIso A sq).hom.app _) ≫
        (f')_*[A].map ((g')^*[A].map ((upperStarLowerStarAdjunction A f).counit.app F)) := by
    simp [baseChangeMap, mateEquiv_apply]
  rw [hmate]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient, squareUpperStarHomotopy_app_quotient_obj,
    Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategory_map,
    Functor.mapHomotopyCategory_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, hbc]
  rfl


section Derived

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

open DerivedCategory

/-- The derived square isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*`
(`AlgebraicGeometry.Etale.derivedSquareUpperStarIso`) is computed on the image of a complex by
the square isomorphism of the underived pullbacks, through the counits of the derived
pullbacks. -/
lemma derivedSquareUpperStarIso_hom_app_Qh_obj (sq : CommSq g' f' f g)
    (N : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    (derivedSquareUpperStarIso A sq).hom.app (Qh.obj N) ≫
        L((g')^*[A]).map ((f)^*[A].leftDerivedFunctorCounit.app N) ≫
        (g')^*[A].leftDerivedFunctorCounit.app (((f)^*[A].mapHomotopyCategory (.up ℤ)).obj N) =
      L((f')^*[A]).map ((g)^*[A].leftDerivedFunctorCounit.app N) ≫
        (f')^*[A].leftDerivedFunctorCounit.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj N) ≫
        Qh.map ((squareUpperStarHomotopy A sq).app N) := by
  have key : Functor.mapHomotopyCategoryCompHom (f)^*[A] (g')^*[A] (g' ≫ f)^*[A]
      (upperStarComp A g' f) N =
    Functor.mapHomotopyCategoryCompHom (g)^*[A] (f')^*[A] (g' ≫ f)^*[A]
      (upperStarComp A f' g (g' ≫ f) sq.w) N ≫ (squareUpperStarHomotopy A sq).app N := by
    simp only [Functor.mapHomotopyCategoryCompHom, squareUpperStarHomotopy, NatTrans.comp_app,
      Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← NatTrans.comp_app_assoc, ← NatTrans.mapHomotopyCategory_comp, squareUpperStarIso,
      Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  rw [derivedSquareUpperStarIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc,
    leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit,
    ← leftDerivedUpperStarComp_inv_app_Qh_obj_comp_counit_assoc A f' g (g' ≫ f) sq.w, key,
    Functor.map_comp]

/-- **The unbounded derived base change map is computed by the underived one.** For a complex
`M` of sheaves on `X`, the derived base change map `Lg^* Rf_* M ⟶ Rf'_* Lg'^* M`, read through
the unit `f_* M ⟶ Rf_* M` and the counit `Lg'^* M ⟶ g'^* M`, is the degreewise underived base
change map `g^* f_* M ⟶ f'_* g'^* M` followed by the unit `f'_* g'^* M ⟶ Rf'_* (g'^* M)`, through
the counit `Lg^* (f_* M) ⟶ g^* f_* M`:
```
Lg^* (f_* M) ──Lg^* (unit)──▶ Lg^* Rf_* M ──(base change)──▶ Rf'_* Lg'^* M
     │                                                            │
  counit                                                   Rf'_* (counit)
     ▼                                                            ▼
g^* f_* M ──(base change)──▶ f'_* g'^* M ──────unit──────▶ Rf'_* (g'^* M)
```
-/
theorem derivedBaseChangeMap_app_fac (sq : CommSq g' f' f g)
    (M : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    L((g)^*[A]).map ((f)_*[A].rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj M)) ≫
      (derivedBaseChangeMap A sq).app (Qh.obj ((HomotopyCategory.quotient _ _).obj M)) ≫
      R((f')_*[A]).map ((g')^*[A].leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj M)) =
    (g)^*[A].leftDerivedFunctorCounit.app
        (((f)_*[A].mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj M)) ≫
      Qh.map ((HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (baseChangeMap A sq) _).app M)) ≫
      (f')_*[A].rightDerivedFunctorUnit.app
        (((g')^*[A].mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj M)) := by
  rw [← mateEquiv_squareUpperStarHomotopy_app_quotient_obj]
  exact Adjunction.derived_mateEquiv_app_fac
    ((upperStarLowerStarAdjunction A f).mapHomotopyCategory (.up ℤ))
    ((upperStarLowerStarAdjunction A f').mapHomotopyCategory (.up ℤ))
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
    (f)^*[A].leftDerivedFunctorCounit (f)_*[A].rightDerivedFunctorUnit
    (f')^*[A].leftDerivedFunctorCounit (f')_*[A].rightDerivedFunctorUnit
    (g)^*[A].leftDerivedFunctorCounit (g')^*[A].leftDerivedFunctorCounit
    (squareUpperStarHomotopy A sq) (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom)
    ((HomotopyCategory.quotient _ _).obj M) (derivedSquareUpperStarIso_hom_app_Qh_obj A sq _)


/-- **The unbounded derived base change map is an isomorphism if the underived one is**, provided
`f'_*` sends exact complexes of `f'_*`-acyclic sheaves to exact complexes (e.g. `f'_*` has
pointwise finite cohomological dimension) and the pullback `g'^* I` of every injective sheaf `I`
is `f'_*`-acyclic. Represent an object of `D(X_ét)` by a K-injective complex `J` with injective
terms: `Rf_*` is computed by `f_*` on `J`, and `Rf'_*` by `f'_*` on the complex `g'^* J` of
`f'_*`-acyclic sheaves (`Functor.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic_of_map_acyclic`),
so the derived base change map at `J` is the underived one
(`AlgebraicGeometry.Etale.derivedBaseChangeMap_app_fac`). -/
theorem isIso_derivedBaseChangeMap_of_isIso_baseChangeMap (sq : CommSq g' f' f g)
    [IsIso (baseChangeMap A sq)]
    (hF : ∀ M : CochainComplex (Sheaf X'.smallEtaleTopology A) ℤ, M.Acyclic →
      (∀ n, ((f')_*[A]).rightAcyclic (M.X n)) →
        ((((f')_*[A]).mapHomologicalComplex _).obj M).Acyclic)
    (hI : ∀ I : Sheaf X.smallEtaleTopology A, Injective I →
      ((f')_*[A]).rightAcyclic ((g')^*[A].obj I)) :
    IsIso (derivedBaseChangeMap A sq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  let ι := (CochainComplex.toKInjectiveResolution.{u + 1} _).app (Q.objPreimage K)
  let J := (CochainComplex.kInjectiveResolutionFunctor.{u + 1} _).obj (Q.objPreimage K)
  have : IsIso (Q.map ι) := Localization.inverts Q (HomologicalComplex.quasiIso _ _) _
    ((CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} _ _).2)
  rw [← NatTrans.isIso_app_iff_of_iso _ ((quotientCompQhIso _).app J ≪≫ (asIso (Q.map ι)).symm ≪≫
    Q.objObjPreimageIso K)]
  have h₁ : IsIso ((f')_*[A].rightDerivedFunctorUnit.app
      (((g')^*[A].mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj J))) :=
    (f')_*[A].isIso_rightDerivedFunctorUnit_app_of_rightAcyclic_of_map_acyclic hF
      (((g')^*[A].mapHomologicalComplex _).obj J) fun n ↦ hI _ inferInstance
  have h₂ : IsIso ((HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex (baseChangeMap A sq) _).app J)) :=
    have : IsIso ((NatTrans.mapHomologicalComplex (baseChangeMap A sq) _).app J) :=
      ((NatIso.mapHomologicalComplex (asIso (baseChangeMap A sq)) (.up ℤ)).app J).isIso_hom
    inferInstance
  have h : IsIso (L((g)^*[A]).map ((f)_*[A].rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj J)) ≫
      (derivedBaseChangeMap A sq).app (Qh.obj ((HomotopyCategory.quotient _ _).obj J)) ≫
      R((f')_*[A]).map ((g')^*[A].leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj J))) := by
    rw [derivedBaseChangeMap_app_fac]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance
    (@IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h)

end Derived

end Etale

end AlgebraicGeometry
