/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import WeilConjectures.SixFunctors.BaseChange.DerivedRestrictScalars
public import WeilConjectures.SixFunctors.BaseChange.Forget
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Abelian sheaves as sheaves of `ULift ℤ`-modules and the derived base change map

The forgetful functor `ModuleCat (ULift ℤ) ⥤ Ab` is an equivalence, hence so is the functor
`forget₂ : Sheaf X_ét (ModuleCat (ULift ℤ)) ⥤ Sheaf X_ét Ab` taking underlying abelian sheaves
(`AlgebraicGeometry.Etale.isEquivalence_sheafCompose_forget₂_uliftInt`). It commutes with the
pushforwards on the nose and with the pullbacks up to the isomorphisms
`AlgebraicGeometry.Etale.upperStarForget₂Comparison`, and it sends injective sheaves to
injective sheaves. Consequently it commutes with the derived pushforwards on `D⁺`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarForget₂`), and the derived base change map
for abelian sheaves at `forget₂ K` is an isomorphism if and only if the derived base change map
for sheaves of `ULift ℤ`-modules is one at `K`
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_forget₂_iff`). Every object of
`D⁺(X_ét, Ab)` is of the form `forget₂ K` up to isomorphism
(`AlgebraicGeometry.Etale.exists_forget₂_mapDerivedCategoryPlus_obj_iso`).

This is how the proper base change theorem for abelian sheaves is deduced from the one for
sheaves of modules over a coefficient ring.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The functor taking the underlying abelian sheaf of an étale sheaf of `ULift ℤ`-modules. -/
local notation "Φ" X:max => sheafCompose (Scheme.smallEtaleTopology X)
  (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})

section Equivalence

variable (X : Scheme.{u})

instance : (Φ X).Faithful where
  map_injective {A B} a b h := by
    ext U : 3
    exact (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}).map_injective
      (congr_app (congrArg (fun a ↦ a.hom) h) U)

instance : (Φ X).Full where
  map_surjective {A B} a :=
    ⟨⟨{ app U := (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}).preimage
          (a.hom.app U)
        naturality U V i := (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          AddCommGrpCat.{u + 1}).map_injective (by
            rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
            exact a.hom.naturality i) }⟩, by
      ext U : 3
      exact (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}).map_preimage _⟩

instance : (Φ X).EssSurj where
  mem_essImage G := by
    let F₀ := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
    let ε := F₀.asEquivalence.counitIso
    exact ⟨(sheafCompose _ F₀.inv).obj G,
      ⟨{ hom := (sheafCompose_map _ ε.hom).app G
         inv := (sheafCompose_map _ ε.inv).app G
         hom_inv_id := by
           rw [← NatTrans.comp_app, ← sheafCompose_comp, ε.hom_inv_id]
           rfl
         inv_hom_id := by
           rw [← NatTrans.comp_app, ← sheafCompose_comp, ε.inv_hom_id]
           rfl }⟩⟩

/-- Taking the underlying abelian sheaf is an equivalence from étale sheaves of
`ULift ℤ`-modules to abelian étale sheaves. -/
instance isEquivalence_sheafCompose_forget₂_uliftInt : (Φ X).IsEquivalence where

end Equivalence

section Pullback

variable (Λ : Type (u + 1)) [CommRing Λ] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- Taking underlying abelian sheaves commutes with the direct image, both being computed
objectwise. -/
noncomputable def lowerStarCompForget₂Iso :
    (g)_*[ModuleCat.{u + 1} Λ] ⋙
        sheafCompose Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      sheafCompose Z.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
        (g)_*[AddCommGrpCat.{u + 1}] :=
  Iso.refl _

/-- The comparison `g^*(forget₂ G) ⟶ forget₂ (g^* G)` between the pullback along `g` and the
underlying abelian sheaf, as a natural transformation: the mate, along the adjunctions
`g^* ⊣ g_*`, of the equality `g_* ∘ forget₂ = forget₂ ∘ g_*`. Its components are the
isomorphisms `AlgebraicGeometry.Etale.upperStarForget₂Comparison`
(`AlgebraicGeometry.Etale.upperStarForget₂_natTrans_app`). -/
noncomputable def upperStarForget₂ :
    TwoSquare (sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) (g)^*[ModuleCat.{u + 1} Λ]
      (g)^*[AddCommGrpCat.{u + 1}]
      (sheafCompose Z.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) :=
  (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)).symm
      (TwoSquare.mk _ _ _ _ (lowerStarCompForget₂Iso Λ g).hom)

lemma upperStarForget₂_natTrans_app (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarForget₂ Λ g).app G = upperStarForget₂Comparison Λ g G := by
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    unit_comp_lowerStar_map_upperStarForget₂Comparison]
  have := unit_mateEquiv_symm (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)
    (TwoSquare.mk _ _ _ _ (lowerStarCompForget₂Iso Λ g).hom) G
  exact this.symm.trans (Category.comp_id _)

instance isIso_upperStarForget₂ : IsIso (upperStarForget₂ Λ g) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro G
  rw [upperStarForget₂_natTrans_app]
  infer_instance

end Pullback

section BaseChange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Taking underlying abelian sheaves commutes with the derived categories' reflection of
isomorphisms: a morphism of `D⁺(X_ét, ULift ℤ)` is an isomorphism if and only if its image in
`D⁺(X_ét, Ab)` is one. -/
lemma isIso_forget₂_mapDerivedCategoryPlus_map_iff {X : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))} (a : K ⟶ L) :
    IsIso ((Φ X).mapDerivedCategoryPlus.map a) ↔ IsIso a := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [DerivedCategory.Plus.isIso_iff] at h ⊢
  intro n
  have := h n
  have : IsIso ((Φ X).map ((DerivedCategory.Plus.homologyFunctor _ n).map a)) :=
    (NatIso.isIso_map_iff ((Φ X).mapDerivedCategoryPlusHomologyFunctorIso n) a).2 this
  exact isIso_of_reflects_iso _ (Φ X)

/-- Every object of `D⁺(X_ét, Ab)` is, up to isomorphism, the underlying complex of abelian
sheaves of an object of `D⁺(X_ét, ULift ℤ)`. -/
lemma exists_forget₂_mapDerivedCategoryPlus_obj_iso {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    ∃ K' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))),
      Nonempty ((Φ X).mapDerivedCategoryPlus.obj K' ≅ K) := by
  let E := (Φ X).asEquivalence
  have : E.functor.Additive := inferInstanceAs (Φ X).Additive
  exact ⟨E.inverse.mapDerivedCategoryPlus.obj K,
    ⟨((Functor.mapDerivedCategoryPlusCompIso E.inverse E.functor).app K).symm ≪≫
      (Functor.mapDerivedCategoryPlusNatIso E.counitIso).app K ≪≫
      (Functor.mapDerivedCategoryPlusIdIso _).app K⟩⟩

/-- The comparison `forget₂ (R⁺f_* K) ⟶ R⁺f_*(forget₂ K)` between taking underlying abelian
sheaves and the derived direct image on `D⁺`. It is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarForget₂`). -/
noncomputable def rightDerivedLowerStarForget₂ (f : X ⟶ Y) :
    ((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)]).rightDerivedFunctorPlus ⋙
        (Φ Y).mapDerivedCategoryPlus ⟶
      (Φ X).mapDerivedCategoryPlus ⋙ ((f)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (lowerStarCompForget₂Iso (ULift.{u + 1} ℤ) f).hom

/-- **Taking underlying abelian sheaves commutes with the derived direct image**, since it sends
injective sheaves to injective sheaves. -/
instance isIso_rightDerivedLowerStarForget₂ (f : X ⟶ Y) :
    IsIso (rightDerivedLowerStarForget₂ f) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun _ _ ↦ Functor.rightAcyclic_of_injective _

/-- The underlying abelian sheaves of the unit `f_* M ⟶ R⁺f_* M`, followed by the comparison
`forget₂ (R⁺f_* M) ≅ R⁺f_*(forget₂ M)`, is the unit at `forget₂ M`. -/
lemma forget₂_map_rightDerivedFunctorPlusUnit_app (f : X ⟶ Y)
    (M : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) :
    (Φ Y).mapDerivedCategoryPlus.map
        (((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)]).rightDerivedFunctorPlusUnith.app M) ≫
      (rightDerivedLowerStarForget₂ f).app (DerivedCategory.Plus.Qh.obj M) =
    (Φ Y).mapDerivedCategoryPlusFactorsh.hom.app
        (((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)]).mapHomotopyCategoryPlus.obj M) ≫
      ((f)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlusUnith.app
        ((Φ X).mapHomotopyCategoryPlus.obj M) ≫
      ((f)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.map
        ((Φ X).mapDerivedCategoryPlusFactorsh.inv.app M) := by
  have := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (lowerStarCompForget₂Iso (ULift.{u + 1} ℤ) f).hom) M
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, lowerStarCompForget₂Iso,
    Iso.refl_hom, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id] at this
  refine this.trans ?_
  erw [Category.id_comp, Category.id_comp, Category.id_comp]

/-- The compatibility of the base change maps with taking underlying abelian sheaves
(`AlgebraicGeometry.Etale.upperStarForget₂Comparison_comp_map_baseChangeMap_app`), applied
degreewise to a bounded below complex. -/
lemma mapHomotopyCategoryPlus_baseChangeMap_forget₂ (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) :
    (NatTrans.mapHomotopyCategoryPlus (baseChangeMap AddCommGrpCat.{u + 1} sq)).app
        ((Φ X).mapHomotopyCategoryPlus.obj K) ≫
      ((f')_*[AddCommGrpCat.{u + 1}]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus
          (upperStarForget₂ (ULift.{u + 1} ℤ) g')).app K) =
    (NatTrans.mapHomotopyCategoryPlus (upperStarForget₂ (ULift.{u + 1} ℤ) g)).app
        (((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)]).mapHomotopyCategoryPlus.obj K) ≫
      (Φ Y').mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus
          (baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) sq)).app K) := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app_comp_map_mapHomotopyCategoryPlus_app,
    NatTrans.ι_map_mapHomotopyCategoryPlus_app_comp_map_mapHomotopyCategoryPlus_app]
  congr 1
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, upperStarForget₂_natTrans_app]
  exact (upperStarForget₂Comparison_comp_map_baseChangeMap_app _ sq (K.obj.as.X n)).symm

/-- The underived part `g^* f_* K ⟶ f'_* g'^* K ⟶ R⁺f'_*(g'^* K)` of the derived base change
map for abelian sheaves at `forget₂ K` is an isomorphism if and only if the one for sheaves of
`ULift ℤ`-modules at `K` is one. -/
lemma isIso_comp_rightDerivedFunctorPlusUnit_forget₂_iff (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) :
    IsIso (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (baseChangeMap AddCommGrpCat.{u + 1} sq)).app
          ((Φ X).mapHomotopyCategoryPlus.obj K)) ≫
        (f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlusUnith.app
          (((g')^*[AddCommGrpCat.{u + 1}]).mapHomotopyCategoryPlus.obj
            ((Φ X).mapHomotopyCategoryPlus.obj K))) ↔
      IsIso (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) sq)).app K) ≫
        (f')_*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)].rightDerivedFunctorPlusUnith.app
          (((g')^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)]).mapHomotopyCategoryPlus.obj K)) := by
  have h₁ := (Φ Y').mapDerivedCategoryPlusFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategoryPlus
      (baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) sq)).app K)
  have h₃ := ((f')_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlusUnith.naturality
    ((NatTrans.mapHomotopyCategoryPlus (upperStarForget₂ (ULift.{u + 1} ℤ) g')).app K)
  exact isIso_map_comp_iff_of_reflectsIsomorphisms _ isIso_forget₂_mapDerivedCategoryPlus_map_iff
    _ _ _ _ _ _ _ _ _ (forget₂_map_rightDerivedFunctorPlusUnit_app f' _) _ _ h₁ _ _
    (mapHomotopyCategoryPlus_baseChangeMap_forget₂ sq K) _ h₃

/-- **The derived base change map and underlying abelian sheaves.** For a commutative square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
and `K ∈ D⁺(X_ét, ULift ℤ)`, the derived base change map for abelian sheaves is an isomorphism
at the underlying complex of abelian sheaves of `K` if and only if the derived base change map
for sheaves of `ULift ℤ`-modules is an isomorphism at `K`. -/
theorem isIso_derivedBaseChangeMapPlus_app_forget₂_iff (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
        ((Φ X).mapDerivedCategoryPlus.obj K)) ↔
      IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) sq).app K) :=
  isIso_derivedBaseChangeMapPlus_app_mapDerivedCategoryPlus_iff _ sq
    (fun _ _ ↦ Functor.rightAcyclic_of_injective _)
    (isIso_comp_rightDerivedFunctorPlusUnit_forget₂_iff sq) K

end BaseChange

end Etale

end AlgebraicGeometry
