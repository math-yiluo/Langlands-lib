/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.HomSheafAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars

/-!
# Restriction of scalars commutes with the derived direct image

Let `φ : Λ →+* Λ'` be a morphism of commutative rings and `f : X ⟶ Y` a morphism of schemes.
Restriction of scalars along `φ` is exact and commutes with the direct image `f_*` (both are
computed objectwise). It also commutes with the derived direct image on `D⁺`:
`R⁺f_* ∘ res ≅ res ∘ R⁺f_*` (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`).
The non-formal input is that an injective sheaf `J` of `Λ'`-modules is `f_*`-acyclic as a sheaf of
`Λ`-modules (`AlgebraicGeometry.Etale.rightAcyclic_lowerStar_restrictScalars_obj`): embedding `J`
into an injective sheaf `I` of `Λ`-modules, `J` is a direct summand of the coextension
`Hom_Λ(Λ', I)`, whose restriction of scalars is the sheaf `Hom_Λ(Λ', I)` of homomorphisms out of
the `Λ`-module `Λ'`, which is acyclic for `f_*`
(`CategoryTheory.Sheaf.rightAcyclic_homSheaf_obj`).

This is the commutation of restriction of scalars with `Rf_*` used for the change of coefficients
in the proof of the proper base change theorem (blueprint
`proposition-proper-base-change-etale-site--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- The coextension of scalars of a `Λ`-module `N` along `φ : Λ →+* Λ'`, viewed again as a
`Λ`-module, is the module `Hom_Λ(Λ', N)` of homomorphisms out of the `Λ`-module `Λ'`. -/
noncomputable def coextendScalarsCompRestrictScalarsIso :
    ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ ⋙ ModuleCat.restrictScalars.{u + 1} φ ≅
      Sheaf.homFunctor Λ ((ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of Λ' Λ')) :=
  NatIso.ofComponents (fun N ↦ LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars.{u + 1} φ).obj ((ModuleCat.coextendScalars φ).obj N))
    { toFun := fun g ↦ ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of Λ' Λ')) (Y := N) g
      invFun := fun g ↦ g.hom
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r g ↦ by
        refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
        let g' : (ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of Λ' Λ') →ₗ[Λ] N := g
        change g' ((show Λ' from s) * φ r) = r • g' s
        rw [mul_comm, ← map_smul]
        rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) (fun _ ↦ rfl)

/-- The restriction of scalars of the coextension `Hom_Λ(Λ', I)` of an étale sheaf `I` of
`Λ`-modules is the sheaf `Hom_Λ(Λ', I)` of homomorphisms out of the `Λ`-module `Λ'`. -/
noncomputable def restrictScalarsCoextendScalarsObjIso {X : Scheme.{u}}
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).obj ((coextendScalars φ X).obj I) ≅
      (Sheaf.homSheaf X.smallEtaleTopology
        ((ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of Λ' Λ'))).obj I where
  hom := (sheafCompose_map _ (coextendScalarsCompRestrictScalarsIso φ).hom).app I
  inv := (sheafCompose_map _ (coextendScalarsCompRestrictScalarsIso φ).inv).app I
  hom_inv_id := by
    ext U : 3
    exact congr_app (coextendScalarsCompRestrictScalarsIso φ).hom_inv_id _
  inv_hom_id := by
    ext U : 3
    exact congr_app (coextendScalarsCompRestrictScalarsIso φ).inv_hom_id _

/-- Restriction of scalars of étale sheaves is faithful: it is computed sectionwise. -/
instance (X : Scheme.{u}) : (Sheaf.restrictScalars X.smallEtaleTopology φ).Faithful where
  map_injective {A B} a b h := by
    ext U : 3
    exact (ModuleCat.restrictScalars.{u + 1} φ).map_injective
      (congr_app (congrArg (fun a ↦ a.hom) h) U)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The direct image of étale sheaves of `Λ`-modules sends morphisms which are surjective on
sections to epimorphisms: it is computed objectwise. -/
lemma epi_lowerStar_map_of_surjective {A B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (p : A ⟶ B) (hp : ∀ U, Function.Surjective (p.hom.app U)) :
    Epi ((f)_*[ModuleCat.{u + 1} Λ].map p) := by
  have : Sheaf.IsLocallySurjective ((f)_*[ModuleCat.{u + 1} Λ].map p) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun U ↦ hp _
  exact Sheaf.epi_of_isLocallySurjective _

/-- **Injective sheaves of `Λ'`-modules are `f_*`-acyclic as sheaves of `Λ`-modules.** -/
theorem rightAcyclic_lowerStar_restrictScalars_obj
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) [Injective J] :
    ((f)_*[ModuleCat.{u + 1} Λ]).rightAcyclic
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj J) := by
  let res := Sheaf.restrictScalars X.smallEtaleTopology φ
  let adj := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ
  let I := Injective.under (res.obj J)
  -- `J` is a direct summand of `Hom_Λ(Λ', I)`
  let j : J ⟶ (coextendScalars φ X).obj I := adj.homEquiv _ _ (Injective.ι (res.obj J))
  have h : res.map j ≫ adj.counit.app I = Injective.ι (res.obj J) := by
    exact (adj.homEquiv_counit (g := j)).symm.trans ((adj.homEquiv _ _).symm_apply_apply _)
  have : Mono (res.map j) := mono_of_mono_fac h
  have : Mono j := res.mono_of_mono_map this
  let r : (coextendScalars φ X).obj I ⟶ J := Injective.factorThru (𝟙 J) j
  have hjr : res.map j ≫ res.map r = 𝟙 _ := by
    rw [← res.map_comp, Injective.comp_factorThru, res.map_id]
  have hI : ((f)_*[ModuleCat.{u + 1} Λ]).rightAcyclic (res.obj ((coextendScalars φ X).obj I)) :=
    ((f)_*[ModuleCat.{u + 1} Λ]).rightAcyclic.prop_of_iso
      (restrictScalarsCoextendScalarsObjIso φ I).symm
      (Sheaf.rightAcyclic_homSheaf_obj _ (epi_lowerStar_map_of_surjective f) I
        (fun U ↦ Sheaf.baer_obj_of_injective.{u + 1} I U.unop) _)
  intro q
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, ← hjr,
    CategoryTheory.Functor.map_comp,
    (hI q).eq_of_tgt (((f)_*[ModuleCat.{u + 1} Λ].rightDerived (q + 1)).map (res.map j)) 0,
    Limits.zero_comp]

/-- Restriction of scalars commutes with the direct image, both being computed objectwise. -/
noncomputable def lowerStarCompRestrictScalarsIso :
    (f)_*[ModuleCat.{u + 1} Λ'] ⋙ Sheaf.restrictScalars Y.smallEtaleTopology φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙ (f)_*[ModuleCat.{u + 1} Λ] :=
  Iso.refl _

/-- The comparison `res(R⁺f_* K) ⟶ R⁺f_*(res K)` between restriction of scalars along
`φ : Λ →+* Λ'` and the derived direct image on `D⁺`: the base change morphism of the
identification `f_* ∘ res = res ∘ f_*`. It is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`). -/
noncomputable def rightDerivedLowerStarRestrictScalars :
    ((f)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlus ⋙
        (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (lowerStarCompRestrictScalarsIso φ f).hom

/-- **Restriction of scalars commutes with the derived direct image**: the comparison
`res(R⁺f_* K) ⟶ R⁺f_*(res K)` is an isomorphism, since restriction of scalars sends injective
sheaves of `Λ'`-modules to `f_*`-acyclic sheaves of `Λ`-modules
(`AlgebraicGeometry.Etale.rightAcyclic_lowerStar_restrictScalars_obj`). -/
instance isIso_rightDerivedLowerStarRestrictScalars :
    IsIso (rightDerivedLowerStarRestrictScalars φ f) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun I _ ↦ rightAcyclic_lowerStar_restrictScalars_obj φ f I

end Etale

end AlgebraicGeometry
