/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.PushforwardZero

/-!
# Transition maps of stages in degree zero, at a sheaf

For a stage `α = (T, S, g, π, w)` and a sheaf `G` on `W`, `H⁰(π^* Rg_* w^*(G[0]))` is
identified with `π^* g_* w^* G` (`AlgebraicGeometry.Etale.LimitStage.homologyZeroIso`), and
under these identifications `H⁰` of the transition map of a morphism of stages is the underived
transition map `AlgebraicGeometry.Etale.LimitStage.sheafTransition`
(`AlgebraicGeometry.Etale.LimitStage.homology_map_transition_homologyZeroIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A sheaf placed in degree `0`, as a bounded below cochain complex. -/
noncomputable abbrev singleComplex {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    CochainComplex.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨(HomologicalComplex.single _ (.up ℤ) 0).obj G, 0, inferInstance⟩

/-- `G[0] ≅ Q(G placed in degree 0)` in the bounded below derived category. -/
noncomputable def singleFunctorIsoQObj {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj G ≅
      DerivedCategory.Plus.Q.obj (singleComplex Λ G) :=
  DerivedCategory.Plus.ι.preimageIso (X := (DerivedCategory.Plus.singleFunctor _ 0).obj G)
    (Y := DerivedCategory.Plus.Q.obj (singleComplex Λ G))
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app G)

namespace LimitStage

variable {B W : Scheme.{u}}

/-- `H⁰` of the comparison map `AlgebraicGeometry.Etale.LimitStage.homotopyUnit` at a sheaf
placed in degree `0` is an isomorphism. -/
instance isIso_homology_homotopyUnit (α : LimitStage B W)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (homotopyUnit Λ α ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G)))) := by
  -- the pullback of the single complex is the single complex of the pullback
  let ψ : (HomotopyCategory.Plus.quotient _).obj
        (singleComplex Λ (((α.w)^*[ModuleCat.{u + 1} Λ]).obj G)) ≅
      ((α.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G)) :=
    (HomotopyCategory.Plus.quotient _).mapIso (ObjectProperty.isoMk _
      (X := singleComplex Λ (((α.w)^*[ModuleCat.{u + 1} Λ]).obj G))
      (Y := ((α.w)^*[ModuleCat.{u + 1} Λ]).mapCochainComplexPlus.obj (singleComplex Λ G))
      ((HomologicalComplex.singleMapHomologicalComplex ((α.w)^*[ModuleCat.{u + 1} Λ])
        (.up ℤ) 0).app G).symm)
  have hu := Functor.isIso_homologyFunctor_zero_map_rightDerivedFunctorPlusUnit_app
    ((α.g)_*[ModuleCat.{u + 1} Λ]) (((α.w)^*[ModuleCat.{u + 1} Λ]).obj G)
  have hc : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (((α.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.app
        (((α.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G))))) := by
    have hN := congrArg (DerivedCategory.Plus.homologyFunctor _ 0).map
      (((α.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.naturality ψ.hom)
    simp only [Functor.comp_map, Functor.map_comp] at hN
    exact IsIso.of_isIso_fac_left hN
  have hz : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (((α.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.app
          (((α.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G))) ≫
        R+((α.g)_*[ModuleCat.{u + 1} Λ]).map
          (((α.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.app
            ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G))))) := by
    rw [Functor.map_comp]
    infer_instance
  have ha : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
        (((α.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.app
            (((α.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
              ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G))) ≫
          R+((α.g)_*[ModuleCat.{u + 1} Λ]).map
            (((α.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.app
              ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G)))))) := by
    have hN := (((α.π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
      0).hom.naturality
      (((α.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.app
          (((α.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G))) ≫
        R+((α.g)_*[ModuleCat.{u + 1} Λ]).map
          (((α.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.app
            ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G))))
    simp only [Functor.comp_map] at hN
    rw [← IsIso.inv_comp_eq] at hN
    rw [← hN]
    infer_instance
  rw [homotopyUnit, Functor.map_comp]
  infer_instance

/-- **`H⁰` of a stage at a sheaf in degree `0`**: `H⁰(π^* Rg_* w^*(G[0])) ≅ π^* g_* w^* G`. -/
noncomputable def homologyZeroIso (α : LimitStage B W)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((functor Λ α).obj (DerivedCategory.Plus.Q.obj (singleComplex Λ G))) ≅
      (sheafFunctor Λ α).obj G :=
  (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((functor Λ α).mapIso
        ((DerivedCategory.Plus.quotientCompQhIso _).app (singleComplex Λ G)).symm) ≪≫
    (asIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (homotopyUnit Λ α ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G))))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((DerivedCategory.Plus.quotientCompQhIso _).app
        (((sheafFunctor Λ α).mapCochainComplexPlus).obj (singleComplex Λ G))) ≪≫
    DerivedCategory.Plus.homologyFunctorObjQIso
      (((sheafFunctor Λ α).mapCochainComplexPlus).obj (singleComplex Λ G)) 0 ≪≫
    singleHomologyZeroIso (sheafFunctor Λ α) G

/-- On single complexes, the levelwise underived transition map is induced by the underived
transition map of sheaves. -/
lemma homotopyTransition_quotient {α β : LimitStage B W} (φ : Hom α β)
    (K : CochainComplex.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    homotopyTransition Λ φ ((HomotopyCategory.Plus.quotient _).obj K) =
      (HomotopyCategory.Plus.quotient _).map
        (ObjectProperty.homMk (X := ((sheafFunctor Λ β).mapCochainComplexPlus).obj K)
          (Y := ((sheafFunctor Λ α).mapCochainComplexPlus).obj K)
          ((NatTrans.mapHomologicalComplex (sheafTransition Λ φ) (.up ℤ)).app K.obj)) := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  rfl

/-- **`H⁰` of the transition maps of stages**: under the identifications
`AlgebraicGeometry.Etale.LimitStage.homologyZeroIso`, `H⁰` of the transition map of a morphism
of stages at a sheaf placed in degree `0` is the underived transition map. -/
lemma homology_map_transition_homologyZeroIso {α β : LimitStage B W} (φ : Hom α β)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.Plus.homologyFunctor _ 0).map
        ((transition Λ φ).app (DerivedCategory.Plus.Q.obj (singleComplex Λ G))) ≫
      (homologyZeroIso Λ α G).hom =
      (homologyZeroIso Λ β G).hom ≫ (sheafTransition Λ φ).app G := by
  have key := congrArg (DerivedCategory.Plus.homologyFunctor _ 0).map
    (homotopyUnit_comp_transition Λ φ ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G)))
  rw [Functor.map_comp, Functor.map_comp, homotopyTransition_quotient] at key
  have hn := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
    (ObjectProperty.homMk (X := ((sheafFunctor Λ β).mapCochainComplexPlus).obj (singleComplex Λ G))
      (Y := ((sheafFunctor Λ α).mapCochainComplexPlus).obj (singleComplex Λ G))
      ((NatTrans.mapHomologicalComplex (sheafTransition Λ φ) (.up ℤ)).app
        (singleComplex Λ G).obj)) 0
  have hr := homologyMap_mapHomologicalComplex_single_singleHomologyZeroIso _ _
    (sheafTransition Λ φ) G
  have ht := congrArg (DerivedCategory.Plus.homologyFunctor _ 0).map
    ((transition Λ φ).naturality
      ((DerivedCategory.Plus.quotientCompQhIso _).inv.app (singleComplex Λ G)))
  have hq := congrArg (DerivedCategory.Plus.homologyFunctor _ 0).map
    ((DerivedCategory.Plus.quotientCompQhIso _).hom.naturality
      (ObjectProperty.homMk
        (X := ((sheafFunctor Λ β).mapCochainComplexPlus).obj (singleComplex Λ G))
        (Y := ((sheafFunctor Λ α).mapCochainComplexPlus).obj (singleComplex Λ G))
        ((NatTrans.mapHomologicalComplex (sheafTransition Λ φ) (.up ℤ)).app
          (singleComplex Λ G).obj)))
  simp only [Functor.comp_map, Functor.map_comp] at ht hq
  simp only [homologyZeroIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, asIso_inv, Category.assoc]
  erw [← reassoc_of% ht]
  congr 1
  rw [← cancel_epi ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (homotopyUnit Λ β ((HomotopyCategory.Plus.quotient _).obj (singleComplex Λ G)))),
    IsIso.hom_inv_id_assoc]
  erw [reassoc_of% key]
  rw [IsIso.hom_inv_id_assoc]
  erw [reassoc_of% hq]
  erw [reassoc_of% hn]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) hr)


/-- The underived transition maps compose. -/
lemma sheafTransition_comp_app {α β γ : LimitStage B W} (φ : Hom α β) (ψ : Hom β γ)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sheafTransition Λ ψ).app G ≫ (sheafTransition Λ φ).app G =
      (sheafTransition Λ (φ.comp ψ)).app G := by
  rw [← cancel_epi (homologyZeroIso Λ γ G).hom,
    ← reassoc_of% (homology_map_transition_homologyZeroIso Λ ψ G),
    ← homology_map_transition_homologyZeroIso Λ φ G,
    ← homology_map_transition_homologyZeroIso Λ (φ.comp ψ) G, ← Functor.map_comp_assoc,
    ← NatTrans.comp_app, transition_comp]
end LimitStage

end AlgebraicGeometry.Etale
