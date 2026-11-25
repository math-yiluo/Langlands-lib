/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality

/-!
# Transition maps between derived direct images over varying bases

Fix a scheme `B` (the base on which everything is compared) and a scheme `W` (the scheme the
coefficients come from). A *stage* is a morphism `g : T ⟶ S` together with morphisms
`π : B ⟶ S` and `w : T ⟶ W`; to it is attached the functor
`K ↦ π^* Rg_* (w^* K)` from `D⁺(W_ét)` to `D⁺(B_ét)`. A morphism of stages `α ⟶ β` is a
commutative square `(t, s)` from `g_α` to `g_β` compatible with the maps from `B` and to `W`;
it induces the transition map `π_β^* Rg_{β*} w_β^* K ⟶ π_α^* Rg_{α*} w_α^* K`, the pullback
along `π_α` of the derived base-change map of the square, modulo the composition isomorphisms
of the pullbacks. These transition maps compose
(`AlgebraicGeometry.Etale.LimitStage.transition_comp`).

All the comparison maps of the limit arguments of
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.LimitBaseChange` are transition maps of this
kind: the maps between the stages of a limit of morphisms with varying base, the maps to the
limit, and the base-change maps of Cartesian squares.

## Main definitions

- `AlgebraicGeometry.Etale.LimitStage`: a stage.
- `AlgebraicGeometry.Etale.LimitStage.Hom`: a morphism of stages.
- `AlgebraicGeometry.Etale.LimitStage.functor`: the functor `K ↦ π^* Rg_* (w^* K)`.
- `AlgebraicGeometry.Etale.LimitStage.transition`: the transition map of a morphism of stages.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- A *stage* over a base `B` with coefficients from `W`: a morphism `g : T ⟶ S` together with
morphisms `π : B ⟶ S` and `w : T ⟶ W`. -/
structure LimitStage (B W : Scheme.{u}) where
  /-- The source of the morphism. -/
  T : Scheme.{u}
  /-- The target of the morphism. -/
  S : Scheme.{u}
  /-- The morphism. -/
  g : T ⟶ S
  /-- The map from the base. -/
  π : B ⟶ S
  /-- The map to the scheme of coefficients. -/
  w : T ⟶ W

namespace LimitStage

variable {B W : Scheme.{u}}

/-- A morphism of stages `α ⟶ β`: a commutative square from `α.g` to `β.g`, compatible with the
maps from `B` and to `W`. -/
@[ext]
structure Hom (α β : LimitStage B W) where
  /-- The map of sources. -/
  t : α.T ⟶ β.T
  /-- The map of targets. -/
  s : α.S ⟶ β.S
  wg : t ≫ β.g = α.g ≫ s
  wπ : α.π ≫ s = β.π
  ww : t ≫ β.w = α.w

/-- The composite of two morphisms of stages. -/
@[simps]
abbrev Hom.comp {α β γ : LimitStage B W} (φ : Hom α β) (ψ : Hom β γ) : Hom α γ where
  t := φ.t ≫ ψ.t
  s := φ.s ≫ ψ.s
  wg := by rw [Category.assoc, ψ.wg, reassoc_of% φ.wg]
  wπ := by rw [reassoc_of% φ.wπ, ψ.wπ]
  ww := by rw [Category.assoc, ψ.ww, φ.ww]

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The functor `K ↦ π^* Rg_* (w^* K)` attached to a stage. -/
noncomputable abbrev functor (α : LimitStage B W) :
    DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  D+((α.w)^*[ModuleCat.{u + 1} Λ]) ⋙ R+((α.g)_*[ModuleCat.{u + 1} Λ]) ⋙
    D+((α.π)^*[ModuleCat.{u + 1} Λ])

lemma functor_obj (α : LimitStage B W)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (functor Λ α).obj K = D+((α.π)^*[ModuleCat.{u + 1} Λ]).obj
      (R+((α.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((α.w)^*[ModuleCat.{u + 1} Λ]).obj K)) := rfl

/-- The transition map of a morphism of stages `φ : α ⟶ β`, as a natural transformation:
`π_β^* Rg_{β*} w_β^* K ≅ π_α^* s^* Rg_{β*} w_β^* K ⟶ π_α^* Rg_{α*} t^* w_β^* K ≅
π_α^* Rg_{α*} w_α^* K`, the middle map being the pullback along `π_α` of the derived base-change
map of the square `(t, s)`. -/
noncomputable def transition {α β : LimitStage B W} (φ : Hom α β) :
    functor Λ β ⟶ functor Λ α :=
  Functor.whiskerLeft D+((β.w)^*[ModuleCat.{u + 1} Λ])
      (Functor.whiskerLeft R+((β.g)_*[ModuleCat.{u + 1} Λ])
        (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩)
        D+((α.π)^*[ModuleCat.{u + 1} Λ]) ≫
      (Functor.associator _ _ _).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv
      (R+((α.g)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((α.π)^*[ModuleCat.{u + 1} Λ]))

lemma transition_app {α β : LimitStage B W} (φ : Hom α β)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (transition Λ φ).app K =
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom.app
          (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K)) ≫
        D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).app
              (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
            R+((α.g)_*[ModuleCat.{u + 1} Λ]).map
              ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t β.w α.w
                φ.ww.symm).inv.app K)) := by
  simp [transition]

/-- The transition maps compose: the transition map of a composite of morphisms of stages is
the composite of the transition maps. -/
lemma transition_comp {α β γ : LimitStage B W} (φ : Hom α β) (ψ : Hom β γ) :
    transition Λ ψ ≫ transition Λ φ = transition Λ (φ.comp ψ) := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  simp only [NatTrans.comp_app, transition_app]
  have hp := Etale.baseChange_app_paste_horiz_of_eq Λ (⟨ψ.wg⟩ : CommSq ψ.t β.g γ.g ψ.s)
    (⟨φ.wg⟩ : CommSq φ.t α.g β.g φ.s) (⟨(φ.comp ψ).wg⟩ : CommSq (φ.t ≫ ψ.t) α.g γ.g (φ.s ≫ ψ.s))
    rfl rfl (D+((γ.w)^*[ModuleCat.{u + 1} Λ]).obj K)
  -- associativity of the composition isomorphisms on the side of the bases
  have hS := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    α.π φ.s ψ.s β.π (φ.s ≫ ψ.s) γ.π φ.wπ.symm rfl ψ.wπ.symm)
    (R+((γ.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((γ.w)^*[ModuleCat.{u + 1} Λ]).obj K))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hS
  -- associativity of the composition isomorphisms on the side of the coefficients
  have hW := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    φ.t ψ.t γ.w (φ.t ≫ ψ.t) β.w α.w rfl ψ.ww.symm (φ.comp ψ).ww.symm) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hW
  have hW' := congrArg Iso.inv (Iso.ext hW :
    (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).app K ≪≫
      D+((φ.t)^*[ModuleCat.{u + 1} Λ]).mapIso
        ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ψ.t γ.w β.w ψ.ww.symm).app K) =
    (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (φ.t ≫ ψ.t) γ.w α.w
        (φ.comp ψ).ww.symm).app K ≪≫
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t ψ.t (φ.t ≫ ψ.t) rfl).app
        (D+((γ.w)^*[ModuleCat.{u + 1} Λ]).obj K))
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv] at hW'
  rw [hp]
  have n1 := (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom.naturality
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨ψ.wg⟩).app (D+((γ.w)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      R+((β.g)_*[ModuleCat.{u + 1} Λ]).map
        ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ψ.t γ.w β.w ψ.ww.symm).inv.app K))
  have n2 := congrArg D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).naturality
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ψ.t γ.w β.w ψ.ww.symm).inv.app K))
  have n3 := congrArg (fun x ↦ D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
    (R+((α.g)_*[ModuleCat.{u + 1} Λ]).map x)) hW'
  simp only [Functor.comp_map, Functor.map_comp] at n1 n2 n3
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, ← reassoc_of% hS]
  rw [reassoc_of% n2, n3]

/-- The identity morphism of a stage. -/
abbrev Hom.id (α : LimitStage B W) : Hom α α where
  t := 𝟙 _
  s := 𝟙 _
  wg := by simp
  wπ := by simp
  ww := by simp

/-- The transition map of the identity morphism of a stage is the identity. -/
lemma transition_id (α : LimitStage B W) : transition Λ (Hom.id α) = 𝟙 _ := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  have h1 := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_id_right (ModuleCat.{u + 1} Λ)
    α.π) (R+((α.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((α.w)^*[ModuleCat.{u + 1} Λ]).obj K))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at h1
  have h2 := Etale.upperStarCompDerivedPlus_id_left_inv_app (ModuleCat.{u + 1} Λ) α.w K
  have h3 : (Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨(Hom.id α).wg⟩).app
      (D+((α.w)^*[ModuleCat.{u + 1} Λ]).obj K) =
      (upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) α.S).hom.app
          (R+((α.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((α.w)^*[ModuleCat.{u + 1} Λ]).obj K)) ≫
        R+((α.g)_*[ModuleCat.{u + 1} Λ]).map
          ((upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) α.T).inv.app
            (D+((α.w)^*[ModuleCat.{u + 1} Λ]).obj K)) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus, Etale.derivedBaseChangeMapPlus_id]
    simp
  rw [transition_app, h3]
  simp only [Category.assoc, ← Functor.map_comp, h2, CategoryTheory.Functor.map_id,
    NatTrans.id_app]
  refine Eq.trans ?_ h1
  congr 2
  exact Category.comp_id _

end LimitStage

/-- A cofiltered system of stages over `B` with coefficients from `W`, indexed by `I`, together
with a cone of stages over it (the *limit stage* `pt`). -/
structure LimitStageSystem (B W : Scheme.{u}) (I : Type u) [Category.{u} I] where
  /-- The stages. -/
  obj : I → LimitStage B W
  /-- The transition morphisms. -/
  map : ∀ {i j : I}, (i ⟶ j) → LimitStage.Hom (obj i) (obj j)
  map_id : ∀ i, map (𝟙 i) = LimitStage.Hom.id (obj i)
  map_comp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), map (f ≫ g) = (map f).comp (map g)
  /-- The limit stage. -/
  pt : LimitStage B W
  /-- The projections from the limit stage. -/
  π : ∀ i, LimitStage.Hom pt (obj i)
  w : ∀ {i j : I} (f : i ⟶ j), (π i).comp (map f) = π j

namespace LimitStageSystem

variable {B W : Scheme.{u}} {I : Type u} [Category.{u} I] (Λ : Type (u + 1)) [CommRing Λ]
  (𝒮 : LimitStageSystem B W I)
  (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ)

/-- The diagram `i ↦ H^q(π_i^* Rg_{i*} w_i^* K)` of sheaves on `B`. -/
@[simps]
noncomputable def diagram : Iᵒᵖ ⥤ Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj i := (DerivedCategory.Plus.homologyFunctor _ q).obj
    ((LimitStage.functor Λ (𝒮.obj i.unop)).obj K)
  map f := (DerivedCategory.Plus.homologyFunctor _ q).map
    ((LimitStage.transition Λ (𝒮.map f.unop)).app K)
  map_id i := by
    rw [unop_id, 𝒮.map_id, LimitStage.transition_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
  map_comp f g := by
    rw [← Functor.map_comp, ← NatTrans.comp_app, LimitStage.transition_comp, unop_comp,
      𝒮.map_comp]

/-- The cocone `H^q(π_i^* Rg_{i*} w_i^* K) ⟶ H^q(π^* Rg_* w^* K)` over
`AlgebraicGeometry.Etale.LimitStageSystem.diagram`. -/
@[simps]
noncomputable def cocone : Cocone (𝒮.diagram Λ K q) where
  pt := (DerivedCategory.Plus.homologyFunctor _ q).obj ((LimitStage.functor Λ 𝒮.pt).obj K)
  ι :=
    { app i := (DerivedCategory.Plus.homologyFunctor _ q).map
        ((LimitStage.transition Λ (𝒮.π i.unop)).app K)
      naturality i j f := by
        simp only [diagram_map, Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id, ← Functor.map_comp, ← NatTrans.comp_app, LimitStage.transition_comp,
          𝒮.w] }

end LimitStageSystem

end AlgebraicGeometry.Etale
