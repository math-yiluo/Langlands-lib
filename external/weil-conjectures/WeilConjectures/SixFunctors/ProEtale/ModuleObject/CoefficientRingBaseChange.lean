/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientRingSections

/-!
# Base change of the coefficient sheaves on weakly contractible objects

Let `f : X ⟶ Y` be a morphism of schemes, `k_Y : Y ⟶ Spec ℤ` and `Λ` a condensed abelian group.
The morphism `η : k_Y^* p^* Λ ⟶ f_* (f ≫ k_Y)^* p^* Λ` adjoint to the composition isomorphism of
the pullbacks (`AlgebraicGeometry.ProEtale.unitCompUpperStarCompInv`) is, on sections over an
object `V` of `Y_proét` whose sections of the coefficient sheaves are computed by `π₀`
(`AlgebraicGeometry.ProEtale.bijective_unit_app_comp_map_unit`), the map
`Λ(π₀ V) ⟶ Λ(π₀(X ×_Y V))` induced by the projection `X ×_Y V ⟶ V`
(`AlgebraicGeometry.ProEtale.map_unit_comp_unitCompUpperStarCompInv_app`). Hence it is bijective
as soon as `π₀(X ×_Y V) ⟶ π₀(V)` is a homeomorphism, i.e. as soon as morphisms `V ⟶ Spec LC(S, ℤ)`
and `X ×_Y V ⟶ Spec LC(S, ℤ)` correspond
(`AlgebraicGeometry.ProEtale.bijective_unitCompUpperStarCompInv_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

section Compat

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) {X Y : Scheme.{u}} (f : X ⟶ Y)
  (kY : Y ⟶ specZ.{u})

/-- The comparison `X ×_Y Y[S] ≅ X[S]` of profinite test objects, as a morphism of `X_proét`. -/
noncomputable abbrev profiniteToProEtAlongPullbackHom (S : Profinite.{u}) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj ((profiniteToProEtAlong kY).obj S) ⟶
      (profiniteToProEtAlong (f ≫ kY)).obj S :=
  (MorphismProperty.Over.pullbackComp f kY).inv.app (profiniteToProEt.obj S)

/-- The morphism `η : k_Y^* p^* Λ ⟶ f_* (f ≫ k_Y)^* p^* Λ` adjoint to the composition isomorphism
of the pullbacks. -/
noncomputable abbrev unitCompUpperStarCompInv :
    (kY)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ) ⟶
      (f)_*[Ab.{u + 1}].obj ((f ≫ kY)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)) :=
  (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app
      ((kY)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)) ≫
    (f)_*[Ab.{u + 1}].map ((ProEtale.upperStarComp Ab.{u + 1} f kY).inv.app (pointUpperStar.obj Λ))

lemma unit_app_comp_unitCompUpperStarCompInv_app (T : Profinite.{u}) :
    ((upperStarFromPointAlongAdjunction kY).unit.app Λ).hom.app (op T) ≫
      (unitCompUpperStarCompInv Λ f kY).hom.app (op ((profiniteToProEtAlong kY).obj T)) =
    ((upperStarFromPointAlongAdjunction (f ≫ kY)).unit.app Λ).hom.app (op T) ≫
      ((f ≫ kY)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)).obj.map
        (profiniteToProEtAlongPullbackHom f kY T).op := by
  have h := congrArg (fun φ ↦ φ.hom.app (op (profiniteToProEt.obj T)))
    (ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp' Ab.{u + 1} f kY
      (pointUpperStar.obj Λ))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  simp only [upperStarFromPointAlongAdjunction, Adjunction.comp_unit_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
  erw [h]
  rfl


variable (V : Y.ProEt)

/-- The map `π₀(X ×_Y V) ⟶ π₀(V)` on the spaces of connected components induced by the projection
`X ×_Y V ⟶ V`, defined through the adjunctions `π₀ ⊣ (S ↦ X[S])` and `π₀ ⊣ (S ↦ Y[S])`. -/
noncomputable def connectedComponentsAlongPullbackHom :
    (connectedComponentsAlong (f ≫ kY)).obj
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V) ⟶
      (connectedComponentsAlong kY).obj V :=
  ((connectedComponentsAlongAdjunction (f ≫ kY)).homEquiv _ _).symm
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
      ((connectedComponentsAlongAdjunction kY).unit.app V) ≫
      profiniteToProEtAlongPullbackHom f kY _)

lemma map_unit_comp_connectedComponentsAlongPullbackHom :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
        ((connectedComponentsAlongAdjunction kY).unit.app V) ≫
      profiniteToProEtAlongPullbackHom f kY _ =
    (connectedComponentsAlongAdjunction (f ≫ kY)).unit.app _ ≫
      (profiniteToProEtAlong (f ≫ kY)).map (connectedComponentsAlongPullbackHom f kY V) := by
  exact (Equiv.apply_symm_apply _ _).symm.trans
    ((connectedComponentsAlongAdjunction (f ≫ kY)).homEquiv_unit _ _ _)

lemma map_unit_comp_unitCompUpperStarCompInv_app :
    (((upperStarFromPointAlongAdjunction kY).unit.app Λ).hom.app
        (op ((connectedComponentsAlong kY).obj V)) ≫
      ((pointUpperStar ⋙ (kY)^*[Ab.{u + 1}]).obj Λ).obj.map
        ((connectedComponentsAlongAdjunction kY).unit.app V).op) ≫
      (unitCompUpperStarCompInv Λ f kY).hom.app (op V) =
    Λ.obj.map (connectedComponentsAlongPullbackHom f kY V).op ≫
      ((upperStarFromPointAlongAdjunction (f ≫ kY)).unit.app Λ).hom.app
        (op ((connectedComponentsAlong (f ≫ kY)).obj
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V))) ≫
      ((pointUpperStar ⋙ (f ≫ kY)^*[Ab.{u + 1}]).obj Λ).obj.map
        ((connectedComponentsAlongAdjunction (f ≫ kY)).unit.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V)).op := by
  have nψ := (unitCompUpperStarCompInv Λ f kY).hom.naturality
    ((connectedComponentsAlongAdjunction kY).unit.app V).op
  have nu := ((upperStarFromPointAlongAdjunction (f ≫ kY)).unit.app Λ).hom.naturality
    (connectedComponentsAlongPullbackHom f kY V).op
  have B := unit_app_comp_unitCompUpperStarCompInv_app Λ f kY ((connectedComponentsAlong kY).obj V)
  simp only [Functor.comp_obj, Functor.id_obj] at nψ nu B ⊢
  rw [Category.assoc, nψ, ← Category.assoc, B, Category.assoc]
  erw [← Functor.map_comp, ← op_comp, map_unit_comp_connectedComponentsAlongPullbackHom, op_comp,
    Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact nu.symm

/-- The comparison `X ×_Y Y[S] ≅ X[S]` is compatible with the projections to `Spec LC(S, ℤ)`. -/
lemma homProfiniteToProEtAlongEquiv_map_comp_profiniteToProEtAlongPullbackHom (S : Profinite.{u})
    (b : V ⟶ (profiniteToProEtAlong kY).obj S) :
    homProfiniteToProEtAlongEquiv (f ≫ kY) _ S
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map b ≫
          profiniteToProEtAlongPullbackHom f kY S) =
      pullback.fst V.hom f ≫ homProfiniteToProEtAlongEquiv kY V S b := by
  have hI := congrArg (fun φ ↦ φ.left)
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f kY).inv_hom_id_app
      (profiniteToProEt.obj S))
  have hfst := MorphismProperty.Over.pullbackComp_left_fst_fst (P := @WeaklyEtale) (Q := ⊤) f kY
    (profiniteToProEt.obj S)
  simp only [homProfiniteToProEtAlongEquiv, Equiv.coe_fn_mk]
  refine (Category.assoc _ _ _).trans ?_
  have key : ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f kY).inv.app
      (profiniteToProEt.obj S)).left ≫ pullback.fst (profiniteToProEt.obj S).hom (f ≫ kY) =
      pullback.fst (pullback.snd (profiniteToProEt.obj S).hom kY) f ≫
        pullback.fst (profiniteToProEt.obj S).hom kY := by
    rw [← hfst, ← Category.assoc]
    exact (congrArg (· ≫ (pullback.fst (pullback.snd (profiniteToProEt.obj S).hom kY) f ≫
      pullback.fst (profiniteToProEt.obj S).hom kY)) hI).trans (Category.id_comp _)
  erw [key]
  rw [MorphismProperty.Over.pullback_map_left]
  erw [pullback.lift_fst_assoc]
  rw [Category.assoc]

/-- If precomposition with the projection `X ×_Y V ⟶ V` is bijective on morphisms to the schemes
`Spec LC(S, ℤ)`, then the induced map `π₀(X ×_Y V) ⟶ π₀(V)` is an isomorphism. -/
lemma isIso_connectedComponentsAlongPullbackHom
    (hV : ∀ S : Profinite.{u}, Function.Bijective
      (fun h : V.left ⟶ profiniteToScheme.obj S ↦ pullback.fst V.hom f ≫ h)) :
    IsIso (connectedComponentsAlongPullbackHom f kY V) := by
  refine isIso_of_coyoneda_map_bijective _ fun S ↦ ?_
  have key (a : (connectedComponentsAlong kY).obj V ⟶ S) :
      homProfiniteToProEtAlongEquiv (f ≫ kY) _ S
        ((connectedComponentsAlongAdjunction (f ≫ kY)).homEquiv _ S
          (connectedComponentsAlongPullbackHom f kY V ≫ a)) =
      pullback.fst V.hom f ≫ homProfiniteToProEtAlongEquiv kY V S
        ((connectedComponentsAlongAdjunction kY).homEquiv V S a) := by
    have h1 : (connectedComponentsAlongAdjunction (f ≫ kY)).homEquiv _ _
        (connectedComponentsAlongPullbackHom f kY V) =
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
          ((connectedComponentsAlongAdjunction kY).unit.app V) ≫
        profiniteToProEtAlongPullbackHom f kY _ :=
      Equiv.apply_symm_apply _ _
    have h2 := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f kY).inv.naturality
      (profiniteToProEt.map a)
    rw [Adjunction.homEquiv_naturality_right, h1, Category.assoc,
      (connectedComponentsAlongAdjunction kY).homEquiv_unit]
    erw [← h2, ← Category.assoc, ← Functor.map_comp]
    exact homProfiniteToProEtAlongEquiv_map_comp_profiniteToProEtAlongPullbackHom f kY V S _
  let e := ((connectedComponentsAlongAdjunction (f ≫ kY)).homEquiv
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V) S).trans
    (homProfiniteToProEtAlongEquiv (f ≫ kY) _ S)
  let e' := ((connectedComponentsAlongAdjunction kY).homEquiv V S).trans
    (homProfiniteToProEtAlongEquiv kY V S)
  have hcomp : e ∘ (fun a ↦ connectedComponentsAlongPullbackHom f kY V ≫ a) =
      (fun h ↦ pullback.fst V.hom f ≫ h) ∘ e' :=
    funext key
  rw [← e.bijective.of_comp_iff', hcomp]
  exact (hV S).comp e'.bijective

/-- **Sections of the unit along a base change.** Let `f : X ⟶ Y` be a morphism of schemes,
`k_Y : Y ⟶ Spec ℤ`, and `V` an object of `Y_proét` such that

* the presheaves `V ↦ Λ(π₀ V)` on `Y_proét` and on `X_proét` agree with their sheafifications on
  sections over `V` and over `X ×_Y V` (e.g. both are affine and weakly contractible), and
* precomposition with the projection `X ×_Y V ⟶ V` is bijective on morphisms to the schemes
  `Spec LC(S, ℤ)` (i.e. `π₀(X ×_Y V) ≅ π₀(V)`).

Then the morphism `k_Y^* p^* Λ ⟶ f_* (f ≫ k_Y)^* p^* Λ` adjoint to the composition isomorphism of
the pullbacks is bijective on sections over `V`: both sides are `Λ(π₀ V)`. -/
theorem bijective_unitCompUpperStarCompInv_app
    (hV : Function.Bijective
      ((toSheafify (ProEt.topology Y) ((connectedComponentsAlong kY).op ⋙ Λ.obj)).app (op V)))
    (hPV : Function.Bijective
      ((toSheafify (ProEt.topology X) ((connectedComponentsAlong (f ≫ kY)).op ⋙ Λ.obj)).app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V))))
    (hfst : ∀ S : Profinite.{u}, Function.Bijective
      (fun h : V.left ⟶ profiniteToScheme.obj S ↦ pullback.fst V.hom f ≫ h)) :
    Function.Bijective ((unitCompUpperStarCompInv Λ f kY).hom.app (op V)) := by
  have := isIso_connectedComponentsAlongPullbackHom f kY V hfst
  have h := map_unit_comp_unitCompUpperStarCompInv_app Λ f kY V
  have hb : Function.Bijective
      ⇑(Λ.obj.map (connectedComponentsAlongPullbackHom f kY V).op ≫
        ((upperStarFromPointAlongAdjunction (f ≫ kY)).unit.app Λ).hom.app
          (op ((connectedComponentsAlong (f ≫ kY)).obj
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V))) ≫
        ((pointUpperStar ⋙ (f ≫ kY)^*[Ab.{u + 1}]).obj Λ).obj.map
          ((connectedComponentsAlongAdjunction (f ≫ kY)).unit.app
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V)).op) := by
    rw [ConcreteCategory.coe_comp]
    exact (bijective_unit_app_comp_map_unit (f ≫ kY) Λ _ hPV).comp
      (ConcreteCategory.bijective_of_isIso _)
  rw [← h, ConcreteCategory.coe_comp] at hb
  exact (Function.Bijective.of_comp_iff _ (bijective_unit_app_comp_map_unit kY Λ V hV)).1 hb

/-- `AlgebraicGeometry.ProEtale.bijective_unitCompUpperStarCompInv_app` for a structure morphism
`k_X` equal to `f ≫ k_Y`: the morphism `k_Y^* p^* Λ ⟶ f_* k_X^* p^* Λ` adjoint to the composition
isomorphism of the pullbacks and `f ≫ k_Y = k_X` is bijective on sections over `V`. -/
theorem bijective_unit_app_comp_lowerStar_map_upperStarComp_inv_app_comp {X Y : Scheme.{u}}
    (f : X ⟶ Y) (kY : Y ⟶ specZ.{u}) (kX : X ⟶ specZ.{u}) (hk : f ≫ kY = kX) (V : Y.ProEt)
    (hV : Function.Bijective
      ((toSheafify (ProEt.topology Y) ((connectedComponentsAlong kY).op ⋙ Λ.obj)).app (op V)))
    (hPV : Function.Bijective
      ((toSheafify (ProEt.topology X) ((connectedComponentsAlong kX).op ⋙ Λ.obj)).app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V))))
    (hfst : ∀ S : Profinite.{u}, Function.Bijective
      (fun h : V.left ⟶ profiniteToScheme.obj S ↦ pullback.fst V.hom f ≫ h)) :
    Function.Bijective (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app
        ((kY)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)) ≫
      (f)_*[Ab.{u + 1}].map ((ProEtale.upperStarComp Ab.{u + 1} f kY).inv.app
        (pointUpperStar.obj Λ) ≫
          (eqToHom (congrArg (ProEtale.upperStar Ab.{u + 1}) hk)).app
            (pointUpperStar.obj Λ))).hom.app (op V)) := by
  subst hk
  simpa using bijective_unitCompUpperStarCompInv_app Λ f kY V hV hPV hfst

end Compat

end AlgebraicGeometry.ProEtale
