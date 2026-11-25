/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# The comparison pullback and direct images
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {U V : Scheme.{u}} (f : U ⟶ V)

/-- Base change along `f` commutes with the inclusion of the small étale site into the small
pro-étale site: both composites send an étale `V`-scheme `E` to `E ×_V U`. -/
noncomputable def toProEtCompOverPullbackIso :
    toProEt V ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ f ≅
      MorphismProperty.Over.pullback @Etale ⊤ f ⋙ toProEt U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext; simp; rfl)

/-- The composite of `ν` with base change along `f` is continuous. -/
instance isContinuous_toProEt_comp_overPullback :
    (toProEt V ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).IsContinuous
      V.smallEtaleTopology (ProEt.topology U) :=
  have := ProEt.isContinuous_overPullback f
  Functor.isContinuous_comp (toProEt V) (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
    V.smallEtaleTopology (ProEt.topology V) (ProEt.topology U)

/-- The composite of base change along `f` with `ν` is continuous. -/
instance isContinuous_overPullback_comp_toProEt :
    (MorphismProperty.Over.pullback @Etale ⊤ f ⋙ toProEt U).IsContinuous
    V.smallEtaleTopology (ProEt.topology U) :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous V.smallEtaleTopology
      U.smallEtaleTopology := Etale.isContinuous_overPullback f
  have := isContinuous_toProEt U
  Functor.isContinuous_comp (MorphismProperty.Over.pullback @Etale ⊤ f) (toProEt U)
    V.smallEtaleTopology U.smallEtaleTopology (ProEt.topology U)

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The restriction functors `ν_*` commute with the direct images along `f`. -/
noncomputable def lowerStarCompComparisonLowerStarIso :
    ProEtale.lowerStar A f ⋙ comparisonLowerStar A V ≅
      comparisonLowerStar A U ⋙ Etale.lowerStar A f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous V.smallEtaleTopology
      U.smallEtaleTopology := Etale.isContinuous_overPullback f
  have := ProEt.isContinuous_overPullback f
  have := isContinuous_toProEt U
  have := isContinuous_overPullback_comp_toProEt f
  Functor.sheafPushforwardContinuousComp (toProEt V)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) A V.smallEtaleTopology
      (ProEt.topology V) (ProEt.topology U) ≪≫
    Functor.sheafPushforwardContinuousIso (toProEtCompOverPullbackIso f) A
      V.smallEtaleTopology (ProEt.topology U) ≪≫
    (Functor.sheafPushforwardContinuousComp (MorphismProperty.Over.pullback @Etale ⊤ f)
      (toProEt U) A V.smallEtaleTopology U.smallEtaleTopology (ProEt.topology U)).symm

/-- The base change morphism `ν_V^* f_* ⟶ f_* ν_U^*`, the mate of
`AlgebraicGeometry.ProEtale.lowerStarCompComparisonLowerStarIso` under the adjunctions
`ν^* ⊣ ν_*`. -/
noncomputable def lowerStarComparisonUpperStarBaseChange :
    Etale.lowerStar A f ⋙ comparisonUpperStar A V ⟶
      comparisonUpperStar A U ⋙ ProEtale.lowerStar A f :=
  (mateEquiv (comparisonAdjunction A U) (comparisonAdjunction A V)).symm
    (lowerStarCompComparisonLowerStarIso f A).inv

/-- On étale `V`-schemes the base change morphism `ν_V^* f_* ⟶ f_* ν_U^*` is an isomorphism:
after applying `ν_V_*` it becomes `f_*` of the unit of `ν_U^* ⊣ ν_U_*`, up to the units of
`ν_V^* ⊣ ν_V_*`, all of which are invertible. -/
instance isIso_comparisonLowerStar_map_lowerStarComparisonUpperStarBaseChange_app
    (F : Sheaf U.smallEtaleTopology A) :
    IsIso ((comparisonLowerStar A V).map ((lowerStarComparisonUpperStarBaseChange f A).app F)) := by
  have h := unit_mateEquiv_symm (comparisonAdjunction A U) (comparisonAdjunction A V)
    (lowerStarCompComparisonLowerStarIso f A).inv F
  simp only [Functor.id_obj] at h
  have := isIso_comparisonAdjunction_unit A U
  have := isIso_comparisonAdjunction_unit A V
  have : IsIso ((comparisonAdjunction A V).unit.app ((Etale.lowerStar A f).obj F) ≫
      (comparisonLowerStar A V).map ((lowerStarComparisonUpperStarBaseChange f A).app F)) := by
    rw [lowerStarComparisonUpperStarBaseChange, ← h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((comparisonAdjunction A V).unit.app _) _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- A morphism of presheaves which is an isomorphism on the members of a cofiltered diagram is an
isomorphism on a cone point over it, if both presheaves send the cone to a colimit. -/
lemma _root_.CategoryTheory.NatTrans.isIso_app_of_isColimit {C : Type*} [Category* C]
    {P₁ P₂ : Cᵒᵖ ⥤ A} (φ : P₁ ⟶ P₂) {I : Type*} [Category* I] {K : I ⥤ C} (c : Cone K)
    (h₁ : IsColimit (P₁.mapCocone c.op)) (h₂ : IsColimit (P₂.mapCocone c.op))
    (h : ∀ i, IsIso (φ.app (op (K.obj i)))) : IsIso (φ.app (op c.pt)) := by
  have : IsIso (Functor.whiskerLeft K.op φ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun i ↦ h i.unop
  let ψ := asIso (Functor.whiskerLeft K.op φ)
  have h₂' := (IsColimit.precomposeHomEquiv ψ (P₂.mapCocone c.op)).symm h₂
  let t : P₁.mapCocone c.op ⟶ (Cocone.precompose ψ.hom).obj (P₂.mapCocone c.op) :=
    { hom := φ.app (op c.pt)
      w := fun i ↦ by simp [ψ] }
  have := IsColimit.hom_isIso h₁ h₂' t
  exact inferInstanceAs (IsIso ((Cocone.forget _).map t))

/-- A morphism of pro-étale sheaves is an isomorphism if it is so on the sections over the objects
of the affine pro-étale site. -/
lemma isIso_of_isIso_app_affineProEt {X : Scheme.{u}} {G₁ G₂ : Sheaf (ProEt.topology X) A}
    (φ : G₁ ⟶ G₂) (h : ∀ W : X.AffineProEt,
      IsIso (φ.hom.app (op ((AffineProEt.toProEt X).obj W)))) : IsIso φ := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  let Φ := (AffineProEt.toProEt X).sheafPushforwardContinuous A (AffineProEt.topology X)
    (ProEt.topology X)
  suffices IsIso ((sheafToPresheaf _ A).map (Φ.map φ)) by
    have : IsIso (Φ.map φ) := isIso_of_reflects_iso _ (sheafToPresheaf _ A)
    exact isIso_of_reflects_iso _ Φ
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun W ↦ h W.unop

section Presentation

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {W : V.AffineProEt}
  (pres : RelativeLimitPresentation J (AffineEtale.toAffineProEt V) W)

/-- The diagram of affine étale `V`-schemes of a presentation of an object `W` of the affine
pro-étale site of `V`. -/
noncomputable def presentationDiagram : J ⥤ V.Etale :=
  pres.diag ⋙ AffineEtale.Spec V

instance (j : J) : IsAffine ((presentationDiagram pres).obj j).left := by
  dsimp only [presentationDiagram, Functor.comp_obj]
  rw [AffineEtale.Spec_obj_left]
  infer_instance

/-- The limit cone with point `W` over `presentationDiagram pres`, in the pro-étale site. -/
noncomputable def presentationCone : Cone (presentationDiagram pres ⋙ toProEt V) :=
  (Cone.postcompose (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft pres.diag (AffineEtale.toAffineProEtCompToProEtIso V) ≪≫
      (Functor.associator _ _ _).symm).hom).obj ((AffineProEt.toProEt V).mapCone pres.cone)

/-- The underlying cone of schemes of `presentationCone pres` is a limit. -/
noncomputable def isLimitPresentationCone :
    IsLimit ((ProEt.forget V ⋙ CategoryTheory.Over.forget V).mapCone (presentationCone pres)) :=
  AffineProEt.isLimitMapConeToSchemeOfIsLimit pres.cone pres.isLimit

/-- The base change along `f` of `presentationDiagram pres`: the étale `U`-schemes
`U ×_V Wⱼ`. -/
noncomputable def pullbackPresentationDiagram : J ⥤ U.Etale :=
  presentationDiagram pres ⋙ MorphismProperty.Over.pullback @Etale ⊤ f

/-- The cone with point `U ×_V W` over `pullbackPresentationDiagram f pres`. -/
noncomputable def pullbackPresentationCone :
    Cone (pullbackPresentationDiagram f pres ⋙ toProEt U) :=
  (Cone.postcompose ((Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (presentationDiagram pres) (toProEtCompOverPullbackIso f).hom ≫
    (Functor.associator _ _ _).inv)).obj
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).mapCone (presentationCone pres))

/-- The underlying cone of schemes of `pullbackPresentationCone f pres` is a limit: base change
along `f` preserves limits. -/
noncomputable def isLimitPullbackPresentationCone :
    IsLimit ((ProEt.forget U ⋙ CategoryTheory.Over.forget U).mapCone
      (pullbackPresentationCone f pres)) := by
  have h₀ : IsLimit ((ProEt.forget V).mapCone (presentationCone pres)) :=
    isLimitOfReflects (CategoryTheory.Over.forget V) (isLimitPresentationCone pres)
  have h₁ := isLimitOfPreserves (CategoryTheory.Over.forget U)
    (isLimitOfPreserves (CategoryTheory.Over.pullback f) h₀)
  refine IsLimit.ofIsoLimit h₁ (Cone.ext (Iso.refl _) fun j ↦ ?_)
  apply pullback.hom_ext
  · simp only [pullbackPresentationCone, toProEtCompOverPullbackIso]
    simp only [Functor.mapCone_pt, Over.forget_obj, Over.pullback_obj_left,
      Functor.const_obj_obj, Functor.comp_obj, Functor.mapCone_π_app, ProEt.forget_map,
      Over.forget_map, Over.pullback_map_left, limit.lift_π, PullbackCone.mk_π_app,
      Cone.postcompose_obj_pt, Iso.refl_hom, Cone.postcompose_obj_π, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
      Functor.associator_inv_app, Category.comp_id, Functor.comp_map,
      MorphismProperty.Over.pullback_map_left, Category.id_comp]
    exact (pullback.lift_fst _ _ _).symm
  · simp only [pullbackPresentationCone, toProEtCompOverPullbackIso]
    simp only [Functor.mapCone_pt, Over.forget_obj, Over.pullback_obj_left,
      Functor.const_obj_obj, Functor.comp_obj, Functor.mapCone_π_app, ProEt.forget_map,
      Over.forget_map, Over.pullback_map_left, limit.lift_π, PullbackCone.mk_π_app,
      Cone.postcompose_obj_pt, Iso.refl_hom, Cone.postcompose_obj_π, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
      Functor.associator_inv_app, Category.comp_id, Functor.comp_map,
      MorphismProperty.Over.pullback_map_left, Category.id_comp]
    exact (pullback.lift_snd _ _ _).symm

variable [QuasiCompact f] [QuasiSeparated f]

instance (j : J) : CompactSpace ((pullbackPresentationDiagram f pres).obj j).left := by
  have : CompactSpace ((𝟭 Scheme).obj ((presentationDiagram pres).obj j).left) :=
    inferInstanceAs (CompactSpace ((presentationDiagram pres).obj j).left)
  exact QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst ((presentationDiagram pres).obj j).hom f)

instance (j : J) : QuasiSeparatedSpace ((pullbackPresentationDiagram f pres).obj j).left := by
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj ((presentationDiagram pres).obj j).left) :=
    inferInstanceAs (QuasiSeparatedSpace ((presentationDiagram pres).obj j).left)
  exact quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst ((presentationDiagram pres).obj j).hom f)

instance {i j : J} (g : i ⟶ j) : IsAffineHom ((pullbackPresentationDiagram f pres).map g).left :=
  MorphismProperty.pullbackLift_fst_snd (P := @IsAffineHom) f
    (Over.w ((presentationDiagram pres).map g).hom).symm inferInstance

end Presentation

/-- The base change morphism `ν_V^* f_* ⟶ f_* ν_U^*` is an isomorphism for `f` quasi-compact
and quasi-separated. -/
theorem isIso_lowerStarComparisonUpperStarBaseChange [QuasiCompact f] [QuasiSeparated f] :
    IsIso (lowerStarComparisonUpperStarBaseChange f A) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  refine isIso_of_isIso_app_affineProEt A _ fun W ↦ ?_
  obtain ⟨J, _, _, ⟨pres⟩⟩ := AffineProEt.exists_relativeLimitPresentation _ W
  obtain ⟨h₁⟩ := isColimit_comparisonUpperStar_mapCocone A ((Etale.lowerStar A f).obj F)
    (presentationDiagram pres) (presentationCone pres) (isLimitPresentationCone pres)
  obtain ⟨h₂⟩ := isColimit_comparisonUpperStar_mapCocone A F (pullbackPresentationDiagram f pres)
    (pullbackPresentationCone f pres) (isLimitPullbackPresentationCone f pres)
  refine NatTrans.isIso_app_of_isColimit A ((lowerStarComparisonUpperStarBaseChange f A).app F).hom
    (presentationCone pres) h₁ ?_ fun j ↦ ?_
  · exact h₂
  · have := isIso_comparisonLowerStar_map_lowerStarComparisonUpperStarBaseChange_app f A F
    have : IsIso ((comparisonLowerStar A V).map
        ((lowerStarComparisonUpperStarBaseChange f A).app F)).hom :=
      inferInstanceAs (IsIso ((sheafToPresheaf (V.smallEtaleTopology) A).map
        ((comparisonLowerStar A V).map ((lowerStarComparisonUpperStarBaseChange f A).app F))))
    exact (NatTrans.isIso_iff_isIso_app _).1 this (op ((presentationDiagram pres).obj j))

end AlgebraicGeometry.ProEtale
