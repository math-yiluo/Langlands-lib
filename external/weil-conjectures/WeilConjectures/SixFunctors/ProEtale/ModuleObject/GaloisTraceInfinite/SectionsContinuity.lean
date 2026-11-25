/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.GaloisLevel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGaloisDescent

/-!
# Sections of sheaves of étale origin over the Galois tower

Let `Ω / L` be a Galois extension, `G` a scheme over `Spec L`, `G_{L'} = G ×_L L'` for the finite
Galois subextensions `L'` and `G_Ω = G ×_L Ω`, with structure maps `g_{L'}`, `g` to `G`. For an
abelian pro-étale sheaf `H` of étale origin on `G` (`H ≅ ν^* F₀`) and an object `W` of `G_proét`
with affine underlying scheme, the sections of `H` over `W ×_G G_Ω` are the filtered colimit of
the sections over the `W ×_G G_{L'}`
(`AlgebraicGeometry.ProEtale.nonempty_isColimit_galoisSectionsCocone`).

This is the continuity of `ν^*`
(`AlgebraicGeometry.ProEtale.isColimit_comparisonUpperStar_mapCocone_of_isAffine`) on the affine
scheme `W`: `W ×_G G_Ω` is the limit of the finite étale `W`-schemes
`W ×_G G_{L'}` (`AlgebraicGeometry.isLimitGaloisLevelCone`), and the restriction of `ν^* F₀` to
`W` is `ν^*` of the étale pullback of `F₀`
(`AlgebraicGeometry.ProEtale.comparisonUpperStarUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite FiniteGaloisIntermediateField

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L)) (H : Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1}) (W : G.ProEt)

variable (Ω) in
/-- The sections `L' ↦ H(W ×_G G_{L'})` of `H` over the finite Galois levels. -/
@[simps]
noncomputable def galoisSectionsDiagram :
    FiniteGaloisIntermediateField L Ω ⥤ AddCommGrpCat.{u + 1} where
  obj L' := H.obj.obj (op ((baseChangeFunctor
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L'))))).obj W))
  map {L' L''} f := H.obj.map ((baseChangeHom _ _ (galoisLevelMap Ω h (leOfHom f))
    (galoisLevelMap_fst h _)).app W).op
  map_id L' := by
    rw [← H.obj.map_id, ← op_id]
    congr 2
    rw [baseChangeHom_congr _ (galoisLevelMap_refl h _), baseChangeHom_id]
    rfl
  map_comp {L' L'' L'''} f f' := by
    rw [← H.obj.map_comp, ← op_comp, ← NatTrans.comp_app, baseChangeHom_comp,
      baseChangeHom_congr _ (galoisLevelMap_comp h (leOfHom f) (leOfHom f') _)]

variable (Ω) in
/-- The restrictions `H(W ×_G G_{L'}) ⟶ H(W ×_G G_Ω)`. -/
@[simps]
noncomputable def galoisSectionsCocone : Cocone (galoisSectionsDiagram Ω h H W) where
  pt := H.obj.obj (op ((baseChangeFunctor
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).obj W))
  ι :=
    { app L' := H.obj.map ((baseChangeHom _ _ (galoisLevelProjection h L')
        (galoisLevelProjection_fst h L')).app W).op
      naturality L' L'' f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          galoisSectionsDiagram_map]
        rw [← H.obj.map_comp, ← op_comp, ← NatTrans.comp_app, baseChangeHom_comp,
          baseChangeHom_congr _ (galoisLevelProjection_comp_galoisLevelMap h (leOfHom f))] }

/-- The object `T` of `G_proét` with the structure morphism `T ⟶ W ⟶ G` is isomorphic to the
base change `W ×_G Y` along `g : Y ⟶ G` when `T = W ×_G Y` and `T ⟶ W` is the first
projection. -/
noncomputable def baseChangeObjIso {Y : Scheme.{u}} (g : Y ⟶ G) [WeaklyEtale g]
    [WeaklyEtale (pullback.fst W.hom g)] :
    (baseChangeFunctor g).obj W ≅
      (MorphismProperty.Over.map ⊤ W.prop).obj
        (MorphismProperty.Over.mk ⊤ (pullback.fst W.hom g) inferInstance) where
  hom := MorphismProperty.Over.homMk (𝟙 _) (by simp [pullback.condition]) trivial
  inv := MorphismProperty.Over.homMk (𝟙 _) (by simp [pullback.condition]) trivial
  hom_inv_id := MorphismProperty.Over.Hom.ext (Category.id_comp _)
  inv_hom_id := MorphismProperty.Over.Hom.ext (Category.id_comp _)

omit [IsGalois L Ω] in
lemma localizationRestriction_obj_obj_map {A B : W.left.ProEt} (f : A ⟶ B) :
    ((localizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop).obj H).obj.map f.op =
      H.obj.map ((MorphismProperty.Over.map ⊤ W.prop).map f).op :=
  rfl

omit [IsGalois L Ω] in
lemma sheafToPresheaf_localizationRestriction_obj_map {A B : W.left.ProEt} (f : A ⟶ B) :
    ((sheafToPresheaf _ _).obj
      ((localizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop).obj H)).map f.op =
      H.obj.map ((MorphismProperty.Over.map ⊤ W.prop).map f).op :=
  rfl

/-- **Continuity of sheaves of étale origin along the Galois tower**: for `H` of étale origin
and `W` affine, `H(W ×_G G_Ω) = colim_{L'} H(W ×_G G_{L'})`. -/
theorem nonempty_isColimit_galoisSectionsCocone
    (hH : (comparisonUpperStar AddCommGrpCat.{u + 1} G).essImage H) [IsAffine W.left] :
    Nonempty (IsColimit (galoisSectionsCocone Ω h H W)) := by
  obtain ⟨F₀, ⟨e⟩⟩ := hH
  let D := pullbackDiagram W.hom (galoisLevelProj Ω h)
  let K : (FiniteGaloisIntermediateField L Ω)ᵒᵖ ⥤ W.left.Etale :=
    MorphismProperty.Over.lift' (P := @Etale) (Q := ⊤) D
      (pullbackDiagramFst W.hom (galoisLevelProj Ω h))
      (fun j ↦ inferInstanceAs (Etale (pullback.fst W.hom ((galoisLevelProj Ω h).app j))))
      (fun _ ↦ trivial)
  have (j : (FiniteGaloisIntermediateField L Ω)ᵒᵖ) : IsAffine (K.obj j).left :=
    isAffine_of_isAffineHom (Y := W.left) (pullback.fst W.hom ((galoisLevelProj Ω h).app j))
  let c₀ := pullbackDiagramCone W.hom (galoisLevelProj Ω h) (galoisLevelCone h)
    (pullback.fst h _) (galoisLevelCone_π_app_comp_galoisLevelProj_app h)
  let c : Cone (K ⋙ toProEt W.left) :=
    { pt := MorphismProperty.Over.mk ⊤ (pullback.fst W.hom
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))) inferInstance
      π :=
        { app j := MorphismProperty.Over.homMk (c₀.π.app j)
            ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) trivial
          naturality j j' φ := MorphismProperty.Over.Hom.ext (c₀.π.naturality φ) } }
  have hc : IsLimit ((ProEt.forget W.left ⋙ Over.forget W.left).mapCone c) :=
    have := IsCofiltered.isConnected (FiniteGaloisIntermediateField L Ω)ᵒᵖ
    isLimitPullbackDiagramCone W.hom (galoisLevelProj Ω h) (galoisLevelCone h) _
      (galoisLevelCone_π_app_comp_galoisLevelProj_app h) (isLimitGaloisLevelCone h)
  obtain ⟨hc'⟩ := isColimit_comparisonUpperStar_mapCocone_of_isAffine AddCommGrpCat.{u + 1}
    ((Etale.upperStar AddCommGrpCat.{u + 1} W.hom).obj F₀) K c hc
  let E : (comparisonUpperStar AddCommGrpCat.{u + 1} W.left).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} W.hom).obj F₀) ≅
      (localizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop).obj H :=
    ((comparisonUpperStarUpperStarIso AddCommGrpCat.{u + 1} W.hom).app F₀).symm ≪≫
      (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop).app _ ≪≫
      (localizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop).mapIso e
  have hc'' := IsColimit.mapCoconeEquiv ((sheafToPresheaf _ _).mapIso E) hc'
  have hw := hc''.whiskerEquivalence (opOpEquivalence (FiniteGaloisIntermediateField L Ω)).symm
  refine ⟨IsColimit.equivOfNatIsoOfIso (NatIso.ofComponents
    (fun (L' : FiniteGaloisIntermediateField L Ω) ↦ H.obj.mapIso (baseChangeObjIso W
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L'))))).op)
      ?_) _ (galoisSectionsCocone Ω h H W) ?_ hw⟩
  · intro X Y f
    simp only [Functor.comp_map, Functor.op_map, Iso.op_hom, Functor.mapIso_hom,
      galoisSectionsDiagram_map]
    erw [sheafToPresheaf_localizationRestriction_obj_map]
    rw [← H.obj.map_comp, ← H.obj.map_comp, ← op_comp, ← op_comp]
    congr 2
  · refine Cocone.ext (H.obj.mapIso (baseChangeObjIso W (pullback.fst h _)).op) (fun j ↦ ?_)
    dsimp
    simp only [Iso.op_inv, Iso.op_hom]
    rw [localizationRestriction_obj_obj_map, ← H.obj.map_comp, ← H.obj.map_comp, ← op_comp,
      ← op_comp]
    congr 2

end AlgebraicGeometry.ProEtale
