/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.SectionsContinuity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.SheafIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.UpperStarLowerStarHom

/-!
# `g_* g^* H` as the colimit of the finite Galois levels

Let `Ω / L` be a Galois extension, `G` a scheme over `Spec L`, `g_{L'} : G_{L'} = G ×_L L' ⟶ G`
for the finite Galois subextensions `L'` and `g : G_Ω = G ×_L Ω ⟶ G`. The restrictions along the
projections `G_Ω ⟶ G_{L'}` form a cocone `g_{L'*} g_{L'}^* ⟶ g_* g^*` over the diagram of the
`g_{L'*} g_{L'}^*` (`AlgebraicGeometry.ProEtale.galoisUpperLowerCocone`). For an abelian sheaf `H`
of étale origin, it is a colimit cocone at `H`
(`AlgebraicGeometry.ProEtale.nonempty_isColimit_galoisUpperLowerCocone`).

This is first proved in the restriction model `j_{g}^* ⋙ g_*`, whose sections over `W` are the
sections of `H` over `W ×_G G_{L'}` (`AlgebraicGeometry.ProEtale.galoisRestrictionCocone`): the
comparison map from the colimit is bijective on sections over objects with affine underlying
scheme, by `AlgebraicGeometry.ProEtale.nonempty_isColimit_galoisSectionsCocone` and the
commutation of sections with filtered colimits, and these objects cover the pro-étale site.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite FiniteGaloisIntermediateField

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

/-! ### The restriction model -/

variable (Ω) in
/-- The diagram of the restriction models `(j_{g_{L'}}^* ⋙ g_{L'*}) H` of `g_{L'*} g_{L'}^* H`,
whose sections over `V` are the sections of `H` over `V ×_G G_{L'}`. -/
@[simps]
noncomputable def galoisRestrictionDiagram (H : Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1}) :
    FiniteGaloisIntermediateField L Ω ⥤ Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1} where
  obj L' := (localizationRestriction AddCommGrpCat.{u + 1}
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L')))) inferInstance ⋙
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L'))))_*[AddCommGrpCat.{u + 1}]).obj
      H
  map f := ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op
    (baseChangeHom _ _ (galoisLevelMap Ω h (leOfHom f)) (galoisLevelMap_fst h _))) H.obj)
  map_id L' := by
    refine Sheaf.hom_ext ?_
    ext V : 2
    exact (galoisSectionsDiagram Ω h H V.unop).map_id L'
  map_comp f f' := by
    refine Sheaf.hom_ext ?_
    ext V : 2
    exact (galoisSectionsDiagram Ω h H V.unop).map_comp f f'

variable (Ω) in
/-- The cocone of the restrictions along the projections `G_Ω ⟶ G_{L'}`, in the restriction
model. -/
@[simps]
noncomputable def galoisRestrictionCocone (H : Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1}) :
    Cocone (galoisRestrictionDiagram Ω h H) where
  pt := (localizationRestriction AddCommGrpCat.{u + 1}
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) inferInstance ⋙
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*[AddCommGrpCat.{u + 1}]).obj H
  ι :=
    { app L' := ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op
        (baseChangeHom _ _ (galoisLevelProjection h L') (galoisLevelProjection_fst h L'))) H.obj)
      naturality L' L'' f := by
        refine Sheaf.hom_ext ?_
        ext V : 2
        exact (galoisSectionsCocone Ω h H V.unop).w f }

/-- Every object of the pro-étale site is covered by objects with affine underlying scheme. -/
lemma exists_mem_topology_isAffine (V : G.ProEt) :
    ∃ S ∈ ProEt.topology G V, ∀ ⦃Y : G.ProEt⦄ (f : Y ⟶ V), S f →
      ∃ (Z : G.ProEt) (a : Y ⟶ Z) (b : Z ⟶ V), IsAffine Z.left ∧ a ≫ b = f := by
  let ι : Type u := V.left.affineOpens
  let Z (U : ι) : G.ProEt := overOpens (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) V U.1
  let b (U : ι) : Z U ⟶ V := overOpensι (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) V U.1
  refine ⟨Sieve.ofArrows Z b, ProEt.mem_topology_of_isOpenImmersion V _ Z b
    (fun U ↦ inferInstanceAs (IsOpenImmersion U.1.ι)) (fun x ↦ ?_)
    (fun U ↦ Sieve.ofArrows_mk _ _ U), ?_⟩
  · obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩
  · rintro Y _ ⟨_, a, _, ⟨U⟩, rfl⟩
    exact ⟨Z U, a, b U, U.2, rfl⟩

/-- **For `H` of étale origin, the restriction cocone is a colimit.** -/
theorem nonempty_isColimit_galoisRestrictionCocone
    (H : Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1})
    (hH : (comparisonUpperStar AddCommGrpCat.{u + 1} G).essImage H) :
    Nonempty (IsColimit (galoisRestrictionCocone Ω h H)) := by
  let hc₀ := colimit.isColimit (galoisRestrictionDiagram Ω h H)
  have key (W : G.ProEt) (hW : IsAffine W.left) :
      IsIso ((hc₀.desc (galoisRestrictionCocone Ω h H)).hom.app (op W)) := by
    have hP := Scheme.ProEt.isColimitSectionsOfIsColimitOfShrink hc₀ W
    obtain ⟨hQ⟩ := nonempty_isColimit_galoisSectionsCocone (Ω := Ω) h H W hH
    have := IsColimit.hom_isIso hP hQ
      ((Scheme.ProEt.abSectionsFunctor W).mapCoconeMorphism
        (hc₀.descCoconeMorphism (galoisRestrictionCocone Ω h H)))
    exact inferInstanceAs (IsIso ((Cocone.forget _).map
      ((Scheme.ProEt.abSectionsFunctor W).mapCoconeMorphism
        (hc₀.descCoconeMorphism (galoisRestrictionCocone Ω h H)))))
  have := Sheaf.isIso_of_isIso_app_of_forall_exists_mem
    (hc₀.desc (galoisRestrictionCocone Ω h H)) (fun (W : G.ProEt) ↦ IsAffine W.left)
    exists_mem_topology_isAffine key
  exact ⟨IsColimit.ofPointIso hc₀⟩

/-! ### The pushforward of the pullback -/

variable (Ω) in
/-- The diagram of the `g_{L'*} g_{L'}^* H`, with transition maps the restrictions along the
transition maps `G_{L''} ⟶ G_{L'}`. -/
@[simps]
noncomputable def galoisUpperLowerDiagram (H : Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1}) :
    FiniteGaloisIntermediateField L Ω ⥤ Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1} where
  obj L' :=
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L'))))_*[AddCommGrpCat.{u + 1}].obj
      ((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L'))))^*[
        AddCommGrpCat.{u + 1}].obj H)
  map f := (upperStarLowerStarHom _ _ (galoisLevelMap Ω h (leOfHom f))
    (galoisLevelMap_fst h _)).app H
  map_id L' := by
    rw [upperStarLowerStarHom_congr _ (galoisLevelMap_refl h _), upperStarLowerStarHom_id]
    rfl
  map_comp f f' := by
    rw [← NatTrans.comp_app, upperStarLowerStarHom_comp,
      upperStarLowerStarHom_congr _ (galoisLevelMap_comp h _ _ _)]

variable (Ω) in
/-- The cocone of the restrictions `g_{L'*} g_{L'}^* H ⟶ g_* g^* H` along the projections
`G_Ω ⟶ G_{L'}`. -/
@[simps]
noncomputable def galoisUpperLowerCocone (H : Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1}) :
    Cocone (galoisUpperLowerDiagram Ω h H) where
  pt :=
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*[AddCommGrpCat.{u + 1}].obj
      ((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*[
        AddCommGrpCat.{u + 1}].obj H)
  ι :=
    { app L' := (upperStarLowerStarHom _ _ (galoisLevelProjection h L')
        (galoisLevelProjection_fst h L')).app H
      naturality L' L'' f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, galoisUpperLowerDiagram_map]
        erw [comp_id, ← NatTrans.comp_app, upperStarLowerStarHom_comp]
        rw [upperStarLowerStarHom_congr _ (galoisLevelProjection_comp_galoisLevelMap h _)] }

/-- The comparison `g^* ≅ j_g^*` identifies `g_* g^* H` and its restriction model, compatibly
with the restrictions along a morphism of covers. -/
lemma upperStarLowerStarHom_app_comp {Y Y' : Scheme.{u}} (g : Y ⟶ G) (g' : Y' ⟶ G)
    [WeaklyEtale g] [WeaklyEtale g'] (s : Y' ⟶ Y) (hs : s ≫ g = g')
    (H : Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1}) :
    (upperStarLowerStarHom g g' s hs).app H ≫ (g')_*[AddCommGrpCat.{u + 1}].map
        ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g' inferInstance).hom.app H) =
      (g)_*[AddCommGrpCat.{u + 1}].map
        ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g inferInstance).hom.app H) ≫
        (restrictionHom g g' s hs).app H := by
  rw [upperStarLowerStarHom, NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerRight_app, assoc, assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  erw [comp_id]

/-- The diagram of the `g_{L'*} g_{L'}^* H` is isomorphic to its restriction model. -/
noncomputable def galoisUpperLowerDiagramIso (H : Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1}) :
    galoisUpperLowerDiagram Ω h H ≅ galoisRestrictionDiagram Ω h H :=
  NatIso.ofComponents (fun L' ↦ (pullback.fst h
      (Spec.map (CommRingCat.ofHom (algebraMap L L'))))_*[AddCommGrpCat.{u + 1}].mapIso
      ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} _ inferInstance).app H))
    fun f ↦ by
      rw [galoisUpperLowerDiagram_map, Functor.mapIso_hom, Iso.app_hom, Functor.mapIso_hom,
        Iso.app_hom, upperStarLowerStarHom_app_comp]
      congr 1
      exact Sheaf.hom_ext (restrictionHom_app_hom _ _ H)

/-- **For `H` of étale origin, `g_* g^* H` is the colimit of the `g_{L'*} g_{L'}^* H`.** -/
theorem nonempty_isColimit_galoisUpperLowerCocone
    (H : Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1})
    (hH : (comparisonUpperStar AddCommGrpCat.{u + 1} G).essImage H) :
    Nonempty (IsColimit (galoisUpperLowerCocone Ω h H)) := by
  obtain ⟨hc⟩ := nonempty_isColimit_galoisRestrictionCocone (Ω := Ω) h H hH
  refine ⟨(IsColimit.equivOfNatIsoOfIso (galoisUpperLowerDiagramIso h H) _ _ ?_).symm hc⟩
  refine Cocone.ext ((pullback.fst h (Spec.map (CommRingCat.ofHom
    (algebraMap L Ω))))_*[AddCommGrpCat.{u + 1}].mapIso
      ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} _ inferInstance).app H)) ?_
  intro L'
  simp only [Cocone.precompose_obj_ι, NatTrans.comp_app, galoisUpperLowerDiagramIso,
    NatIso.ofComponents_inv_app, galoisUpperLowerCocone_ι_app, Functor.mapIso_hom, Iso.app_hom,
    galoisRestrictionCocone_ι_app, Functor.mapIso_inv, Iso.app_inv, assoc]
  rw [upperStarLowerStarHom_app_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, id_comp]
  exact Sheaf.hom_ext (restrictionHom_app_hom _ _ H)

end AlgebraicGeometry.ProEtale
