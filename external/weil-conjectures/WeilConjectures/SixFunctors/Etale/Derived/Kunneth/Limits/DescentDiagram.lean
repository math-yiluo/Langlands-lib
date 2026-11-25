/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# The system `p_i^* p_{i*} F` attached to a cone of schemes

Let `c` be a cone over a diagram of schemes `D : I ⥤ Scheme`, with projections
`p_i : c.pt ⟶ D.obj i`, and let `F` be an étale sheaf on `c.pt`. The sheaves
`p_i^* p_{i*} F` form a diagram indexed by `Iᵒᵖ`, and the counits `p_i^* p_{i*} F ⟶ F` form a
cocone over it.

For `q : X ⟶ Y`, `g : Y ⟶ Z` and `r = q ≫ g`, the transition map
`r^* r_* F ⟶ q^* q_* F` (`AlgebraicGeometry.Etale.descentTransition`) is the transpose along
`r^* ⊣ r_*` of the composite
`r_* F ≅ g_* q_* F ⟶ g_* q_* q^* q_* F ≅ r_* q^* q_* F` of the unit of `q^* ⊣ q_*` with the
composition isomorphisms of the pushforwards.

## Main definitions

- `AlgebraicGeometry.Etale.descentTransition`: the transition map `r^* r_* F ⟶ q^* q_* F`.
- `AlgebraicGeometry.Etale.descentDiagram`: the diagram `i ↦ p_i^* p_{i*} F`.
- `AlgebraicGeometry.Etale.descentCocone`: the cocone of counits `p_i^* p_{i*} F ⟶ F`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section Transition

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X Y Z : Scheme.{u}} (q : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ Z) (hr : r = q ≫ g)
  (F : Sheaf X.smallEtaleTopology A)

/-- The composite `r_* F ≅ g_* q_* F ⟶ g_* q_* q^* q_* F ≅ r_* q^* q_* F` of the unit of
`q^* ⊣ q_*` at `q_* F` with the composition isomorphisms of the pushforwards, for `r = q ≫ g`.
Its transpose along `r^* ⊣ r_*` is `AlgebraicGeometry.Etale.descentTransition`. -/
noncomputable def descentTransitionAux :
    (r)_*[A].obj F ⟶ (r)_*[A].obj ((q)^*[A].obj ((q)_*[A].obj F)) :=
  (lowerStarComp A q g r hr).inv.app F ≫
    (g)_*[A].map ((upperStarLowerStarAdjunction A q).unit.app ((q)_*[A].obj F)) ≫
    (lowerStarComp A q g r hr).hom.app _

/-- The transition map `r^* r_* F ⟶ q^* q_* F` for `r = q ≫ g`: the transpose along
`r^* ⊣ r_*` of `AlgebraicGeometry.Etale.descentTransitionAux`. -/
noncomputable def descentTransition :
    (r)^*[A].obj ((r)_*[A].obj F) ⟶ (q)^*[A].obj ((q)_*[A].obj F) :=
  ((upperStarLowerStarAdjunction A r).homEquiv _ _).symm (descentTransitionAux A q g r hr F)

omit [HasSmallSiteSheafify A] in
lemma homEquiv_descentTransition :
    (upperStarLowerStarAdjunction A r).homEquiv _ _ (descentTransition A q g r hr F) =
      descentTransitionAux A q g r hr F := by
  simp [descentTransition]

omit [HasSmallSiteSheafify A] in
/-- The transition maps are compatible with the counits. -/
@[reassoc (attr := simp)]
lemma descentTransition_counit :
    descentTransition A q g r hr F ≫ (upperStarLowerStarAdjunction A q).counit.app F =
      (upperStarLowerStarAdjunction A r).counit.app F := by
  have h : descentTransitionAux A q g r hr F ≫
      (r)_*[A].map ((upperStarLowerStarAdjunction A q).counit.app F) = 𝟙 _ := by
    simp only [descentTransitionAux, Category.assoc]
    rw [← (lowerStarComp A q g r hr).hom.naturality, Functor.comp_map, ← Functor.map_comp_assoc,
      Adjunction.right_triangle_components]
    simp
  rw [descentTransition, ← Adjunction.homEquiv_naturality_right_symm, h,
    Adjunction.homEquiv_counit]
  simp

omit [HasSmallSiteSheafify A] in
/-- The transition map along an identity is the identity. -/
lemma descentTransition_id (e : Y ⟶ Y) (he : e = 𝟙 Y) :
    descentTransition A q e q (by simp [he]) F = 𝟙 _ := by
  subst he
  apply ((upperStarLowerStarAdjunction A q).homEquiv _ _).injective
  rw [homEquiv_descentTransition, Adjunction.homEquiv_id, descentTransitionAux,
    lowerStarComp_id_right]
  simp

omit [HasSmallSiteSheafify A] in
/-- The transition maps compose. -/
lemma descentTransition_comp {W : Scheme.{u}} (g₂ : Z ⟶ W) (g₁₂ : Y ⟶ W)
    (hg₁₂ : g₁₂ = g ≫ g₂) (r₂ : X ⟶ W) (hr₂ : r₂ = r ≫ g₂) :
    descentTransition A q g₁₂ r₂ (by rw [hr₂, hr, hg₁₂, Category.assoc]) F =
      descentTransition A r g₂ r₂ hr₂ F ≫ descentTransition A q g r hr F := by
  apply ((upperStarLowerStarAdjunction A r₂).homEquiv _ _).injective
  rw [homEquiv_descentTransition, Adjunction.homEquiv_naturality_right,
    homEquiv_descentTransition]
  simp only [descentTransitionAux, Category.assoc]
  rw [← (lowerStarComp A r g₂ r₂ hr₂).hom.naturality, Functor.comp_map,
    ← Functor.map_comp_assoc, ← Adjunction.homEquiv_unit, homEquiv_descentTransition,
    descentTransitionAux]
  have kiso : Functor.isoWhiskerRight (lowerStarComp A q g r hr) (g₂)_*[A] ≪≫
      lowerStarComp A r g₂ r₂ hr₂ = Functor.isoWhiskerLeft (q)_*[A]
        (lowerStarComp A g g₂ g₁₂ hg₁₂) ≪≫
      lowerStarComp A q g₁₂ r₂ (by rw [hr₂, hr, hg₁₂, Category.assoc]) :=
    Iso.ext (lowerStarComp_assoc' A q g g₂ r g₁₂ r₂ hr hg₁₂ hr₂)
  have k1 := NatTrans.congr_app (congrArg Iso.hom kiso)
    ((q)^*[A].obj ((q)_*[A].obj F))
  have k2 := NatTrans.congr_app (congrArg Iso.inv kiso) F
  have k3 := (lowerStarComp A g g₂ g₁₂ hg₁₂).hom.naturality
    ((upperStarLowerStarAdjunction A q).unit.app ((q)_*[A].obj F))
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] at k1 k2
  simp only [Functor.comp_map] at k3
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% k2, k1, reassoc_of% k3, Iso.inv_hom_id_app_assoc]

end Transition

section Diagram

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {I : Type*} [Category I] {D : I ⥤ Scheme.{u}} (c : Cone D)
  (F : Sheaf c.pt.smallEtaleTopology A)

/-- **The system `p_i^* p_{i*} F`.** For a cone `c` over a diagram of schemes `D : I ⥤ Scheme`
with projections `p_i : c.pt ⟶ D.obj i` and an étale sheaf `F` on `c.pt`, the diagram
`i ↦ p_i^* p_{i*} F` indexed by `Iᵒᵖ`, with transition maps
`AlgebraicGeometry.Etale.descentTransition`. -/
@[simps]
noncomputable def descentDiagram : Iᵒᵖ ⥤ Sheaf c.pt.smallEtaleTopology A where
  obj i := (c.π.app i.unop)^*[A].obj ((c.π.app i.unop)_*[A].obj F)
  map {i j} f := descentTransition A (c.π.app j.unop) (D.map f.unop) (c.π.app i.unop)
    (c.w f.unop).symm F
  map_id i := descentTransition_id A (c.π.app i.unop) F (D.map (𝟙 i.unop)) (D.map_id _)
  map_comp {i j k} f f' := descentTransition_comp A (c.π.app k.unop) (D.map f'.unop)
    (c.π.app j.unop) (c.w f'.unop).symm F (D.map f.unop) (D.map (f'.unop ≫ f.unop))
    (D.map_comp _ _) (c.π.app i.unop) (c.w f.unop).symm

/-- The cocone of counits `p_i^* p_{i*} F ⟶ F` over `AlgebraicGeometry.Etale.descentDiagram`. -/
@[simps]
noncomputable def descentCocone : Cocone (descentDiagram A c F) where
  pt := F
  ι :=
    { app i := (upperStarLowerStarAdjunction A (c.π.app i.unop)).counit.app F
      naturality {i j} f := by simp }

end Diagram

end AlgebraicGeometry.Etale
