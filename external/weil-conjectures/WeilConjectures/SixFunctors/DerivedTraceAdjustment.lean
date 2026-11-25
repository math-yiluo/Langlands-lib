/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # Adjustment of a transported trace by a coefficient automorphism -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem adjust_trace
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P : D ⥤ E) (Q : C ⥤ E) (c : F ⋙ P ≅ Q)
    {B : C} {L : D} (b : L ≅ F.obj B) (s : F.obj B ≅ L) (a : B ≅ B)
    (ha : F.map a.hom = b.inv ≫ s.inv) :
    Q.map a.hom ≫ c.inv.app B ≫ P.map s.hom = c.inv.app B ≫ P.map b.inv := by
  rw [c.inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [← P.map_comp, ha]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem transport_trace_shape
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P : D ⥤ E) (Q : C ⥤ E) (c : F ⋙ P ≅ Q)
    {B V : C} {L : D} (v : V ≅ B) (z : F.obj V ≅ L)
    {W U U' : E} (lead : W ⟶ Q.obj B) (trace : P.obj L ⟶ U) (j : U ⟶ U') :
    lead ≫ Q.map v.inv ≫ c.inv.app V ≫ P.map z.hom ≫ trace ≫ j =
      lead ≫ c.inv.app B ≫ P.map ((F.mapIso v.symm ≪≫ z).hom) ≫ trace ≫ j := by
  rw [c.inv.naturality_assoc]
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]

private theorem normalize_trace_generic
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F Q : C ⥤ E) (r : F ≅ Q) (H : C ⥤ D) [H.IsEquivalence]
    (P : D ⥤ E) (c : H ⋙ P ≅ Q) {B : C} {L : D}
    (b : L ≅ H.obj B) (s : H.obj B ≅ L)
    {U V : E} (trace : P.obj L ⟶ U) (j : U ⟶ V) :
    ∃ a : B ≅ B,
      F.map a.hom ≫ (r.hom.app B ≫ c.inv.app B ≫ P.map s.hom ≫ trace ≫ j) =
        r.hom.app B ≫ (c.inv.app B ≫ P.map b.inv ≫ trace) ≫ j := by
  let a : B ≅ B := H.preimageIso (b.symm ≪≫ s.symm)
  have ha : H.map a.hom = b.inv ≫ s.inv := by
    simp only [a, Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom, Iso.symm_hom]
  refine ⟨a, ?_⟩
  rw [r.hom.naturality_assoc]
  rw [reassoc_of% (adjust_trace H P Q c b s a ha)]
  simp only [Category.assoc]

private theorem normalize_raw_trace
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F Q : C ⥤ E) (r : F ≅ Q) (H : C ⥤ D) [H.IsEquivalence]
    (P : D ⥤ E) (c : H ⋙ P ≅ Q) {B V : C} {L : D}
    (b : L ≅ H.obj B) (v : V ≅ B) (z : H.obj V ≅ L)
    {U W : E} (trace : P.obj L ⟶ U) (j : U ⟶ W) :
    ∃ a : B ≅ B,
      F.map a.hom ≫ (r.hom.app B ≫ Q.map v.inv ≫ c.inv.app V ≫
        P.map z.hom ≫ trace ≫ j) =
      r.hom.app B ≫ (c.inv.app B ≫ P.map b.inv ≫ trace) ≫ j := by
  obtain ⟨a, ha⟩ := normalize_trace_generic F Q r H P c b (H.mapIso v.symm ≪≫ z) trace j
  refine ⟨a, ?_⟩
  exact (congrArg (F.map a.hom ≫ ·)
    (transport_trace_shape H P Q c v z (r.hom.app B) trace j)).trans ha

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory

private theorem compOfEq_inv_eq
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (rightDerivedLowerStarCompOfEq C f g h w).inv.app K =
      (rightDerivedLowerStarCongr C w).inv.app K ≫
        (rightDerivedLowerStarComp C f g).inv.app K := by
  subst w
  rw [rightDerivedLowerStarCongr_refl, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  rfl

/-- Two isomorphisms identifying the coefficient after an equivalence give traces related
by an automorphism of that coefficient.

Source: blueprint latest, `thm-amb-p1-adjunction.proof.md`, transport through a presentation.
(auxiliary; not a blueprint node)

Proof: direct image along f is an equivalence, so lift the discrepancy b⁻¹ s⁻¹ uniquely
back to an automorphism of B. Naturality of composition and of the comparison r moves
this automorphism across both comparisons. Its image cancels s, leaving b⁻¹. For an
equality of geometric composites, eliminate the equality and apply this categorical
calculation to the canonical pushforward composition isomorphism. No property of the
trace itself is required. -/
theorem exists_derivedTraceAdjustment
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    [(lowerStar C f).rightDerivedFunctor.IsEquivalence]
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (r : F ≅ (lowerStar C h).rightDerivedFunctor)
    {B V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)}
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)}
    (b : L ≅ (lowerStar C f).rightDerivedFunctor.obj B)
    (v : V ≅ B) (z : (lowerStar C f).rightDerivedFunctor.obj V ≅ L)
    {U W : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)}
    (trace : (lowerStar C g).rightDerivedFunctor.obj L ⟶ U) (j : U ⟶ W) :
    ∃ a : B ≅ B,
      F.map a.hom ≫ (r.hom.app B ≫ (lowerStar C h).rightDerivedFunctor.map v.inv ≫
        (rightDerivedLowerStarCompOfEq C f g h w).inv.app V ≫
        (lowerStar C g).rightDerivedFunctor.map z.hom ≫ trace ≫ j) =
      r.hom.app B ≫ ((rightDerivedLowerStarCongr C w).inv.app B ≫
        (rightDerivedLowerStarComp C f g).inv.app B ≫
        (lowerStar C g).rightDerivedFunctor.map b.inv ≫ trace) ≫ j := by
  obtain ⟨a, ha⟩ := normalize_raw_trace F (lowerStar C h).rightDerivedFunctor r
    (lowerStar C f).rightDerivedFunctor (lowerStar C g).rightDerivedFunctor
    (rightDerivedLowerStarCompOfEq C f g h w) b v z trace j
  refine ⟨a, ?_⟩
  apply ha.trans
  simpa only [Category.assoc] using
    congrArg (fun k ↦ r.hom.app B ≫
      (k ≫ (lowerStar C g).rightDerivedFunctor.map b.inv ≫ trace) ≫ j)
        (compOfEq_inv_eq C f g h w B)

end AlgebraicGeometry.Etale
