/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-! # The adjunction calculation behind the canonical representative square

Source: blueprint theorem-poincare-duality-frobenius--2, Step 5
(blueprint: lem-pod-tensor-roos-representative-square).

Two reduction/limit adjunctions, a limit comparison `δ` and a reduction comparison `a`
satisfying the transported unit and counit laws identify the coherent tensor arrow,
followed by the ordinary-to-completed maps, with the ordinary-to-completed map
followed by the counit-conjugated system tensor comparison.
-/

@[expose] public section

open CategoryTheory

namespace WeilConjectures

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {CY : Type u₁} {CX : Type u₂} {AY : Type u₃} {AX : Type u₄}
  [Category.{v₁} CY] [Category.{v₂} CX] [Category.{v₃} AY] [Category.{v₄} AX]

/-- One input factor of the representative square: the reduction comparison followed by
the reduction of the ordinary-to-completed map is the inverse target counit followed by the
reduction of the pullback model.
Source: blueprint theorem-poincare-duality-frobenius--2, Step 5. -/
theorem podMate_factor
    (F : CY ⥤ CX) (Pb : CY ⥤ CX) (V₁ V₂ : AY ⥤ AX) (j : V₂ ≅ V₁)
    {RY : CY ⥤ AY} {LY : AY ⥤ CY} (adjY : RY ⊣ LY)
    {RX : CX ⥤ AX} {LX : AX ⥤ CX} (adjX : RX ⊣ LX)
    (δ : LY ⋙ F ⟶ V₁ ⋙ LX) (a : RY ⋙ V₁ ≅ F ⋙ RX) (p : Pb ≅ RY ⋙ V₂ ⋙ LX)
    (hcounit : ∀ A : AY, a.inv.app (LY.obj A) ≫ V₁.map (adjY.counit.app A) =
      RX.map (δ.app A) ≫ adjX.counit.app (V₁.obj A))
    (M : CY) [IsIso (adjX.counit.app (V₂.obj (RY.obj M)))] :
    j.hom.app (RY.obj M) ≫ a.hom.app M ≫
        RX.map (F.map (adjY.unit.app M) ≫ δ.app (RY.obj M) ≫
          LX.map (j.inv.app (RY.obj M)) ≫ p.inv.app M) =
      inv (adjX.counit.app (V₂.obj (RY.obj M))) ≫ RX.map (p.inv.app M) := by
  have hε := adjX.counit.naturality (j.inv.app (RY.obj M))
  have ha := a.hom.naturality (adjY.unit.app M)
  have hc := hcounit (RY.obj M)
  have ht := adjY.left_triangle_components M
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hε ha hc ht
  have hk : j.hom.app (RY.obj M) ≫ a.hom.app M ≫ RX.map (F.map (adjY.unit.app M)) ≫
      RX.map (δ.app (RY.obj M)) ≫ RX.map (LX.map (j.inv.app (RY.obj M))) =
        inv (adjX.counit.app (V₂.obj (RY.obj M))) := by
    rw [← cancel_mono (adjX.counit.app (V₂.obj (RY.obj M))), IsIso.inv_hom_id]
    simp only [Category.assoc]
    rw [hε, ← Category.assoc (RX.map (δ.app _)), ← hc]
    simp only [Category.assoc]
    rw [← reassoc_of% ha]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]
    rw [ht]
    simp
  rw [RX.map_comp, RX.map_comp, RX.map_comp, ← hk]
  simp only [Category.assoc]
/-- The unit and counit bookkeeping on the source side: the ordinary-to-completed map of a
completed tensor, followed by the reduction of its tensor model and the source counit, is the
reindexed tensor model followed by the limit comparison.
Source: blueprint theorem-poincare-duality-frobenius--2, Step 5. -/
theorem podMate_source
    (F : CY ⥤ CX) (V₁ V₂ : AY ⥤ AX) (j : V₂ ≅ V₁)
    {RY : CY ⥤ AY} {LY : AY ⥤ CY} (adjY : RY ⊣ LY) {LX : AX ⥤ CX}
    (δ : LY ⋙ F ⟶ V₁ ⋙ LX) {T : CY} {U : AY} (d : T ⟶ LY.obj U) :
    F.map (adjY.unit.app T) ≫ δ.app (RY.obj T) ≫
        LX.map (j.inv.app (RY.obj T) ≫ V₂.map (RY.map d) ≫ V₂.map (adjY.counit.app U)) =
      F.map d ≫ δ.app U ≫ LX.map (j.inv.app U) := by
  have hj₁ := j.inv.naturality (RY.map d)
  have hj₂ := j.inv.naturality (adjY.counit.app U)
  have hδ₁ := δ.naturality (RY.map d)
  have hδ₂ := δ.naturality (adjY.counit.app U)
  have hη := adjY.unit.naturality d
  have ht := adjY.right_triangle_components U
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    at hj₁ hj₂ hδ₁ hδ₂ hη ht
  rw [← reassoc_of% hj₁, ← hj₂, LX.map_comp, LX.map_comp, ← reassoc_of% hδ₁,
    ← reassoc_of% hδ₂, ← F.map_comp_assoc, ← F.map_comp_assoc, ← hη, Category.assoc, ht,
    Category.comp_id]
/-- The representative square in adjunction form. The coherent tensor arrow `κ`,
followed by the tensor of the two ordinary-to-completed maps, is the ordinary-to-completed
map of the tensor followed by the counit-conjugated system tensor comparison.
Source: blueprint theorem-poincare-duality-frobenius--2, Step 5
(blueprint: lem-pod-tensor-roos-representative-square). -/
theorem podMate_square
    (F : CY ⥤ CX) (Pb : CY ⥤ CX) (V₁ V₂ : AY ⥤ AX) (j : V₂ ≅ V₁)
    {RY : CY ⥤ AY} {LY : AY ⥤ CY} (adjY : RY ⊣ LY)
    {RX : CX ⥤ AX} {LX : AX ⥤ CX} (adjX : RX ⊣ LX)
    (δ : LY ⋙ F ⟶ V₁ ⋙ LX) (a : RY ⋙ V₁ ≅ F ⋙ RX) (p : Pb ≅ RY ⋙ V₂ ⋙ LX)
    (hcounit : ∀ A : AY, a.inv.app (LY.obj A) ≫ V₁.map (adjY.counit.app A) =
      RX.map (δ.app A) ≫ adjX.counit.app (V₁.obj A))
    (TY : CY × CY ⥤ CY) (TX : CX × CX ⥤ CX) (SY : AY × AY ⥤ AY) (SX : AX × AX ⥤ AX)
    (dY : TY ≅ (RY.prod RY) ⋙ SY ⋙ LY) (dX : TX ≅ (RX.prod RX) ⋙ SX ⋙ LX)
    (σ : SY ⋙ V₂ ≅ (V₂.prod V₂) ⋙ SX)
    (o : ∀ K : CY, F.obj K ⟶ Pb.obj K)
    (ho : ∀ K : CY, o K = F.map (adjY.unit.app K) ≫ δ.app (RY.obj K) ≫
      LX.map (j.inv.app (RY.obj K)) ≫ p.inv.app K)
    (M N : CY) (hM : IsIso (adjX.counit.app (V₂.obj (RY.obj M))))
    (hN : IsIso (adjX.counit.app (V₂.obj (RY.obj N))))
    (w : V₁.obj (SY.obj (RY.obj M, RY.obj N)) ⟶
      SX.obj (V₁.obj (RY.obj M), V₁.obj (RY.obj N)))
    (hw : w = j.inv.app (SY.obj (RY.obj M, RY.obj N)) ≫ σ.hom.app (RY.obj M, RY.obj N) ≫
      SX.map (Prod.mkHom (j.hom.app (RY.obj M)) (j.hom.app (RY.obj N)))) :
    (F.map (dY.hom.app (M, N)) ≫ δ.app (SY.obj (RY.obj M, RY.obj N)) ≫ LX.map w ≫
        LX.map (SX.map (Prod.mkHom (a.hom.app M) (a.hom.app N))) ≫
        dX.inv.app (F.obj M, F.obj N)) ≫ TX.map (Prod.mkHom (o M) (o N)) =
      o (TY.obj (M, N)) ≫ (p.hom.app (TY.obj (M, N)) ≫
        LX.map (V₂.map (RY.map (dY.hom.app (M, N)))) ≫
        (LX.map (V₂.map (adjY.counit.app (SY.obj (RY.obj M, RY.obj N)))) ≫
        LX.map (σ.hom.app (RY.obj M, RY.obj N)) ≫
        LX.map (SX.map (Prod.mkHom (inv (adjX.counit.app (V₂.obj (RY.obj M))))
          (inv (adjX.counit.app (V₂.obj (RY.obj N))))))) ≫
        LX.map (SX.map (Prod.mkHom (RX.map (p.inv.app M)) (RX.map (p.inv.app N)))) ≫
        dX.inv.app (Pb.obj M, Pb.obj N)) := by
  have hd := dX.inv.naturality (Prod.mkHom (o M) (o N))
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.prod_obj, Functor.prod_map]
    at hd
  have hfM := podMate_factor F Pb V₁ V₂ j adjY adjX δ a p hcounit M
  have hfN := podMate_factor F Pb V₁ V₂ j adjY adjX δ a p hcounit N
  rw [← ho M] at hfM
  rw [← ho N] at hfN
  have hs := podMate_source F V₁ V₂ j adjY δ (dY.hom.app (M, N))
  rw [ho (TY.obj (M, N))]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← hd]
  have hs' := hs
  simp only [LX.map_comp, Functor.prod_obj] at hs'
  rw [reassoc_of% hs', hw]
  have hp : SX.map (Prod.mkHom (j.hom.app (RY.obj M)) (j.hom.app (RY.obj N))) ≫
      SX.map (Prod.mkHom (a.hom.app M) (a.hom.app N)) ≫
      SX.map (Prod.mkHom (RX.map (o M)) (RX.map (o N))) =
    SX.map (Prod.mkHom (inv (adjX.counit.app (V₂.obj (RY.obj M))))
        (inv (adjX.counit.app (V₂.obj (RY.obj N))))) ≫
      SX.map (Prod.mkHom (RX.map (p.inv.app M)) (RX.map (p.inv.app N))) := by
    simp only [← SX.map_comp, Prod.mkHom, prod_comp, hfM, hfN]
  have hp' := congrArg LX.map hp
  simp only [LX.map_comp] at hp'
  simp only [LX.map_comp, Category.assoc]
  rw [reassoc_of% hp']

end WeilConjectures
