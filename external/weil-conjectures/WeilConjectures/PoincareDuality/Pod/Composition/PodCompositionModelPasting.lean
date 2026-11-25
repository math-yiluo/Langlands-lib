/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.CategoryTheory.Slice

/-! # Pasting normalized comparison models -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace WeilConjectures

/-- A commuting triangle of models gives composition for the original comparisons.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 0941
(blueprint: lem-pod-composition-model-pasting).

Proof: postcompose with the two successive representative isomorphisms and the
final model isomorphism. Naturality moves the first representative across the
second comparison. Substitute its model formula and then the first model formula.
Naturality of the ordinary compositor moves the initial model to the front.
The strict composition equation and the composite model formula give the other
path; naturality of the final model and the representative compositor finish.
All postcomposed factors are isomorphisms, so cancellation proves the equality. -/
theorem podCompositionModelPasting
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {H : C₀ ⥤ C₂}
    {S : D₀ ⥤ D₁} {T : D₁ ⥤ D₂} {U : D₀ ⥤ D₂}
    {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂}
    (bF : R₀ ⋙ F ⟶ S ⋙ R₁) (bG : R₁ ⋙ G ⟶ T ⋙ R₂)
    (bH : R₀ ⋙ H ⟶ U ⋙ R₂) (k : H ⟶ F ⋙ G) (s : U ⟶ S ⋙ T)
    (x : D₀) (y : D₁) (z w : D₂)
    (sf : S.obj x ⟶ y) (th : T.obj y ⟶ z) (cc : U.obj x ⟶ w)
    (sc : w ⟶ z) [IsIso sf] [IsIso th]
    (v₀ : C₀) (v₁ : C₁) (v₂ v₃ : C₂)
    (r₀ : R₀.obj x ≅ v₀) (r₁ : R₁.obj y ≅ v₁)
    (r₂ : R₂.obj z ≅ v₂) (rc : R₂.obj w ≅ v₃)
    (mF : F.obj v₀ ⟶ v₁) (mG : G.obj v₁ ⟶ v₂)
    (mH : H.obj v₀ ⟶ v₃) (ms : v₃ ⟶ v₂)
    (hs : s.app x ≫ T.map sf ≫ th = cc ≫ sc)
    (hr : R₂.map sc ≫ r₂.hom = rc.hom ≫ ms)
    (hf : F.map r₀.hom ≫ mF = bF.app x ≫ R₁.map sf ≫ r₁.hom)
    (hg : G.map r₁.hom ≫ mG = bG.app y ≫ R₂.map th ≫ r₂.hom)
    (hc : H.map r₀.hom ≫ mH = bH.app x ≫ R₂.map cc ≫ rc.hom)
    (hm : k.app v₀ ≫ G.map mF ≫ mG = mH ≫ ms) :
    k.app (R₀.obj x) ≫ G.map (bF.app x) ≫ bG.app (S.obj x) =
      bH.app x ≫ R₂.map (s.app x) := by
  apply (cancel_mono (R₂.map (T.map sf) ≫ R₂.map th ≫ r₂.hom)).1
  simp only [Category.assoc]
  calc
    _ = k.app (R₀.obj x) ≫ G.map (bF.app x) ≫
        G.map (R₁.map sf) ≫ bG.app y ≫ R₂.map th ≫ r₂.hom := by
      have hn := bG.naturality sf
      change G.map (R₁.map sf) ≫ bG.app y =
        bG.app (S.obj x) ≫ R₂.map (T.map sf) at hn
      rw [← reassoc_of% hn]
    _ = k.app (R₀.obj x) ≫
        G.map (bF.app x ≫ R₁.map sf ≫ r₁.hom) ≫ mG := by
      rw [← hg]
      simp only [Functor.map_comp, Category.assoc]
    _ = k.app (R₀.obj x) ≫ G.map (F.map r₀.hom) ≫ G.map mF ≫ mG := by
      rw [← hf, Functor.map_comp, Category.assoc]
    _ = H.map r₀.hom ≫ k.app v₀ ≫ G.map mF ≫ mG := by
      have hn := k.naturality r₀.hom
      change H.map r₀.hom ≫ k.app v₀ =
        k.app (R₀.obj x) ≫ G.map (F.map r₀.hom) at hn
      rw [← reassoc_of% hn]
    _ = H.map r₀.hom ≫ mH ≫ ms := by rw [hm]
    _ = bH.app x ≫ R₂.map cc ≫ rc.hom ≫ ms := by rw [← Category.assoc, hc]; simp
    _ = bH.app x ≫ R₂.map (cc ≫ sc) ≫ r₂.hom := by
      rw [← hr, Functor.map_comp, Category.assoc]
    _ = _ := by rw [← hs]; simp only [Functor.map_comp, Category.assoc]

end WeilConjectures
