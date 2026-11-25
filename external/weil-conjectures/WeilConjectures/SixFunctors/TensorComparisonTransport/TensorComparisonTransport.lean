/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.CategoryTheory.Slice
/-! # Transport of tensor-composition coherence along natural isomorphisms
Source: the naturality and inverse-compositor cancellation in Stacks 07A4 and 07A7. -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
namespace WeilConjectures.TensorComparisonTransport
private theorem mkHom_comp {C D : Type*} [Category C] [Category D]
    {X₁ X₂ X₃ : C} {Y₁ Y₂ Y₃ : D}
    (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃) (g : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) :
    Prod.mkHom (f ≫ f') (g ≫ g') = Prod.mkHom f g ≫ Prod.mkHom f' g' := rfl

/-- Tensor-composition coherence is invariant under compatible isomorphisms of the
three pullback functors and their tensor comparisons.
Source: naturality and categorical cancellation, Stacks 07A4 and 07A7
(blueprint: lem-sf-tensor-comparison-transport).
Proof: whisker the first two functor isomorphisms to obtain D : F⋙G ≅ F'⋙G'.
Naturality of the second tensor comparison, the two individual comparison squares,
and naturality of the second functor isomorphism give the composite comparison square.
Postcompose the desired equation with the tensor square of D followed by the ambient
compositor. This is invertible. The compositor-identification square and ambient
coherence turn both sides into the third individual comparison square. Cancel the
invertible postcomposition. -/
theorem transfer_tensor_composition
    {A B C : Type*} [Category A] [Category B] [Category C]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (F F' : A ⥤ B) (G G' : B ⥤ C) (H H' : A ⥤ C)
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H')
    (mF : TA ⋙ F ≅ F.prod F ⋙ TB) (mG : TB ⋙ G ≅ G.prod G ⋙ TC)
    (mH : TA ⋙ H ≅ H.prod H ⋙ TC)
    (nF : TA ⋙ F' ≅ F'.prod F' ⋙ TB) (nG : TB ⋙ G' ≅ G'.prod G' ⋙ TC)
    (nH : TA ⋙ H' ≅ H'.prod H' ⋙ TC)
    (a : H ≅ F ⋙ G) (b : F' ⋙ G' ≅ H')
    (hmF : ∀ M N, eF.hom.app (TA.obj (M, N)) ≫ nF.hom.app (M, N) =
      mF.hom.app (M, N) ≫ TB.map
        (Prod.mkHom (eF.hom.app M) (eF.hom.app N)))
    (hmG : ∀ M N, eG.hom.app (TB.obj (M, N)) ≫ nG.hom.app (M, N) =
      mG.hom.app (M, N) ≫ TC.map
        (Prod.mkHom (eG.hom.app M) (eG.hom.app N)))
    (hmH : ∀ M N, eH.hom.app (TA.obj (M, N)) ≫ nH.hom.app (M, N) =
      mH.hom.app (M, N) ≫ TC.map
        (Prod.mkHom (eH.hom.app M) (eH.hom.app N)))
    (ha : ∀ M, a.hom.app M ≫ eG.hom.app (F.obj M) ≫
      G'.map (eF.hom.app M) = eH.hom.app M ≫ b.inv.app M)
    (hc : ∀ M N, G'.map (nF.hom.app (M, N)) ≫
      nG.hom.app (F'.obj M, F'.obj N) ≫
      TC.map (Prod.mkHom (b.hom.app M) (b.hom.app N)) =
      b.hom.app (TA.obj (M, N)) ≫ nH.hom.app (M, N)) :
    ∀ M N, a.hom.app (TA.obj (M, N)) ≫ G.map (mF.hom.app (M, N)) ≫
      mG.hom.app (F.obj M, F.obj N) = mH.hom.app (M, N) ≫
      TC.map (Prod.mkHom (a.hom.app M) (a.hom.app N)) := by
  let D : F ⋙ G ≅ F' ⋙ G' := isoWhiskerLeft F eG ≪≫ isoWhiskerRight eF G'
  let d : F ⋙ G ≅ H' := D ≪≫ b
  have had (M : A) : a.hom.app M ≫ d.hom.app M = eH.hom.app M := by
    dsimp only [d, D, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app]
    simp only [Category.assoc]
    slice_lhs 1 3 => rw [ha]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have htr (M N : A) :
      G.map (mF.hom.app (M, N)) ≫ mG.hom.app (F.obj M, F.obj N) ≫
        TC.map (Prod.mkHom (D.hom.app M) (D.hom.app N)) =
      D.hom.app (TA.obj (M, N)) ≫ G'.map (nF.hom.app (M, N)) ≫
        nG.hom.app (F'.obj M, F'.obj N) := by
    have hn := nG.hom.naturality
      (Prod.mkHom (eF.hom.app M) (eF.hom.app N))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    dsimp only [D, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app]
    rw [mkHom_comp, TC.map_comp]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [← hmG]
    slice_lhs 1 2 => erw [eG.hom.naturality (mF.hom.app (M, N))]
    slice_lhs 3 4 => rw [← hn]
    slice_lhs 2 3 => rw [← G'.map_comp, ← hmF, G'.map_comp]
    simp only [Category.assoc, Functor.comp_obj]
  intro M N
  have : IsIso (Prod.mkHom (d.hom.app M) (d.hom.app N)) :=
    (isIso_prod_iff C C).2 ⟨inferInstance, inferInstance⟩
  apply (cancel_mono (TC.map (Prod.mkHom (d.hom.app M) (d.hom.app N)))).1
  calc
    _ = a.hom.app (TA.obj (M, N)) ≫
        (G.map (mF.hom.app (M, N)) ≫ mG.hom.app (F.obj M, F.obj N) ≫
          TC.map (Prod.mkHom (D.hom.app M) (D.hom.app N))) ≫
        TC.map (Prod.mkHom (b.hom.app M) (b.hom.app N)) := by
      simp only [d, Iso.trans_hom, NatTrans.comp_app, mkHom_comp,
        TC.map_comp, Category.assoc]
    _ = a.hom.app (TA.obj (M, N)) ≫ D.hom.app (TA.obj (M, N)) ≫
        (G'.map (nF.hom.app (M, N)) ≫ nG.hom.app (F'.obj M, F'.obj N) ≫
          TC.map (Prod.mkHom (b.hom.app M) (b.hom.app N))) := by
      rw [htr]
      simp only [Category.assoc]
    _ = eH.hom.app (TA.obj (M, N)) ≫ nH.hom.app (M, N) := by
      rw [hc]
      dsimp only [D, Iso.trans_hom, NatTrans.comp_app,
        isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app]
      simp only [Category.assoc]
      slice_lhs 1 3 => rw [ha]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    _ = mH.hom.app (M, N) ≫ TC.map
        (Prod.mkHom (eH.hom.app M) (eH.hom.app N)) := hmH M N
    _ = _ := by
      rw [← had M, ← had N, mkHom_comp, TC.map_comp]
      simp only [Category.assoc]

end WeilConjectures.TensorComparisonTransport
