/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import WeilConjectures.Mathlib.Topology.Separation.Hausdorff

/-!
# Pullbacks

Ported from the `proetale` package (`Proetale.Mathlib.Topology.Category.TopCat.Limits.Pullbacks`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

lemma TopCat.prodFst_apply {X Y : TopCat.{u}} (x : X × Y) : TopCat.prodFst x = x.1 := by
  rfl

lemma TopCat.prodSnd_apply {X Y : TopCat.{u}} (x : X × Y) : TopCat.prodSnd x = x.2 := by
  rfl

-- use the following lemma: `t2Space_iff_diagonal_closed`
-- after `TopCat.isEmbedding_pullback_to_prod`
@[stacks 08ZH]
theorem TopCat.isClosedEmbedding_pullback_to_prod {X Y Z : TopCat.{u}} [T2Space Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    Topology.IsClosedEmbedding ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) := by
  refine ⟨isEmbedding_pullback_to_prod f g, ?_⟩
  suffices s1 : Set.range (prod.lift (pullback.fst f g) (pullback.snd f g)) =
      (homeoOfIso (prodIsoProd X Y)) ⁻¹' (Prod.map f.hom g.hom ⁻¹' Set.diagonal Z) by
    rw [s1, (TopCat.homeoOfIso (TopCat.prodIsoProd X Y)).isClosed_preimage]
    exact .preimage (.prodMap (map_continuous f.hom) (map_continuous g.hom))
      (t2_iff_isClosed_diagonal.mp ‹T2Space Z›)
  ext x
  simp only [Set.mem_range, Set.mem_preimage, Set.mem_diagonal_iff, Prod.map_fst,
    Prod.map_snd]
  constructor
  · rintro ⟨a, rfl⟩
    rw [← TopCat.prodFst_apply, ← TopCat.prodSnd_apply, homeoOfIso_apply]
    simp only [← ConcreteCategory.comp_apply]
    simp [pullback.condition]
  · intro ha
    -- TODO: replace this by `range_pullback_to_prod` after updating mathlib
    use (pullbackIsoProdSubtype f g).inv ⟨(X.prodIsoProd Y).hom x , ha⟩
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩ <;>
       rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, limit.lift_π] <;>
        -- This used to be `simp` before https://github.com/leanprover/lean4/pull/2644
    cat_disch
