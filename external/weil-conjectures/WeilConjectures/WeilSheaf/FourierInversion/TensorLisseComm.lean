/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.IhomLisse.SwapWeil

/-!
# Tensor products of Weil complexes with lisse sheaves commute

Tensoring Weil complexes with two lisse Weil sheaves `G` and `H` does not depend on the order:
`G ⊗ (H ⊗ -) ≅ H ⊗ (G ⊗ -)` (`AlgebraicGeometry.WeilComplex.nonempty_iso_tensorLisse_comm`).
This follows from the swap `[G^∨, [H^∨, -]] ≅ [H^∨, [G^∨, -]]` of internal homs of pro-étale Weil
sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorCompIhomFunctorIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Tensoring with two lisse Weil sheaves commutes**: `G ⊗ (H ⊗ -) ≅ H ⊗ (G ⊗ -)`. -/
theorem WeilComplex.nonempty_iso_tensorLisse_comm {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (G H : WeilSheaf k₀ l X) (hG : G.IsLisse) (hH : H.IsLisse) :
    Nonempty (WeilComplex.tensorLisse G hG ⋙ WeilComplex.tensorLisse H hH ≅
      WeilComplex.tensorLisse H hH ⋙ WeilComplex.tensorLisse G hG) := by
  unfold WeilComplex.tensorLisse
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (G.dual hG).obj hG.dual
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (H.dual hH).obj hH.dual
  exact ⟨((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (WeilComplex.ihomLisseCompιIso _ hH.dual) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (WeilComplex.ihomLisseCompιIso _ hG.dual) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory _) _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorIsoMapDerivedCategory _) ≪≫
          Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (ProEtaleWeilSheaf.ihomFunctorCompIhomFunctorIso (H.dual hH).obj (G.dual hG).obj) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
          Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorIsoMapDerivedCategory _).symm ≪≫
          Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory _).symm _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (WeilComplex.ihomLisseCompιIso _ hH.dual).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (WeilComplex.ihomLisseCompιIso _ hG.dual).symm ≪≫
      (Functor.associator _ _ _).symm)⟩

end AlgebraicGeometry
