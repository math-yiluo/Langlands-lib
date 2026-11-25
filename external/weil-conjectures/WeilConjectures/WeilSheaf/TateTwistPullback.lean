/-
Copyright (c) 2026 The Weil Conjectures Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil Conjectures Contributors
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse

/-!
# Pullback and Tate twists of Weil complexes

The Tate twist is a constant scalar twist on the derived category of pro-étale Weil
sheaves. Its compatibility with pullback therefore restricts to Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]

/-- Pullback of Weil complexes commutes with Tate twists. -/
noncomputable def tateTwistCompUpperStarIso (m : ℤ) :
    tateTwist k₀ l Y m ⋙ upperStar f ≅ upperStar f ⋙ tateTwist k₀ l X m := by
  let eU : upperStar (k₀ := k₀) (l := l) f ⋙ (objectProperty k₀ l X).ι ≅
      (objectProperty k₀ l Y).ι ⋙ (ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory :=
    ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  refine ((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso ?_
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tateTwist k₀ l Y m) eU ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tateTwistCompιIso m) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompUpperStarIso k₀ l f _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eU.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (tateTwistCompιIso m).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Pullback of Weil complexes commutes with a Tate twist followed by a shift. -/
noncomputable def tateTwistShiftCompUpperStarIso (m n : ℤ) :
    (tateTwist k₀ l Y m ⋙ shiftFunctor (WeilComplex k₀ l Y) n) ⋙ upperStar f ≅
      upperStar f ⋙ tateTwist k₀ l X m ⋙ shiftFunctor (WeilComplex k₀ l X) n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((upperStar f).commShiftIso n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tateTwistCompUpperStarIso f m) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.WeilComplex
