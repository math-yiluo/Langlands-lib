/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import all WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction

/-! # The perfect-quotient projection formula in the completed coefficient presentation

Source: Zheng, Proposition 4.21; Stacks 0944 and 099N;
Bhatt--Scholze, Lemma 6.5.11(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical projection-formula map, obtained by transposing direct image of
 the actual scalar unit through the normalized restriction comparison.
Source: Stacks 07A6 and 0944
(blueprint: lem-weil-completed-direct-image-finite-projection). -/
def completedDirectImageFiniteProjection {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (scalarReductionDerivedExtension l E Y n).obj
        ((sfCompletedDerivedDirectImage l E f).obj K) ⟶ sfFiniteDerivedDirectImage l E f K n :=
  ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    ((sfCompletedDerivedDirectImage l E f).map ((sfDerivedReductionUnit l E X n).app K) ≫
      (sfDerivedRestrictionComparison l E f n).hom.app
        ((scalarReductionDerivedExtension l E X n).obj K))

/-- Each positive quotient is perfect over the completed coefficient ring, so the
canonical finite projection formula is invertible on every unbounded complex.
Source: Zheng, Proposition 4.21; Stacks 0944 and 099N;
Bhatt--Scholze, Lemma 6.5.11(3).
(blueprint: lem-weil-completed-direct-image-finite-projection).

Proof: use the two-term free uniformizer resolution of the quotient. The existing
completed direct-image proof transports the perfect projection formula across the
coefficient-presentation isomorphisms, retaining the scalar adjunction and the
K-injective unit normalization. Its sf_projection_formula proves invertibility of
exactly the arrow defined here. There is no completeness or boundedness assumption
on K, and the proof includes n = 0, zero complexes and empty schemes. -/
theorem completedDirectImageFiniteProjection_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) (K : DerivedCategory (scalarReductionSource l E X)) :
    IsIso (completedDirectImageFiniteProjection l E f n K) := by
  exact sf_projection_formula l E f n K

end WeilConjectures
