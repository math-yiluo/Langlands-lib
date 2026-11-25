/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates

/-! # Compact-support projection comparison equations

Source: the coherence paragraph of the projection-formula proof in
literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done.
(blueprint: def-sf-projection-comparison-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

/-- The four comparison equations for the specified projection, without an
invertibility or naturality assertion. These are precisely the corresponding
fields of `CompactSupportProjectionLaws`, with the same second-input predicate.
Source: fix-prop-projection-formula.proof.md, final coherence sentence.
(blueprint: def-sf-projection-comparison-equations). -/
structure CompactSupportProjectionCoherence {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ X, ObjectProperty (B X)) : Prop where
  compactification : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
      ((T Y).map ((S.comparison f c d).hom.app K)).app L ≫
          compactSupportProjectionComponent A f d K L =
        compactSupportProjectionComponent A f c K L ≫
          (S.comparison f c d).hom.app (((T X).obj K).obj ((S.pull f).obj L))
  composition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) (L : B Z), P Z L →
      ((T Z).map ((S.composition f g cf cg cfg).hom.app K)).app L ≫
          compactSupportProjectionComponent A g cg ((S.support f cf).obj K) L ≫
          (S.support g cg).map
            (compactSupportProjectionComponent A f cf K ((S.pull g).obj L)) =
        compactSupportProjectionComponent A (f ≫ g) cfg K L ≫
          (S.composition f g cf cg cfg).hom.app
            (((T X).obj K).obj ((S.pull (f ≫ g)).obj L)) ≫
          (S.support g cg).map ((S.support f cf).map
            (((T X).obj K).map ((S.pullComposition f g).hom.app L)))
  pentagon : ∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : B X),
    HEq ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K))
      ((S.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K))
  proper : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
      ((T Y).map ((S.properIdentification f c).hom.app K)).app L ≫
          compactSupportProperProjection A f K L =
        compactSupportProjectionComponent A f c K L ≫
          (S.properIdentification f c).hom.app
            (((T X).obj K).obj ((S.pull f).obj L))

end WeilConjectures
