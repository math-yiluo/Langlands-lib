/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalRefinementMate

/-! # Inputs and left comparisons for normalized coefficient assembly

The coefficient-stage records retain the literal rational object and localized integral-arrow
normalizations and the closed functor action on representative arrows. The additional
normalization below records the shift and transition properties used for refinement descent. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The inherited shift on the full ring-stage inclusion.
Source: full coefficient subcategories in the exceptional construction
(blueprint: def-sf-constructible-exceptional-assembly-data). -/
@[instance_reducible]
def constructionInclusionShift (T : Scheme.{max u v}) (s : RingStage.{max u v} l) :
    (RingStage.inclusion.{u, v} l Ω T s).CommShift ℤ :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance

attribute [local instance] constructionInclusionShift

variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Additional normalizations retained before constructing refinement comparisons.
The ring realizations preserve the inherited shifts. Scalar shifts are chosen independently
of compactification, and raw rationalization preserves the represented left object literally.
The closed-stage left functor sends the common-stage transition isomorphisms to the
rational scalar q: the closed category is the pair category, whose arrows between
different finite stages are not images of one stage inclusion, so without this field the
closed functors of two compactifications could differ by a stage-dependent sign twist
on such arrows and no natural refinement map would exist.
These are properties of the chosen stage data, not refinement maps or refinement existence.
Source: Zheng 5.22 and raw localization; exceptional construction steps 3--5
(blueprint: def-sf-constructible-exceptional-assembly-data). -/
structure CoefficientConstructionNormalization
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F) : Prop where
  leftShift (c : Compactification f) (s : RingStage.{max u v} l) :
    (R.left c s).hom.CommShift ℤ
  localizationShiftX (c d : Compactification f) (E : FieldStage.{max u v} l) :
    (F.rationalizationComparison c E).shiftX = (F.rationalizationComparison d E).shiftX
  localizationShiftY (c d : Compactification f) (E : FieldStage.{max u v} l) :
    (F.rationalizationComparison c E).shiftY = (F.rationalizationComparison d E).shiftY
  localizationIdentity (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((F.rationalizationComparison c E).q.hom.app K)
      (𝟙 ((rationalization.{u, v} l Ω E Y).obj ((R.operation c (.integral E)).F.obj K)))
  commonShiftX (c d : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    (M.commonComparison c i).shiftX = (M.commonComparison d i).shiftX
  commonShiftY (c d : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    (M.commonComparison c i).shiftY = (M.commonComparison d i).shiftY
  commonTransitionNatural (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (M.commonComparison c i).q.hom.app K ≫
        (R.operation c .closed).F.map ((commonTransition.{u, v} l Ω X i j h).inv.app K) =
      (commonTransition.{u, v} l Ω Y i j h).inv.app
          ((R.operation c (.rational (commonField.{u, v} l Ω i))).F.obj K) ≫
        (commonInclusion.{u, v} l Ω Y j).map
          ((F.rationalComparison c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q.hom.app K) ≫
        (M.commonComparison c j).q.hom.app
          ((rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X).obj K)

/-- Only the left geometric refinement maps, with their realization and descent equations.
The right maps in the normalization predicate are the explicit adjunction conjugates;
no right comparison, unit equation, or counit equation is assumed as input data.
Source: proper/open refinement, raw localization, and common-field descent
(blueprint: def-sf-constructible-exceptional-assembly-data). -/
structure CoefficientLeftRefinements
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F) where
  left {c d : Compactification f} (r : c.Refinement d) (s : Stage.{max u v} l) :
    (R.operation c s).F ≅ (R.operation d s).F
  leftShift {c d : Compactification f} (r : c.Refinement d) (s : Stage.{max u v} l) :
    (left r s).hom.CommShift ℤ
  normalized {c d : Compactification f} (r : c.Refinement d) (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (R.left c s) (R.left d s)
      (refinementComparisonOfLeft.{u, v} l Ω (R.operation c (s.stage l))
        (R.operation d (s.stage l)) (left r (s.stage l)) (leftShift r (s.stage l)))
  rational {c d : Compactification f} (r : c.Refinement d) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((left r (.rational E)).hom.app ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω E Y).map ((left r (.integral E)).hom.app K))
  common {c d : Compactification f} (r : c.Refinement d)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (M.commonComparison c i).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y i).map
          ((left r (.rational (commonField.{u, v} l Ω i))).hom.app K) ≫
        (M.commonComparison d i).q.hom.app K =
      (left r .closed).hom.app ((commonInclusion.{u, v} l Ω X i).obj K)

end WeilConjectures.ConstructibleExceptionalCoefficients
