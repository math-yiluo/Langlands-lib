/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites

/-! # The projection compactification comparison predicates

Unchanged data interface extracted from FixProjectionCompactificationComparison so that
single-refinement steps can be stated independently of their common-refinement assembly.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.FixProjectionCompactification

/-- Package a given compactification with the identity base-change square. This selects
its projection from the recorded exchange/projection family without choosing any new map.
Source: prop-sf-pf-coherence.proof.md, chosen compactification
(blueprint: lem-fix-projection-compactification-comparison). -/
def identitySquare {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) : SixFunctorCompactifiedSquare D := by
  letI : LocallyOfFiniteType Y.obj.hom := Y.property.1
  letI : QuasiCompact Y.obj.hom := Y.property.2
  let Z : SixFunctorSpace D :=
    ⟨Over.mk (c.g ≫ Y.obj.hom),
      inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.obj.hom)),
      inferInstanceAs (QuasiCompact (c.g ≫ Y.obj.hom))⟩
  let i : X ⟶ Z := ObjectProperty.homMk
    (Over.homMk c.i (by
      change c.i ≫ c.g ≫ Y.obj.hom = X.obj.hom
      rw [← Category.assoc, ← c.comm]
      exact f.hom.w))
  let p : Z ⟶ Y := ObjectProperty.homMk (Over.homMk c.g rfl)
  have h : f = i ≫ p := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact c.comm
  exact
    { X := X, Y := Y, X' := X, Y' := Y, Z := Z, Z' := Z
      f := f, f' := f, g := 𝟙 Y, g' := 𝟙 X
      i := i, i' := i, p := p, p' := p, h := 𝟙 Z
      open_i := c.isOpenImmersion, open_i' := c.isOpenImmersion
      proper_p := c.isProper, proper_p' := c.isProper
      factorization := h, factorization' := h
      square := IsPullback.of_horiz_isIso ⟨by simp⟩
      properSquare := IsPullback.of_horiz_isIso ⟨by simp⟩
      openSquare := IsPullback.of_horiz_isIso ⟨by simp⟩
      squareComm := by simp, properComm := by simp, openComm := by simp }

/-- The displayed compactification comparison equation at a higher coefficient stage.
The tensor, projection and rho are all taken from the supplied normalized operation datum;
P is instantiated below with exactly the recorded finite-Tor domain at that stage.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison). -/
def higherLaw {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ Y, ObjectProperty (B Y)) : Prop :=
  ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
    (A (identitySquare f c₁)).projectionComponent K L ≫
        (S.comparison f c₁ c₂).hom.app
          (((T X).obj K).obj ((S.pull f).obj L)) =
      ((T Y).map ((S.comparison f c₁ c₂).hom.app K)).app L ≫
        (A (identitySquare f c₂)).projectionComponent K L

/-- The local comparison square for one proper refinement. Common refinements are
assembled from two such squares using the recorded comparison cocycle.
Source: prop-sf-pf-coherence.proof.md, compactification-independence calculation, step 5
(blueprint: def-sf-projection-single-refinement-law). -/
def refinementLaw {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ Y, ObjectProperty (B Y)) : Prop :=
  ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (_r : c.Refinement d) (K : B X) (L : B Y), P Y L →
    (A (identitySquare f c)).projectionComponent K L ≫
        (S.comparison f c d).hom.app
          (((T X).obj K).obj ((S.pull f).obj L)) =
      ((T Y).map ((S.comparison f c d).hom.app K)).app L ≫
        (A (identitySquare f d)).projectionComponent K L

/-- The finite-coefficient equation in fixed-scalar coordinates. The common-refinement
comparison is theta(d,c1) inverse followed by theta(d,c2), exactly as prescribed by
compactification_coherence. The retained target witness is transported by e; quantifying
over e keeps every presentation of the tensor object, rather than choosing an antecedent.
K is bounded constructible, and only L is required to have finite Tor amplitude.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison). -/
def finiteLaw (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (hl : IsUnit (C.l : D.k)) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ d : Compactification f) (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂)
    (O : RefinementFiniteLevelOrigin C.l E n hn X)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (OT : RefinementFiniteLevelOrigin C.l E n hn X),
    let K := refinementFiniteLevelFixedObject C.l E n hn X O
    let M := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    let T := ((derivedTensor M X).obj K).obj ((upperStar M f).leftDerivedFunctor.obj L)
    ∀ (e : refinementFiniteLevelFixedObject C.l E n hn X OT ≅ T),
    intrinsicFiniteTorsionConstructible C.l E n hn X
      ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing C.l E n)).functor.obj
        K) →
    finiteTorConstructible C.l E n hn Y
      ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing C.l E n)).functor.obj
        L) →
    let rhoK := (refinementComparisonIsomorphism D.k C.l hl E n hn f r₁ O).symm ≪≫
      refinementComparisonIsomorphism D.k C.l hl E n hn f r₂ O
    let rhoT := (rightDerivedLowerShriekOfCompactification M c₁).mapIso e.symm ≪≫
      (refinementComparisonIsomorphism D.k C.l hl E n hn f r₁ OT).symm ≪≫
      refinementComparisonIsomorphism D.k C.l hl E n hn f r₂ OT ≪≫
      (rightDerivedLowerShriekOfCompactification M c₂).mapIso e
    ((projectionMapOfCompactification M c₁).app K).app L ≫ rhoT.hom =
      ((derivedTensor M Y).map rhoK.hom).app L ≫
        ((projectionMapOfCompactification M c₂).app K).app L

end WeilConjectures.FixProjectionCompactification
