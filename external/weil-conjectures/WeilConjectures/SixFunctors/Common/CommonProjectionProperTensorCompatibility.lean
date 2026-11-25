/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionCoefficientTransport.RationalProjectionTensorCompatibility
import WeilConjectures.SixFunctors.Common.CommonProjectionProperFactor
import WeilConjectures.SixFunctors.Common.CommonProjectionOpenFactor
import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackTensorCompatibility

/-! # Coefficient comparison of individual common-stage projection maps

Source: thm-sf-pf-field.proof.md, Compatibility and the common coefficient-field paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures
open ProjectionCoefficientTransport

private theorem normalizedProperProjection
    {A : Type v} [Category.{w} A] {B : Type v'} [Category.{w'} B]
    {F F₀ : B ⥤ A} {G G₀ : A ⥤ B}
    {TX TX₀ : A ⥤ A ⥤ A} {TY TY₀ : B ⥤ B ⥤ B}
    (adj : F ⊣ G) (adj₀ : F₀ ⊣ G₀)
    (mu : (Functor.postcompose₂.obj F₀).obj TY₀ ≅
      (((Functor.whiskeringLeft₂ _).obj F₀).obj F₀).obj TX₀)
    (hF : F₀ = F) (hG : G₀ = G) (hX : TX₀ = TX) (hY : TY₀ = TY)
    (ha : HEq adj₀ adj) (K : A) (L : B) :
    eqToHom (by rw [hG, hY]) ≫
        ((adj₀.rightAdjointProjectionMap mu.hom).app K).app L ≫
        eqToHom (by rw [hF, hG, hX]) =
      ((adj.rightAdjointProjectionMap
        (projectionTransportTensorComparison hF hX hY mu).hom).app K).app L := by
  subst F₀ G₀ TX₀ TY₀
  cases eq_of_heq ha
  simp [projectionTransportTensorComparison]

private theorem properProjection_normalized
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : B X) (L : B Y) :
    compactSupportProperProjection A f K L =
      (((S.pullDirectAdjunction f).rightAdjointProjectionMap
        (projectionPullbackTensor (A (compactSupportProperSquare f))).hom).app K).app L := by
  unfold compactSupportProperProjection projectionPullbackTensor
  exact normalizedProperProjection (S.pullDirectAdjunction f)
      (A (compactSupportProperSquare f)).stage.properAdjunction
      (A (compactSupportProperSquare f)).stage.tensorPullback
      (A (compactSupportProperSquare f)).properPull
      (A (compactSupportProperSquare f)).properPush
      (A (compactSupportProperSquare f)).tensorBar
      (A (compactSupportProperSquare f)).tensorY
      (A (compactSupportProperSquare f)).properAdjunction K L

private theorem adjunctionComparison_mate
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    {adj : F ⊣ G} {adj' : F' ⊣ G'} {V : A ⥤ A'} {W : B ⥤ B'}
    (C : CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison
      adj adj' V W) (M : B) :
    (mateEquiv adj adj' C.left.inv).app M = C.right.hom.app M := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact (mateEquiv_counit adj adj' C.left.inv M).trans (C.counit M).symm

private theorem properMate_preserved
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category* (B X)]
    {B' : SixFunctorSpace D → Type*} [∀ X, Category* (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {V : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q)
    (hφ : Adjunction.ComparisonCompatible (C.directAdjunction Q.p).left.symm
      (projectionPullbackTensor A).hom (projectionPullbackTensor A').hom
      (projectionCurriedTensorComparison (V Q.Z) (T Q.Z) (T' Q.Z) (t Q.Z))
      (projectionCurriedTensorComparison (V Q.Y) (T Q.Y) (T' Q.Y) (t Q.Y)))
    (M : B Q.Z) (N : B Q.Y) :
    (V Q.Y).map
        ((((S.pullDirectAdjunction Q.p).rightAdjointProjectionMap
          (projectionPullbackTensor A).hom).app M).app N) ≫
      (properTarget C t Q.p M N).hom =
    (properSource C t Q.p M N).hom ≫
      (((S'.pullDirectAdjunction Q.p).rightAdjointProjectionMap
        (projectionPullbackTensor A').hom).app ((V Q.Z).obj M)).app ((V Q.Y).obj N) := by
  have h := Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv
    (S.pullDirectAdjunction Q.p) (S'.pullDirectAdjunction Q.p) hφ M N
  simp only [Iso.symm_hom, Iso.symm_inv, adjunctionComparison_mate] at h
  simpa [properTarget, properSource, ProjectionCoefficientTransport.inner,
    projectionCurriedTensorComparison, Functor.uncurry, Category.assoc] using h

private theorem properProjection_preserved
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category* (B X)]
    {B' : SixFunctorSpace D → Type*} [∀ X, Category* (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {V : ∀ X, B X ⥤ B' X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (A' : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S' T' Q)
    (C : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (hφ : projectionTensorComparisonCompatible C t
      (A (compactSupportProperSquare f)) (A' (compactSupportProperSquare f)))
    (K : B X) (L : B Y) :
    (V Y).map (compactSupportProperProjection A f K L) ≫
        (properTarget C t f K L).hom =
      (properSource C t f K L).hom ≫
        compactSupportProperProjection A' f ((V X).obj K) ((V Y).obj L) := by
  rw [properProjection_normalized, properProjection_normalized]
  exact properMate_preserved C t (A (compactSupportProperSquare f))
    (A' (compactSupportProperSquare f)) (by
      simpa only [projectionTensorComparisonCompatible] using hφ) K L

set_option backward.isDefEq.respectTransparency false in
/-- One tensor comparison carries the compact-support projection and the proper counit
projection through inclusion of a finite coefficient field. The compact-support square
holds for every f, and the proper square holds for proper f. This compares maps;
it assumes no compactification, composition, pentagon or proper projection equation.

Source: latest blueprint, sec-six-functors-basics/sk-thm-sf-pf-field,
thm-sf-pf-field.proof.md, Compatibility and the common coefficient-field paragraph.
(blueprint: lem-sf-common-projection-proper-tensor-compatibility).

Proof: normalize the rational and common tensor functors using their recorded tensor
normalizations. For two included objects use the inverse of the included
commonStageTensorComparison, then the inverse stage-system isoToStage for their tensor
at the compositum, with the
two scalar identity comparisons on the inputs. This constructs the tensor endpoint isomorphism
at the original field. The representative formula of commonStageDerivedTensor_existsUnique
and naturality of rationalTensorScalarComparison prove naturality in both inputs; no
injectivity of a transition functor is needed. The normalization of
canonicalCommonStagePullbackTensor at every larger finite field identifies the two
pullback/tensor comparisons with these endpoints. Substitute the common-stage operation
comparisons, whose model-normalization fields fix their components on included objects.
For the proper square transpose the counit-defined projection under the common-stage
pull/direct adjunction. The counit equation of commonStageComparison, tensor naturality
and the preceding pullback/tensor square identify the transpose with the image of the
rational transpose, hence give the proper square by the adjunction Hom bijection.
For compact support, perform the analogous transpose for the open projection using
openAdjunction and its unit equation; invert the equality of the open tensor
isomorphisms. Paste it with the proper square for the proper factor. The support
factorization normalization and pullComposition equation identify the pasted map with
the specified compact-support component. Its endpoints are exactly source and target.
The compact-support calculation applies to every f, since its compactification
has a proper factor and an open factor. The proper square uses the same tensor
comparison, without deriving it from a compact-support coherence equation.
The construction includes identity opens, zero objects and empty schemes. The existential
tensor comparison is eliminated only inside proofs; no data is defined by choosing an
arbitrary witness, and no faithfulness or projection invertibility is assumed. -/
theorem commonProjectionProperTensorCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C)
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) :
    ∃ t : ∀ X : SixFunctorSpace D,
      Functor.uncurry.obj ((H.coefficientStages E₀).rationalTensor X) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀ ≅
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).prod
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀) ⋙
          Functor.uncurry.obj (H.commonStageTensor X),
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        (c : Compactification f.hom.left)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
        (L : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀),
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).map
            (compactSupportProjectionComponent
              (H.coefficientStages E₀).rationalExchange f c K L) ≫
          (target (H.commonStageComparison E₀) t f c K L).hom =
        (source (H.commonStageComparison E₀) t f c K L).hom ≫
          compactSupportProjectionComponent H.commonStageExchange f c
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K)
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L)) ∧
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
        (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
        (L : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀),
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).map
            (compactSupportProperProjection (H.coefficientStages E₀).rationalExchange f K L) ≫
          (properTarget (H.commonStageComparison E₀) t f K L).hom =
        (properSource (H.commonStageComparison E₀) t f K L).hom ≫
          compactSupportProperProjection H.commonStageExchange f
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K)
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L)) := by
  refine ⟨commonProjectionTensorComparison H E₀, ?_, ?_⟩
  · intro X Y f c K L
    let Q := compactSupportProjectionSquare f c
    exact projection_preserved_of_factors (H.commonStageComparison E₀)
      (commonProjectionTensorComparison H E₀)
      ((H.coefficientStages E₀).rationalExchange Q) (H.commonStageExchange Q) K L
      (commonProjectionProperFactor H E₀ Q K L)
      (commonProjectionOpenFactor H E₀ Q K L)
  · intro X Y f hf K L
    exact properProjection_preserved (H.coefficientStages E₀).rationalExchange
      H.commonStageExchange (H.commonStageComparison E₀)
      (commonProjectionTensorComparison H E₀) f
      (commonProjectionPullbackTensorCompatibility H E₀ (compactSupportProperSquare f)) K L

end WeilConjectures
