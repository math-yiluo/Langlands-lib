/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealization
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
import WeilConjectures.SmoothPurity.Integral.IntegralCanonicalPullbackTensorReduction
import WeilConjectures.SmoothPurity.Integral.IntegralSystemCompositionIdentification

/-! The reduced system form of integral pullback/tensor composition coherence.

Source: Stacks 07A4 and 0941; the strict quotient-system calculation before reflection.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced)

The former finite-evaluation proof used a false joint-faithfulness assertion.
`integralPullbackTensorCompositionReduced_of_systemLaw` compares whole strict-system
representatives before localization: for every compositor whose reduction is the system
compositor after the whole-system pullback comparisons, the equation reduces to the
composition law of the coherent system pullback/tensor comparison, which descends from
the strict cochain law. The compositor `pullbackTensorIntegralComposition`, chosen from
`integralPullbackComposition`, has this normalization by the last clause of that theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

-- Use the sequence-site presentations throughout the transport calculation. These
-- adapters avoid repeatedly comparing the two presentations of the derived categories.
private def integralPullbackSystemComparison_sequence {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralPullback l E f ⋙
        ((sfIntegralConstructible l E X).ι ⋙ (pullbackTensorCalculus l E X).reduction) ≅
      ((sfIntegralConstructible l E Y).ι ⋙ (pullbackTensorCalculus l E Y).reduction) ⋙
        integralComparisonDerivedSequencePullback l E f :=
  (integralPullbackSystemComparison l E).choose f

private theorem canonicalIntegralPullbackTensor_systemReduction_sequence {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    ((sfIntegralConstructible l E X).ι ⋙ (pullbackTensorCalculus l E X).reduction).map
        (canonicalIntegralPullbackTensor l E f M N).hom =
      (integralPullbackSystemComparison_sequence l E f).hom.app
          ((constructibleIntegralTensor l E Y).obj (M, N)) ≫
        (integralComparisonDerivedSequencePullback l E f).map
          ((integralSystemTensorReduction l E Y).hom.app (M, N)) ≫
        (integralSystemTensorComparison l E f).hom.app
          (((sfIntegralConstructible l E Y).ι ⋙ (pullbackTensorCalculus l E Y).reduction).obj M,
            ((sfIntegralConstructible l E Y).ι ⋙ (pullbackTensorCalculus l E Y).reduction).obj N) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom ((integralPullbackSystemComparison_sequence l E f).inv.app M)
            ((integralPullbackSystemComparison_sequence l E f).inv.app N)) ≫
        (integralSystemTensorReduction l E X).inv.app
          ((constructibleIntegralPullback l E f).obj M,
            (constructibleIntegralPullback l E f).obj N) := by
  exact canonicalIntegralPullbackTensor_systemReduction l E f M N

-- Infer the compositor equality in its finite-system presentation before extracting
-- its component; elaborating it directly against the sequence type unfolds the functors.
private theorem finiteSystemDerivedComposition_hom_app_sequence {X Y Z : Scheme.{u}}
    (h : Z ⟶ X) (f : X ⟶ Y) (A : coefficientSequenceDerived l E Y) :
    ((finiteSystemDerivedComposition (integralSystemRings l E)
      (integralSystemTransition l E) h f).hom.app A :
        (integralComparisonDerivedSequencePullback l E (h ≫ f)).obj A ⟶
          (integralComparisonDerivedSequencePullback l E h).obj
            ((integralComparisonDerivedSequencePullback l E f).obj A)) =
      (integralComparisonSystemComposition l E h f).hom.app A := by
  have e := congrArg (fun a ↦ a.hom.app A)
    (finiteSystemDerivedComposition_eq l E h f)
  exact e

/-- Reduced integral pullback/tensor composition equation for a system-normalized compositor.
Source: Stacks 07A4 and 0941; quotient-system pure-tensor calculation.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced)

Proof: the reductions of the canonical integral pullback/tensor comparisons are the
system comparisons conjugated by the whole-system pullback comparisons of
`integralPullbackSystemComparison` and the reduction/tensor comparisons.
The system comparisons obey the composition law for the system compositor, by descent of
the strict cochain law. The hypothesis on `c` identifies its reduction with the system
compositor; `reducedPullbackTensorComposition_of_systemLaw` combines these equations. -/
theorem integralPullbackTensorCompositionReduced_of_systemLaw {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (c : constructibleIntegralPullback l E (h ≫ f) ≅
      constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E h)
    (hc : ∀ K : sfIntegralConstructibleCategory l E Y,
      (integralSystemReduction l E Z).map (c.hom.app K) ≫
          ((integralPullbackSystemComparison l E).choose h).hom.app
            ((constructibleIntegralPullback l E f).obj K) ≫
          (finiteSystemDerivedPullback (integralSystemRings l E)
            (integralSystemTransition l E) h).map
              (((integralPullbackSystemComparison l E).choose f).hom.app K) =
        ((integralPullbackSystemComparison l E).choose (h ≫ f)).hom.app K ≫
          (finiteSystemDerivedComposition (integralSystemRings l E)
            (integralSystemTransition l E) h f).hom.app
              ((integralSystemReduction l E Y).obj K))
    (M N : sfIntegralConstructibleCategory l E Y) :
    (integralSystemReduction l E Z).map
        ((canonicalIntegralPullbackTensor l E (h ≫ f) M N).hom ≫
          (constructibleIntegralTensor l E Z).map
            (Prod.mkHom (c.hom.app M) (c.hom.app N))) =
      (integralSystemReduction l E Z).map
        (c.hom.app ((constructibleIntegralTensor l E Y).obj (M, N)) ≫
          (constructibleIntegralPullback l E h).map
            (canonicalIntegralPullbackTensor l E f M N).hom ≫
          (canonicalIntegralPullbackTensor l E h
            ((constructibleIntegralPullback l E f).obj M)
            ((constructibleIntegralPullback l E f).obj N)).hom) := by
  have key := reducedPullbackTensorComposition_of_systemLaw
    ((sfIntegralConstructible l E Y).ι ⋙ (pullbackTensorCalculus l E Y).reduction)
    ((sfIntegralConstructible l E X).ι ⋙ (pullbackTensorCalculus l E X).reduction)
    ((sfIntegralConstructible l E Z).ι ⋙ (pullbackTensorCalculus l E Z).reduction)
    (constructibleIntegralPullback l E f) (constructibleIntegralPullback l E h)
    (constructibleIntegralPullback l E (h ≫ f))
    (integralComparisonDerivedSequencePullback l E f)
    (integralComparisonDerivedSequencePullback l E h)
    (integralComparisonDerivedSequencePullback l E (h ≫ f))
    (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
    (constructibleIntegralTensor l E Z)
    (pullbackTensorCalculus l E Y).systemClosed.tensor
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (pullbackTensorCalculus l E Z).systemClosed.tensor
    (integralPullbackSystemComparison_sequence l E f)
    (integralPullbackSystemComparison_sequence l E h)
    (integralPullbackSystemComparison_sequence l E (h ≫ f))
    (integralSystemTensorReduction l E Y) (integralSystemTensorReduction l E X)
    (integralSystemTensorReduction l E Z)
    (integralSystemTensorComparison l E f) (integralSystemTensorComparison l E h)
    (integralSystemTensorComparison l E (h ≫ f))
    (integralComparisonSystemComposition l E h f) c
    (fun K ↦ by
      calc
        _ = (integralPullbackSystemComparison_sequence l E (h ≫ f)).hom.app K ≫
            (finiteSystemDerivedComposition (integralSystemRings l E)
              (integralSystemTransition l E) h f).hom.app
                (((sfIntegralConstructible l E Y).ι ⋙
                  (pullbackTensorCalculus l E Y).reduction).obj K) := hc K
        _ = _ := congrArg
          ((integralPullbackSystemComparison_sequence l E (h ≫ f)).hom.app K ≫ ·)
          (finiteSystemDerivedComposition_hom_app_sequence l E h f
            (((sfIntegralConstructible l E Y).ι ⋙
              (pullbackTensorCalculus l E Y).reduction).obj K)))
    (canonicalIntegralPullbackTensor l E f) (canonicalIntegralPullbackTensor l E h)
    (canonicalIntegralPullbackTensor l E (h ≫ f))
    (canonicalIntegralPullbackTensor_systemReduction_sequence l E f)
    (canonicalIntegralPullbackTensor_systemReduction_sequence l E h)
    (canonicalIntegralPullbackTensor_systemReduction_sequence l E (h ≫ f))
    (integralSystemTensorComparison_comp l E h f) M N
  exact key

/-- Reduced form of the integral pullback/tensor composition equation.
Source: Stacks 07A4 and 0941; quotient-system pure-tensor calculation.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced)

Proof: the recorded compositor `pullbackTensorIntegralComposition` is the one chosen from
`integralPullbackComposition`, whose last clause says that its reduction is the system
compositor after the whole-system pullback comparisons. This is the hypothesis of
`integralPullbackTensorCompositionReduced_of_systemLaw`. -/
theorem integralPullbackTensorCompositionReduced {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (integralSystemReduction l E Z).map
        (((@canonicalIntegralPullbackTensor l _ E _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ Z hZ)).map (Prod.mkHom
            (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M)
            (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app N))) =
      (integralSystemReduction l E Z).map
        (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app
          (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M, N)) ≫
          ((@constructibleIntegralPullback l _ E _ _ _ Z X h hZ hX)).map
            ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
          ((@canonicalIntegralPullbackTensor l _ E _ _ _ Z X h hZ hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom) :=
  integralPullbackTensorCompositionReduced_of_systemLaw l E f h _
    (fun K ↦ (integralPullbackComposition l E).choose_spec.2.2 h f K) M N

end WeilConjectures
