/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import WeilConjectures.PoincareDuality.Pod.Reindexing.Composition.PodReindexingCompositionReduction
import WeilConjectures.PoincareDuality.Pod.Reindexing.Composition.PodReindexingCompositionLimit
import WeilConjectures.PoincareDuality.Pod.Reindexing.Composition.PodReindexingCompositionTensor

/-! # Compatibility of normalized ordinary reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Successive ordinary relabellings commute with reduction, total limit and tensor.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941
(blueprint: lem-pod-reindexing-composition-compatibility).

Proof: work first with strict complexes and the section-normalized compositor.
At each positive quotient the two paths send a scalar-tensor generator to the same
section under Over.mapComp. QuotientGenerators and QuotientTransition thus identify
the entire quotient comparisons, including transitions. On strict systems the
RestrictedGenerators formula and the adjunction-unit normalization of the system
compositor identify its two restricted-tower maps. Compare the product maps after
every product projection; their composites agree by functoriality of relabelling.
RoosFst and RoosSnd identify both coordinates of the resulting cone maps, so the
whole maps commute with composition. K-injective normalization and naturality of
the source and target Roos models allow the intervening model comparisons to cancel.
Substitute into LimitModel and localize. The functorial localization compositor
identifies the localized section compositor with A.compositionDerived; the strict
system compositor localizes to integralComparisonSystemComposition. This proves
the limit equation on arbitrary systems, by representing them with complexes.
Unit and Counit say that reduction and limit are mates for the actual adjunctions.
Taking mates of the limit equation and using the triangle identities gives the
reduction equation on every ambient derived object. For tensor, choose flat-term
K-flat representatives for both constructible inputs and their relabellings.
Generators sends each pure tensor along both paths to the same relabelled tensor.
The quotient transitions and both Roos coordinates give equality before localization.
Substitute the Model equations for the three tensor comparisons and cancel the
representative comparison isomorphisms. Naturality then gives the displayed tensor
equation on the original inputs. No faithfulness of finite derived evaluations is
used; the equations are checked on entire strict chain maps before localization.
Zero inputs and empty sites obey the identical formulas. -/
theorem podReindexingCompositionCompatibility
    (A : PodReindexFamily l E)
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (A.completion f))
    (htensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex.Laws l E f (A.completion f) (A.tensor f))
    (hcomposition : ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
      [IsIso h] [IsIso f] (M : scalarReductionSource l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))),
      ((A.composition h f).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x) :
    A.Composition l E := by
  have hlimit := @podReindexingCompositionLimit l _ E _ _ _ A hcompletion hcomposition
  have hred := @podReindexingCompositionReduction l _ E _ _ _ A hcompletion hlimit
  intro V W Z h f _ _ _ _ _
  exact ⟨hred h f, hlimit h f,
    podReindexingCompositionTensor l E A hcompletion htensor hcomposition h f⟩

end WeilConjectures
