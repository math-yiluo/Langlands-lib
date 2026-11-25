/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import WeilConjectures.PoincareDuality.Pod.Composition.PodCompositionRestrictedTower
import WeilConjectures.PoincareDuality.Pod.Composition.PodCompositionRoosPasting
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison

/-! # Composition on the strict normalized Roos models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem normalized_roos_eq
    {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    (D : PodCompletionReindex l E f)
    (hf : PodCompletionReindex.RoosFst l E f D)
    (hs : PodCompletionReindex.RoosSnd l E f D)
    (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ) :
    (D.roos C).hom = scalarRoosMap (isoReductionIntegralInverse l E f) C := by
  obtain ⟨hcf, hcs⟩ := podReindexingRoosCoordinates (isoReductionIntegralInverse l E f) C
  have hfirst := (hf C).trans hcf.symm
  have hsecond (i : ℤ) := (hs C i).trans (hcs i).symm
  apply HomologicalComplex.hom_ext
  intro i
  have hfi := congrArg (fun q ↦ q.f i) hfirst
  change _ ≫ _ = _ ≫ _ at hfi
  have hid := CochainComplex.mappingCocone.id_X
    (podRoosBoundary ((podReindexTower l E f).obj C)) i (i - 1) (by omega)
  have hl := congrArg (fun z ↦ (D.roos C).hom.f i ≫ z) hid
  have hr := congrArg
    (fun z ↦ (scalarRoosMap (isoReductionIntegralInverse l E f) C).f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hl hr
  rw [hfi, hsecond i] at hl
  exact (Category.comp_id _).symm.trans
    (hl.symm.trans (hr.trans (Category.comp_id _)))

section
/-- The composition square before localization, on every restricted strict complex.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 0941
(blueprint: lem-pod-composition-restricted-roos).

Proof: the two coordinate normalizations identify every supplied Roos comparison
with the canonical additive Roos map, since the mapping-cocone identity is the
sum of its two coordinate inclusions. The restricted-tower composition theorem
identifies the composite restricted map with the two successive maps. Naturality
of the additive Roos map moves the first restricted map past the second Roos
comparison; composition of additive Roos comparisons then yields the single Roos
comparison followed by the ordinary compositor on the tower. Functoriality of
the strict Roos construction and the restricted-tower equation identify the
remaining maps. Every step holds for all complexes, including zero complexes. -/
theorem podCompositionRestrictedRoos
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (A : PodReindexFamily l E)
    (hf : PodCompletionReindex.Laws l E f (A.completion f))
    (hh : PodCompletionReindex.Laws l E h (A.completion h))
    (hc : PodCompletionReindex.Laws l E (h ≫ f) (A.completion (h ≫ f)))
    (ha : ∀ (M : scalarReductionSource l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))),
      ((A.composition h f).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x)
    (C : CochainComplex (coefficientSequenceModules l E V) ℤ) :
    let Cf := ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C
    let σ := (NatTrans.mapHomologicalComplex
      (integralComparisonSequenceComposition l E h f).hom (.up ℤ)).app C
    let Tσ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).map σ)
    let α : isoReductionIntegralComplex l E (h ≫ f) ⟶
        isoReductionIntegralComplex l E f ⋙ isoReductionIntegralComplex l E h :=
      NatTrans.mapHomologicalComplex (A.composition h f).hom (.up ℤ)
    α.app (integralOperationsRoos (podRestrictedTower l E C)) ≫
      (isoReductionIntegralComplex l E h).map
        ((A.completion f).roos (podRestrictedTower l E C)).hom ≫
      (isoReductionIntegralComplex l E h).map
        (integralOperationsRoosFunctor.map ((A.completion f).restricted C).hom) ≫
      ((A.completion h).roos (podRestrictedTower l E Cf)).hom ≫
      integralOperationsRoosFunctor.map ((A.completion h).restricted Cf).hom =
    ((A.completion (h ≫ f)).roos (podRestrictedTower l E C)).hom ≫
      integralOperationsRoosFunctor.map ((A.completion (h ≫ f)).restricted C).hom ≫
      integralOperationsRoosFunctor.map Tσ := by
  dsimp only
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hff, hfs, _, _, _, _, hfr, _⟩ := hf
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hhf, hhs, _, _, _, _, hhr, _⟩ := hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hcf, hcs, _, _, _, _, hcr, _⟩ := hc
  have ht := podCompositionRestrictedTower l E h f (A.completion f) (A.completion h)
    (A.completion (h ≫ f)) hfr hhr hcr (A.composition h f) ha C
  let τ := isoWhiskerLeft (podRestrictedTower l E C)
    (NatIso.mapHomologicalComplex (A.composition h f) (.up ℤ))
  change τ.inv ≫ _ ≫ _ = _ at ht
  have ht' := τ.inv_comp_eq.mp ht
  exact podCompositionRoosPasting (isoReductionIntegralInverse l E f)
    (isoReductionIntegralInverse l E h) (isoReductionIntegralInverse l E (h ≫ f))
    (A.composition h f) (podRestrictedTower l E C)
    (podRestrictedTower l E
      (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C))
    (podRestrictedTower l E
      (((integralComparisonSequencePullback l E (h ≫ f)).mapHomologicalComplex (.up ℤ)).obj C))
    (podRestrictedTower l E
      (((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C)))
    ((A.completion f).roos (podRestrictedTower l E C)).hom
    ((A.completion h).roos _).hom ((A.completion (h ≫ f)).roos _).hom
    ((A.completion f).restricted C).hom ((A.completion h).restricted _).hom
    ((A.completion (h ≫ f)).restricted C).hom _
    (normalized_roos_eq l E f _ hff hfs _) (normalized_roos_eq l E h _ hhf hhs _)
    (normalized_roos_eq l E (h ≫ f) _ hcf hcs _) ht'

end

end WeilConjectures
