/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteDerivedCoefficientData
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.ThreeStepAdjunctionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRealizationFunctor
public import WeilConjectures.CategoryTheory.ProperBaseChange.TransportedCompositeIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedExchangeAmbient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.ResidueExchangeAmbient

/-! # The specified exchange from coherent coefficient comparisons -/

@[expose] public section
universe u
open CategoryTheory Limits

-- Keep hom types on the category's direct quiver, including the diagram records.
attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance] coefficientProfiniteEssentiallySmall
private theorem reverse_step {C : Type*} [Category C]
    {A A' D D' : C} {a : A ⟶ A'} {d : D ⟶ D'}
    (p : A ≅ D) (q : A' ≅ D') (h : a ≫ q.hom = p.hom ≫ d) :
    d ≫ q.inv = p.inv ≫ a := by
  apply (p.eq_inv_comp).2
  rw [← Category.assoc, ← h, Category.assoc, q.hom_inv_id, Category.comp_id]

private def reverse_comparison {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃}
    {d : B₀ ⟶ B₁} {e : B₁ ⟶ B₂} {f : B₂ ⟶ B₃}
    (h : FiniteDiscreteThreeStepComparison a b c d e f) :
    FiniteDiscreteThreeStepComparison d e f a b c where
  e0 := h.e0.symm
  e1 := h.e1.symm
  e2 := h.e2.symm
  e3 := h.e3.symm
  first := reverse_step h.e0 h.e1 h.first
  second := reverse_step h.e1 h.e2 h.second
  third := reverse_step h.e2 h.e3 h.third

private def reverse_chain_comparison {C : Type*} [Category C]
    {s t : ExchangeChain C} (h : ExchangeChain.Comparison s t) :
    ExchangeChain.Comparison t s := reverse_comparison h

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

-- Compare the whole pullback family before taking square components, so the kernel
-- does not normalize concrete derived functors to compare an inserted eta expansion.
private theorem square_projection
    (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T)))
    (P : CoefficientComparisonData B Λ F) :
    CoefficientPullbackSquare B Λ F (@P.pullback) := by
  have hp : (fun {S T : Scheme.{u}} ↦
      @CoefficientComparisonData.pullback B _ Λ _ _ F P S T) = (@P.pullback) := rfl
  exact @Eq.mp _ _ (congrArg (CoefficientPullbackSquare B Λ F) hp) (@P.square)

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar in
private theorem stepAdjunction_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T : Scheme.{u}} (h : S ⟶ T) :
    residueExchangeAdjunction Λ h = coefficientDerivedAdjunction Λ h := by
  rw [coefficientDerivedAdjunction_eq]
  unfold residueExchangeAdjunction
  rfl

attribute [local semireducible] residueExchangeUpperStar in
private theorem stepSquare_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : CommSq g' f' f g) :
    residueExchangeSquare Λ sq = coefficientAmbientSquare Λ sq := by
  rw [coefficientAmbientSquare_eq, coefficientIsoTransThree_eq,
    residueExchangeSquare, transportedCompositeIso_eq]
  unfold coefficientDerivedUpperStarComp residueExchangeUpperStarComp
    coefficientDerivedUpperStar residueExchangeUpperStar
  rfl

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar in
private theorem stepChain_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : CommSq g' f' f g)
    (K : residueExchangeDerived Λ X) :
    coefficientInternalExchangeChain Λ sq K =
      Adjunction.exchangeChain (coefficientDerivedAdjunction Λ f)
        (coefficientDerivedAdjunction Λ f') (coefficientAmbientSquare Λ sq).hom K := by
  unfold coefficientInternalExchangeChain
  rw [stepAdjunction_eq Λ f, stepAdjunction_eq Λ f', stepSquare_eq Λ sq]

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar in
omit [TopologicalSpace B] [IsTopologicalRing B] in
private theorem comparison_exchange
    (C : Type) [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [DiscreteTopology C] [Finite C] [Fact (IsNilpotent (ℓ : C))]
    (sq : CommSq g' f' f g)
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj C) T)))
    (P : CoefficientComparisonData B (Profinite.continuousMapRingObj C) F) :
    coefficientExchangeSteps ℓ k B C sq (F X) (F Y') := by
  let Λ := Profinite.continuousMapRingObj.{u} C
  intro L hL
  have : QuasiCompact f := by
    have : QuasiCompact (f ≫ (Y ↘ Spec (.of k))) := by
      rw [comp_over f (Spec (.of k))]
      infer_instance
    exact QuasiCompact.of_comp f (Y ↘ Spec (.of k))
  have : QuasiCompact f' := by
    have : QuasiCompact (f' ≫ (Y' ↘ Spec (.of k))) := by
      rw [comp_over f' (Spec (.of k))]
      infer_instance
    exact QuasiCompact.of_comp f' (Y' ↘ Spec (.of k))
  have : QuasiSeparated f := by
    let : IsSeparated (f ≫ (Y ↘ Spec (.of k))) := by
      rw [comp_over f (Spec (.of k))]
      infer_instance
    let : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of k))
    infer_instance
  have : QuasiSeparated f' := by
    let : IsSeparated (f' ≫ (Y' ↘ Spec (.of k))) := by
      rw [comp_over f' (Spec (.of k))]
      infer_instance
    let : IsSeparated f' := IsSeparated.of_comp f' (Y' ↘ Spec (.of k))
    infer_instance
  obtain ⟨hc⟩ := (@CategoryTheory.Adjunction.threeStepComparison_family
      Scheme.{u} _
      (fun T : Scheme.{u} ↦ FiniteDiscreteEtalePlus B T)
      (fun T : Scheme.{u} ↦
        DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
          (condensedRingObj Λ T)))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      (fun {_ _} h ↦ D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h))
      (fun {_ _} h ↦ coefficientDerivedUpperStar Λ h) F (@P.pullback)
      (fun {_ _ _ _} {_ _ _ _} sq ↦
        Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq)
      (fun {_ _ _ _} {_ _ _ _} sq ↦ coefficientAmbientSquare Λ sq)
      (@square_projection B _ Λ _ _ F P) X Y X' Y' f g f' g' sq
      (R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f))
      (R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f'))
      (coefficientDerivedLowerStar Λ f) (coefficientDerivedLowerStar Λ f')
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) f)
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) f')
      (coefficientDerivedAdjunction Λ f)
      (coefficientDerivedAdjunction Λ f')
      (P.pushforward f) (P.pushforward f') (P.unit f') (P.counit f) L)
  refine ⟨{ comparison := ?_, source_eq := ?_, target_eq := ?_ }⟩
  · change ExchangeChain.Comparison
      (coefficientInternalExchangeChain Λ sq ((F X).obj L))
      ((coefficientEtaleExchangeChain B sq L).map (F Y'))
    rw [stepChain_eq Λ sq]
    exact reverse_chain_comparison hc
  · exact coefficientAmbientBoundedExchange_factorization ℓ k C sq ⟨(F X).obj L, hL⟩
  · exact coefficientEtaleExchange_map_factorization B
      (D := residueExchangeDerived Λ Y') (F Y') sq L

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar in
/-- Coherent coefficient comparisons identify the three specified exchange factors.
Source: Mathlib adjunction restriction and mates; the specified exchange definitions
(blueprint: lem-weil-pbc-coefficient-exchange-from-comparisons).

Proof in words. The continuous-function condensed ring of B is killed by ell.
The finite-type separated hypotheses imply that f and f-prime are qcqs.
Apply threeStepComparison_family to the two etale and two internal derived adjunctions.
Its hypotheses are P.unit, P.counit and P.square. First identify the eta-expanded
pullback family with the original family by function equality, preserving the
whole square-coherence predicate during this transport. Reverse its four vertex
isomorphisms using inverse cancellation, and substitute the etale component
formulas. The residueExchange interfaces are exactly the same actual derived
functors, adjunction, and pullback-square comparison as the coefficient interfaces.
This gives the comparison between the specified ambient unit, square, and counit
factors. Fully faithful restriction identifies these factors with the underlying
bounded factors. For the source total factorization use the existing theorem
boundedConstructibleBaseChange_hom_eq_ambient and the component formula for the
adjunction mate. For the target use Etale.baseChange_app_eq_mateEquiv and functoriality.
Neither properness, Cartesianity, nor invertibility of exchange is assumed;
empty schemes and zero objects are included. -/
theorem coefficientComparisonData_exchangeSteps [DiscreteTopology B] [Finite B]
    (hB : (ℓ : B) = 0) (sq : CommSq g' f' f g)
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (FiniteDiscreteInternalModules B T))
    (P : CoefficientComparisonData B (Profinite.continuousMapRingObj B) F) :
    haveI : Fact (IsNilpotent (ℓ : B)) := ⟨⟨1, by rw [pow_one]; exact hB⟩⟩
    finiteDiscreteExchangeSteps B ℓ k sq (F X) (F Y') := by
  have : Fact (IsNilpotent (ℓ : B)) := ⟨⟨1, by rw [pow_one]; exact hB⟩⟩
  exact comparison_exchange B ℓ k B sq F P

end AlgebraicGeometry.ProEtale.CondensedRing
