/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismStrictQuotientModels
public import WeilConjectures.TraceFormula.QuotientTensor.QuotientTensorInsertion
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismStrictQuotientMultiplication

/-! # Normalized isomorphism of ordinary quotient towers

Source: Stacks Tags 03D2 and 03EL; expanded clause 4 of
prose-10-21.
(blueprint: lem-pur-isomorphism-ordinary-quotient-tower-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralOnSlice

attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit
attribute [local instance_reducible] IntegralOnSlice.Site IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring
attribute [local instance_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf

/-- The quotient tower isomorphism has the specified insertion at every level.
Source: Stacks Tag 03EL; the existing unrestricted quotient-insertion construction.
(blueprint: lem-pur-isomorphism-ordinary-quotient-tower-normalization).
Proof: the slice-none and unrestricted chosen tower presentations are definitionally
identical. Apply the already proved unrestricted insertion isomorphism directly; its
component is the specified insertion by reflexivity. -/
theorem isomorphismOrdinaryQuotientTowerNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : Cx l E Y none) :
    ∃ a : (tower l E Y none).obj P ⋙ trfInverseImageComplex l E g ≅
      (integralOperationsPullbackTowerFunctor l E g).obj P,
      ∀ n : ℕ, a.hom.app (op n) = QuotientTensor.insertion l E g n
        ((unrestrictedIntegralFiniteComplex l E Y n).obj P) := by
  refine ⟨(WeilConjectures.insertion_iso l E g).app P, ?_⟩
  intro n
  rfl

end WeilConjectures.IntegralOnSlice
