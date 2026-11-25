/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Exact line tensor preserves the canonical augmented reduction triangle

Source: definition-tate-twists--10, proof steps 6--7.
(blueprint: lem-weil-integral-line-tensor-completeness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Tensor by a completed coefficient line preserves intrinsic derived completeness.
Source: blueprint definition-tate-twists--10, proof steps 6--7
(blueprint: lem-weil-integral-line-tensor-completeness).

Proof: the internal dual of L is its tensor inverse, checked after a rank-one
trivialization. Tensor by L and by that dual are inverse exact equivalences of module
sheaves, and hence give inverse triangulated equivalences on unbounded derived
categories. The derived equivalence preserves products by their universal property:
maps B to the image of a product correspond to maps from the inverse image of B
to that product, and hence to the product of the corresponding component Hom sets.
Choose flat-term K-flat representatives for the reductions of K. The usual balanced
associativity map identifies reduction of K tensor L with reduction of K tensored
with the ordinary reduction of L. After restriction of scalars it also identifies
these reductions with the line twist of the original restricted reductions, without
requiring those restrictions to be K-flat over the integral ring. On pure tensors
these maps commute with quotient transitions and with x mapped to 1 tensor x.
Apply the triangulated equivalence to the distinguished augmented Roos triangle
in IsSfDerivedComplete. Its product comparisons and the preceding compatible
reduction comparisons identify its first map with the canonical reduction units
and its second map with 1 minus the quotient shift. The transported connecting map
therefore supplies exactly the required distinguished triangle. This argument uses
no boundedness, constructibility, or choice of a unique map to a derived limit. -/
theorem integralLineTensor_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    (L : scalarReductionSource.{u, u} l E S)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u + 1, u, u + 1} L 1]
    [(SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) L).Additive]
    [PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) L)]
    [PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) L)]
    (K : DerivedCategory.{u + 2} (scalarReductionSource.{u, u} l E S))
    (hK : IsSfDerivedComplete l E S K) :
    IsSfDerivedComplete l E S
      ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) L).mapDerivedCategory.obj
          K) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  have hc : IsDerivedCompleteUnrestricted l E S K :=
    ⟨D, hl, (sfDerivedComplete_iff_legacy l E S D hl K).mp hK⟩
  obtain ⟨D', hl', ht⟩ := CompletedLineTensor.complete l E S L 1 K hc
  apply (sfDerivedComplete_iff_legacy l E S D' hl' _).mpr
  exact ht

end WeilConjectures
