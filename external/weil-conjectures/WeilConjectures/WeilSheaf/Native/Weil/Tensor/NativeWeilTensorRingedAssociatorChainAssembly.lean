/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainData

/-! Assembly of homogeneous associator components. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Outer map-bifunctor extensionality assembles the homogeneous transport.
Source: Stacks 0FPQ, 0FNG, 06YU, 0FPT.
(blueprint: new-sf-native-weil-ringed-associator-chain-assembly).

Proof: take the degree component, apply the map-bifunctor hom-extensionality
lemma for the forgetting functor, and invoke the homogeneous transport for the
outer summand.  This is the coproduct assembly step and introduces no derived
or localization data. -/
theorem nativeChainForgetAssociator_assembly
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X}
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T)
    (hcomp : ∀ (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (n p q : ℤ) (h : p + q = n), nativeChainForgetComponent D P Q N n p q h) :
    nativeChainForgetAssociator D := by
  intro P Q N
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
  intro p q h
  exact hcomp P Q N n p q h

end AlgebraicGeometry.ProEtaleWeilSheaf
