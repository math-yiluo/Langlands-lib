/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainData
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorComplexSquare

/-! Homogeneous form of the ringed associator square. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The ringed preimage square on one homogeneous degree.
Source: Stacks 0FPQ and 0FNG.
(blueprint: new-sf-native-weil-ringed-associator-chain-ringed-square).

Proof: apply `HomologicalComplex.Hom.f · n` to both sides of the already
constructed ringed preimage square `nativeRingedAssociatorComplex_square`
(blueprint: lem-sf-native-weil-ringed-associator-complex-square).  The component
is kept separate because the subsequent forgetting calculation uses it together
with the normalized ordinary summand formulas. -/
theorem nativeRingedAssociatorComponent_square
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X}
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T)
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (n : ℤ) :
    nativeRingedAssociatorComponent D P Q N n :=
  congrArg (fun f ↦ HomologicalComplex.Hom.f f n)
    (nativeRingedAssociatorComplex_square D.b T D.adj D.A P Q N)

end AlgebraicGeometry.ProEtaleWeilSheaf
