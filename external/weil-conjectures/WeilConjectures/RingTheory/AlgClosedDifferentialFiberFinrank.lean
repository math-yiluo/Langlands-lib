/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Differential-fibre finrank is preserved at any prime above q after scalar
extension. Source: Stacks Project, Tag 00RV.
(blueprint: new-algclosed-differential-fiber-finrank).

Proof: Write B = K ⊗[k] S, κ = κ(q), and L = κ(qK). Contraction gives the
canonical field embedding κ → L, compatible with the maps from S. Differential
base change gives Ω[B/K] ≃ B ⊗[S] Ω[S/k]. Tensor with L over B and cancel B
to identify the left-hand fibre with L ⊗[S] Ω[S/k]. Compatibility of S → κ → L
and tensor associativity identify this with L ⊗[κ] (κ ⊗[S] Ω[S/k]). Extending
a κ-vector-space basis to L preserves finrank, proving the asserted equality.
The argument does not require maximality or algebraic closedness, and works
also when the differential fibre is zero; finrank base change holds without
a finite-dimensionality hypothesis.
-/
theorem algClosed_prime_over_finrank_differentials_eq
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S] [FiniteType k S]
    (q : PrimeSpectrum S)
    (K : Type (max u v)) (_hK : Field K) (_hAk : Algebra k K) (_hCK : IsAlgClosed K)
    (qK : PrimeSpectrum (K ⊗[k] S))
    (_hmax : qK.asIdeal.IsMaximal)
    (hq : PrimeSpectrum.comap
      (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK = q) :
    Module.finrank qK.asIdeal.ResidueField
        (qK.asIdeal.ResidueField ⊗[K ⊗[k] S] KaehlerDifferential K (K ⊗[k] S)) =
      Module.finrank q.asIdeal.ResidueField
        (q.asIdeal.ResidueField ⊗[S] KaehlerDifferential k S) := by
  let B := K ⊗[k] S
  let L := qK.asIdeal.ResidueField
  let κ := q.asIdeal.ResidueField
  let : Algebra S B := TensorProduct.rightAlgebra
  have hp : q.asIdeal = qK.asIdeal.comap (algebraMap S B) :=
    (congrArg PrimeSpectrum.asIdeal hq).symm
  let f : κ →ₐ[S] L := Ideal.ResidueField.mapₐ q.asIdeal qK.asIdeal
    (Algebra.ofId S B) hp
  let : Algebra κ L := f.toAlgebra
  have : IsScalarTower S κ L := IsScalarTower.of_algHom f
  let e : (L ⊗[B] KaehlerDifferential K B) ≃ₗ[L]
      (L ⊗[κ] (κ ⊗[S] KaehlerDifferential k S)) :=
    LinearEquiv.baseChange B L _ _ (KaehlerDifferential.tensorKaehlerEquiv k K S B).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.cancelBaseChange S B L L _
      ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange S κ L L _).symm
  exact e.finrank_eq.trans (Module.finrank_baseChange (R := L) (S := κ))

end Algebra
