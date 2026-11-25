/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.ProperBaseChange.GeometricallyNormalTensorNormal
import WeilConjectures.RingTheory.ProperBaseChange.SeparableFieldGeometricallyNormal

/-!
# Normal algebras under separable scalar extension

Source: Stacks Project, Varieties, Tag 0C3M, lemma-base-change-normal-by-separable;
Algebra, Tags 0C30 and 06DF
(blueprint: lem-weil-pbc-normal-algebra-separable-scalar-extension).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- A normal commutative `k`-algebra remains normal after a separable field extension `K/k`.
Separability means that every finitely generated intermediate field is separably generated.
Normality means that every prime localization is an integrally closed domain.
There is no algebraicity, finite-generation, domain or nonzero assumption on the algebra.
Source: Stacks Project, Varieties, Tag 0C3M, lemma-base-change-normal-by-separable;
Algebra, Tags 0C30 and 06DF
(blueprint: lem-weil-pbc-normal-algebra-separable-scalar-extension).

Proof:
1. Apply `lem-weil-pbc-separable-field-geometrically-normal` to `K/k`. Its separability
   hypothesis is precisely `IsSeparableExtension k K`, not algebraic separability. Thus
   `K` is geometrically normal: `K ⊗[k] E` is normal for every field extension `E/k`.
2. Apply `lem-weil-pbc-geometrically-normal-tensor-normal` with `A = K` and the given `B`.
   Step 1 and the normality hypothesis on `B` give normality of `K ⊗[k] B`.
3. Swap the tensor factors by the balanced map `c ⊗ b ↦ b ⊗ c`. Its reverse is inverse
   on pure tensors, so the universal property and generation by pure tensors of
   `def-weil-pbc-module-tensor-product` give inverse maps. The tensor multiplication and
   unit formulas make these ring maps. The resulting ring isomorphism identifies primes
   and their localizations, sending `x/s` to `f(x)/f(s)`. It preserves domains and
   integral closedness: the induced fraction-field isomorphism preserves monic equations
   and their roots. Hence every prime localization of `B ⊗[k] K` is an integrally closed
   domain, as required by `def-weil-pbc-normal-ring`. If `B` is zero there are no primes;
   disconnected normal rings are covered prime by prime.
-/
theorem isNormal_tensorProduct_of_separableExtension
    (k : Type u) (B : Type v) (K : Type w)
    [Field k] [CommRing B] [Field K] [Algebra k B] [Algebra k K]
    (hK : IsSeparableExtension k K)
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal (B ⊗[k] K)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  set_option linter.style.haveILetI false in
  let hA : ∀ (E : Type (max u v w)) [Field E] [Algebra k E],
      ∀ (p : Ideal (K ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
    fun E _ _ ↦ normal_tensorProduct_of_isSeparableExtension k K E hK
  let hnormal := isNormal_tensorProduct_of_geometricallyNormal k K B hA hB
  intro q hq
  haveI := hq
  let e : (K ⊗[k] B) ≃+* (B ⊗[k] K) :=
    (Algebra.TensorProduct.comm k K B).toRingEquiv
  let p : Ideal (K ⊗[k] B) := Ideal.comap e q
  haveI : p.IsPrime := Ideal.IsPrime.comap e
  have hp := hnormal p
  let f := Localization.localRingEquiv p q e rfl
  haveI : IsDomain (Localization.AtPrime p) := hp.1
  haveI : IsIntegrallyClosed (Localization.AtPrime p) := hp.2
  exact ⟨f.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv f⟩

end Algebra
