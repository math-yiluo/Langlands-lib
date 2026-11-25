/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import WeilConjectures.RingTheory.NagataUniversallyJapanese

/-!
# Finiteness of the normalization of a finite type domain over ℤ

Source: literature/stacks-project/algebra.tex, Algebra, Proposition Tag 0335,
items (3) and (5), together with Definitions Tags 032R and 032F
(blueprint: lem-weil-pbc-finite-type-z-domain-normalization-finite).
-/

@[expose] public section

universe u v

namespace RingTheory

private theorem isN2_field (F : Type u) [Field F] : IsN2 F (FractionRing F) := by
  intro L _ _ _ _ _
  let : Module.Finite F (FractionRing F) :=
    Module.Finite.equiv (FractionRing.algEquiv F F).symm.toLinearEquiv
  let : Module.Finite F L := Module.Finite.trans (FractionRing F) L
  let : IsNoetherian F L := inferInstance
  exact Module.IsNoetherian.finite F (integralClosure F L)

private theorem isNagataRing_of_equiv_int (R : Type u) [CommRing R]
    (e : R ≃+* ℤ) : IsNagataRing R := by
  let : IsNoetherianRing R := isNoetherianRing_of_ringEquiv ℤ e.symm
  let : IsDomain R := e.isDomain
  let : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv e.symm
  let : Ring.DimensionLEOne R := Ring.DimensionLEOne.of_ringEquiv e
  refine ⟨inferInstance, ?_⟩
  intro p hp
  by_cases h : p = ⊥
  · subst p
    let e₀ := (RingEquiv.quotientBot R).trans e
    let : IsIntegrallyClosed (R ⧸ (⊥ : Ideal R)) :=
      IsIntegrallyClosed.of_equiv e₀.symm
    let : CharZero (R ⧸ (⊥ : Ideal R)) := ⟨fun m n hmn ↦ by
      have he := congrArg e₀ hmn
      simpa using he⟩
    intro L _ _ _ _ _
    exact IsIntegralClosure.finite (R ⧸ (⊥ : Ideal R))
      (FractionRing (R ⧸ (⊥ : Ideal R))) L (integralClosure (R ⧸ (⊥ : Ideal R)) L)
  · let : p.IsMaximal := hp.isMaximal h
    let := Ideal.Quotient.field p
    exact isN2_field (R ⧸ p)

/--
Let `A` be an integral domain of finite type over `ℤ`, and let `K` be its field
of fractions. The integral closure of `A` in `K` is finite as an `A`-module.

Source: literature/stacks-project/algebra.tex, Algebra, Proposition Tag 0335,
items (3) and (5), with Definitions Tags 032R and 032F
(blueprint: lem-weil-pbc-finite-type-z-domain-normalization-finite).

Proof: (1) `ℤ` is Nagata, by Proposition Tag 0335 (3), using the characteristic-zero
normal-domain argument of Lemma Tag 032M. (2) Finite type algebras over a Nagata
ring are universally Japanese by Proposition Tag 0335 (5), so `A` is N-2.
(3) Apply the N-2 condition to the trivial finite extension of the fraction field;
the integral closure is finite, by Definition Tag 032F. The proof uses
`def-weil-pbc-nagata-ring`, `def-weil-pbc-noetherian-ring`,
`def-weil-pbc-japanese-domain`, `def-pc-field-extension`,
`def-weil-pbc-normal-ring`,
`def-weil-pbc-separable-algebraic-extension`,
`lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`, and
`lem-weil-pbc-nagata-universally-japanese`.
-/
theorem finiteTypeZDomain_integralClosure_finite
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A]
    [Algebra.FiniteType ℤ A] [Field K] [Algebra A K]
    [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by
  let : Algebra (ULift.{u} ℤ) A := ULift.algebra' ℤ A
  let : IsScalarTower ℤ (ULift.{u} ℤ) A := ⟨fun n r a ↦ by
    simp [Algebra.smul_def, mul_assoc]⟩
  let : Algebra.FiniteType (ULift.{u} ℤ) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ULift.{u} ℤ) A
  have hZ := isNagataRing_of_equiv_int (ULift.{u} ℤ) ULift.ringEquiv
  have hA := isUniversallyJapanese_of_isNagataRing (ULift.{u} ℤ) hZ A
  let : Module.Finite A (integralClosure A (FractionRing A)) := hA (FractionRing A)
  exact Module.Finite.equiv
    (FractionRing.algEquiv A K).mapIntegralClosure.toLinearEquiv

end RingTheory
