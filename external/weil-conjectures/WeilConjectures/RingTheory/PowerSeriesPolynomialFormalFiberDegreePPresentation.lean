/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Basic

import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs

import WeilConjectures.RingTheory.FormalFiberDegreePDerivation
import WeilConjectures.RingTheory.FormalFiberDegreePQuotient

/-!
# Degree-p presentations of extended generic formal fibres

Source: Stacks Project, More on Algebra, Tag 07PR, finite-model and derivation paragraphs.
(blueprint: lem-weil-pbc-power-series-polynomial-degree-p-presentation)
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- A degree-p final step in a purely inseparable extension presents the extended formal
fibre as a binomial hypersurface over the preceding fibre. A derivation of that fibre
sends its constant coefficient to a unit.
Source: Stacks Project, More on Algebra, Tag 07PR, proof, finite-model and derivation
paragraphs; Tags 07N9, 07PH and 07PE.
(blueprint: lem-weil-pbc-power-series-polynomial-degree-p-presentation)

Proof:
Choose a in M with z^p = a, and put f = a tensor 1 in R. The specified-coefficient
formal-fibre derivation component gives an absolute derivation D of R with D(f) a
unit. It uses the finite A-subalgebra model of M, the singleton finite-extension
completion comparison, and extension of derivations through localizations and
completion; clearing denominators by a pth power preserves the unit conclusion
for this original coefficient a. Independently, the quotient component base changes
the simple field presentation L = M[Z]/(Z^p-a), giving R[Z]/(Z^p-f) isomorphic to T.
Both components use the same a, so their witnesses give the required conjunction.
No regularity of the preceding fibre is assumed or concluded.

Edge cases: n or m may be zero. A zero formal fibre causes no exception: its
polynomial quotient and the extended fibre are zero rings, where zero is a unit.
Degree p is nontrivial because p is prime, so the non-pth-power argument applies. -/
theorem formalFiber_polynomial_degreePPresentation
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime]
    (L : Type u) [Field L]
    [Algebra ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    (M : IntermediateField
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L)
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    (z : L) (hz : IntermediateField.adjoin M ({z} : Set L) = ⊤)
    (hpow : ∃ f : M, z ^ p = (f : L)) (hdeg : Module.finrank M L = p) :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let K := (⊥ : Ideal A).ResidueField
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := TensorProduct K M ((⊥ : Ideal A).Fiber C)
    let T := TensorProduct K L ((⊥ : Ideal A).Fiber C)
    letI : CommSemiring R := (inferInstance : CommRing R).toCommSemiring
    letI : AddCommMonoid R := (inferInstance : CommRing R).toAddCommGroup.toAddCommMonoid
    letI : CommSemiring T := (inferInstance : CommRing T).toCommSemiring
    letI : AddCommMonoid T := (inferInstance : CommRing T).toAddCommGroup.toAddCommMonoid
    ∃ (f : R) (D : Derivation ℤ R R), IsUnit (D f) ∧
      Nonempty ((Polynomial R ⧸
        Ideal.span ({Polynomial.X ^ p - Polynomial.C f} : Set (Polynomial R))) ≃+* T) := by
  intro A K C R T
  -- Direct elimination avoids rechecking the entire dependent tensor-product goal at each step.
  refine hpow.elim fun a ha ↦ ?_
  refine (exists_derivation_isUnit_tmul_formalFiber k p n m q L M z hz a ha hdeg).elim
    fun D hD ↦ ?_
  have hiso := nonempty_quotient_X_pow_sub_C_ringEquiv_tensorProduct K L M ((⊥ : Ideal A).Fiber C)
    p z hz a ha hdeg
  exact ⟨Algebra.TensorProduct.includeLeftRingHom a, D, hD, hiso⟩

end MvPowerSeries
