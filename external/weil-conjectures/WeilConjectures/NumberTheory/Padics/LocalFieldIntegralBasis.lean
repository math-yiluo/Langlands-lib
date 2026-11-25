/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.NumberTheory.Padics.PadicIntegersIntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral bases for finite extensions of local coefficient fields

Source: Weil conjectures blueprint, finite-free coefficient detail
(blueprint: lem-sfb-local-field-integral-basis).
-/

@[expose] public section

universe u v

namespace Padic

/--
For a finite tower of coefficient fields, the unit ball of the upper field has an
integral basis over the unit ball of the lower field.

Source: Weil conjectures blueprint, `sk-prop-sfb-cartesian-coefficients-finite-free.proof.md`,
opening sentence (blueprint: lem-sfb-local-field-integral-basis).

Proof:
1. Write the unit balls as `A` and `B`. By
   `lem-weil-l-adic-extension-integers-dvr` and `def-sc-discrete-valuation-ring`,
   `A` is a DVR and a principal ideal domain, hence Noetherian by
   `lem-weil-pbc-pid-noetherian-normal`. Compatibility makes `B` an `A`-module.
   The field `E` is complete by `lem-weil-l-adic-extension-complete`, and its
   absolute value is nontrivial because the value of `l` is `l⁻¹ < 1`.
2. Choose an `E`-basis of `F` with coordinates `c_i`. The coordinate linear
   equivalence is a homeomorphism by
   `lem-weil-pbc-finite-dimensional-linear-homeomorphism`: the absolute-value
   topologies are Hausdorff, and compatibility makes the inclusion isometric,
   so scalar multiplication is continuous. Thus some `ε > 0` satisfies
   `|y| < ε → |c_i(y)| < 1` for every `i`.
3. Choose `N ≥ 0` with `l⁻ᴺ < ε`. For `x ∈ B`, the coordinates of `lᴺ x`
   belong to `A`. Therefore `B` lies in the single finitely generated lattice
   spanned over `A` by `l⁻ᴺ` times the chosen field basis.
4. By `lem-weil-pbc-noetherian-submodule-finite`, `B` is finitely generated over
   `A`. It is torsion-free because it embeds in the field `F`. Apply
   `lem-sc-dvr-fg-torsionfree-free` to obtain a finite `A`-basis of `B`.
5. This basis spans `F` over `E`: multiply any field element by a sufficiently
   large power of `l` to put it in `B`, expand there, and divide back. It is
   also `E`-linearly independent: multiply any finite relation by one power
   of `l` that puts all coefficients in `A`, then use `A`-linear independence
   and cancel that nonzero power.
6. By `def-weil-vector-space-dimension`, this field basis has cardinality
   `Module.finrank E F`. Reindex the integral basis accordingly. Its elements
   lie in `B`, and its basis coordinates give exactly the asserted integral
   expansion and uniqueness.
-/
theorem exists_integral_basis
    (l : ℕ) [Fact l.Prime]
    (E : Type u) (F : Type v)
    [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [Algebra E F] [IsScalarTower (Padic l) E F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    [FiniteDimensional E F]
    (hcompat : ∀ x : E,
      coefficientExtensionAbsoluteValue l F (algebraMap E F x) =
        coefficientExtensionAbsoluteValue l E x) :
    ∃ b : Fin (Module.finrank E F) → F,
      (∀ i, b i ∈ coefficientExtensionIntegers l F) ∧
        ∀ x : F, x ∈ coefficientExtensionIntegers l F →
          ∃! a : Fin (Module.finrank E F) → E,
            (∀ i, a i ∈ coefficientExtensionIntegers l E) ∧
              x = ∑ i, algebraMap E F (a i) * b i := by
  classical
  have _ := hcompat
  -- The integral-closure bridge lets Mathlib supply finiteness, freeness, and rank.
  let A := coefficientExtensionIntegers l E
  have hmap (z : A) : algebraMap A E z = (z : E) := rfl
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsFractionRing A E := h.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing A := h.2.2.2.2.2.2.2.2.1
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic l) E).injective
  let C := integralClosure A F
  have : Module.Finite A C := IsIntegralClosure.finite A E F C
  have : Module.Free A C := IsIntegralClosure.module_free A E F C
  have hdim : Module.finrank A C = Module.finrank E F :=
    IsIntegralClosure.rank A E F C
  let b := Module.finBasisOfFinrankEq A C hdim
  let i : E →ₐ[Padic l] F := IsScalarTower.toAlgHom (Padic l) E F
  have hC (x : F) : x ∈ coefficientExtensionIntegers l F ↔ x ∈ integralClosure A F :=
    padic_integers_integralClosure l E F i x
  refine ⟨fun j ↦ (b j : F), fun j ↦ (hC _).2 (b j).property, ?_⟩
  intro x hx
  let y : C := ⟨x, (hC x).1 hx⟩
  let a : Fin (Module.finrank E F) → E := fun j ↦ (b.repr y j : E)
  refine ⟨a, ⟨fun j ↦ (b.repr y j).property, ?_⟩, ?_⟩
  · have hy := b.sum_repr y
    have hy' := congrArg (fun z : C ↦ (z : F)) hy
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply A E F,
      hmap, a, y] using hy'.symm
  · intro a' ha'
    let c : Fin (Module.finrank E F) → A := fun j ↦ ⟨a' j, ha'.1 j⟩
    have heq : ∑ j, c j • b j = y := by
      apply Subtype.ext
      simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply A E F,
        hmap, c, y] using ha'.2.symm
    have hc' : ∀ j, c j = b.repr y j := by
      intro j
      calc
        c j = b.repr (∑ k, c k • b k) j := (congrFun (b.repr_sum_self c) j).symm
        _ = b.repr y j := congrArg (fun z : C ↦ b.repr z j) heq
    funext j
    exact congrArg (fun z : A ↦ (z : E)) (hc' j)

end Padic
