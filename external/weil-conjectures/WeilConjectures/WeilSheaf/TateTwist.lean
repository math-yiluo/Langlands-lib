/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.WeilSheaf.Fourier
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Tate twists of Weil complexes

Let `k₀` be a finite field with algebraic closure `k̄` and `X` a `k₀`-scheme with geometric fiber
`X̄`. The Tate sheaf `ℚ̄_ℓ(1) = ℤ_ℓ(1) ⊗_{ℤ_ℓ} ℚ̄_ℓ` on `X̄_proét` is built from the sheaves
`μ_{ℓⁿ}` of roots of unity with the `ℓ`-th power maps as transitions, and its Weil structure
`Fr_X^* ℚ̄_ℓ(1) ≅ ℚ̄_ℓ(1)` is the functorial pullback of roots of unity.

Since `X̄` lives over the algebraically closed field `k̄` and `ℓ` is invertible on it, every
`μ_{ℓⁿ}` is the constant sheaf on `μ_{ℓⁿ}(k̄)`, so `ℚ̄_ℓ(1)` is the constant `ℓ`-adic sheaf with
fiber the line `ℤ_ℓ(1)(k̄) ⊗ ℚ̄_ℓ` (`cyclotomicTateModule`). The geometric Galois Frobenius
`Fr_X = 𝟙 × σ` acts on the coefficients through the geometric Frobenius `σ` of `k̄`, so the
pullback of roots of unity, read on this constant description, is the canonical Weil structure
of the constant sheaf `ℚ̄_ℓ` followed by the action of `σ` on `ℤ_ℓ(1)(k̄)`. That action is
multiplication by the `ℓ`-adic cyclotomic character `χ_ℓ(σ) ∈ ℤ_ℓˣ`
(`cyclotomicCharacter`; it is `q⁻¹`, see `AlgebraicGeometry.WeilSheaf.cyclotomicUnit_eq`), a
scalar which does not depend on a choice of generator of `ℤ_ℓ(1)(k̄)`. Hence `ℚ̄_ℓ(1)` is the
constant Weil twist `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)}` (`AlgebraicGeometry.WeilSheaf.constantTwist`), which is
how it is defined here.

The higher twists are `ℚ̄_ℓ(0) = ℚ̄_ℓ`, `ℚ̄_ℓ(m) = ℚ̄_ℓ(1) ⊗ ℚ̄_ℓ(m - 1)` and
`ℚ̄_ℓ(-m) = [ℚ̄_ℓ(m), ℚ̄_ℓ]` for `m > 0`. They are lisse Weil sheaves, hence flat over `ℚ̄_ℓ,X̄`,
so the derived tensor products and internal homs of the blueprint are the underived ones. The
Tate twist `K ↦ K(m)` of Weil complexes is the derived tensor product with `ℚ̄_ℓ(m)`.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.cyclotomicUnit`: the scalar `χ_ℓ(σ)` by which the geometric
  Frobenius of `k̄` acts on `ℤ_ℓ(1)(k̄)`, in `ℚ̄_ℓ`.
- `AlgebraicGeometry.WeilSheaf.tateTwistSheaf`: the Tate sheaves `ℚ̄_ℓ(m)`, `m ∈ ℤ`.
- `AlgebraicGeometry.WeilComplex.tateTwist`: the Tate twist functor `(-)(m)` on Weil complexes.

## Main statements

- `AlgebraicGeometry.WeilSheaf.cyclotomicUnit_eq`: for `ℓ ≠ p`, `χ_ℓ(σ) = q⁻¹`.
- `AlgebraicGeometry.WeilSheaf.isLisse_tateTwistSheaf`: the Tate sheaves are lisse.
- `AlgebraicGeometry.WeilSheaf.tateTwistSheaf_one`: `ℚ̄_ℓ(1)` is the constant Weil twist
  `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)}`.

## Blueprint

`AlgebraicGeometry.WeilSheaf.tateTwistSheaf` and `AlgebraicGeometry.WeilComplex.tateTwist`
implement `definition-tate-twists`. The cyclotomic Tate module `ℤ_ℓ(1)` of the subsection
`definition-tate-twists--8` is `cyclotomicTateModule`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

section

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]

/-- The scalar `χ_ℓ(σ) ∈ ℚ̄_ℓˣ` by which the geometric Frobenius `σ : x ↦ x ^ (1 / q)` of the
algebraic closure `k̄` of `k₀` acts on the cyclotomic Tate module `ℤ_ℓ(1)(k̄)`: the value at `σ`
of the `ℓ`-adic cyclotomic character, mapped along `ℤ_ℓ ⟶ ℚ_ℓ ⟶ ℚ̄_ℓ`. For `ℓ ≠ p` it is `q⁻¹`
(`cyclotomicUnit_eq`); for `ℓ = p` its value is meaningless. (blueprint:
`definition-tate-twists`) -/
noncomputable def cyclotomicUnit : (PadicAlgCl l)ˣ :=
  letI := Fintype.ofFinite k₀
  Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
    (cyclotomicCharacter (AlgebraicClosure k₀) l
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)).toRingEquiv)

variable [Fact (ringChar k₀ ≠ l)]

/-- For `ℓ ≠ p`, the geometric Frobenius acts on `ℤ_ℓ(1)(k̄)` by `q⁻¹`, where `q = #k₀`: the
arithmetic Frobenius `x ↦ x ^ q` raises roots of unity to the `q`-th power. -/
theorem cyclotomicUnit_eq :
    (cyclotomicUnit k₀ l : PadicAlgCl l) = (Nat.card k₀ : PadicAlgCl l)⁻¹ := by
  let := Fintype.ofFinite k₀
  set k := AlgebraicClosure k₀
  have : NeZero ((l : ℕ) : k) := ⟨by
    rw [← map_natCast (algebraMap k₀ k), map_ne_zero_iff _ (algebraMap k₀ k).injective,
      Ne, ringChar.spec, Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime k₀ _) Fact.out]
    exact Fact.out⟩
  have hσ : ((cyclotomicCharacter k l (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ k).toRingEquiv
      : ℤ_[l]ˣ) : ℤ_[l]) = (Fintype.card k₀ : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
    rw [cyclotomicCharacter.toZModPow, ← modularCyclotomicCharacter.unique]
    intro t ht
    rw [map_natCast, ZMod.val_natCast, ← Units.val_pow_eq_pow_val,
      ← pow_eq_pow_mod _ ((mem_rootsOfUnity _ _).mp ht)]
    simp
  have hinv : (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ k).toRingEquiv =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ k).toRingEquiv⁻¹ := rfl
  rw [cyclotomicUnit, Units.coe_map, hinv, map_inv]
  change algebraMap ℚ_[l] (PadicAlgCl l) (PadicInt.Coe.ringHom
    ((cyclotomicCharacter k l (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ k).toRingEquiv)⁻¹ :
      ℤ_[l]ˣ)) = _
  rw [map_units_inv, map_inv₀, hσ]
  simp [Nat.card_eq_fintype_card]

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The non-negative Tate sheaves `ℚ̄_ℓ(n) = ℚ̄_ℓ(1)^{⊗ n}`: `ℚ̄_ℓ(0)` is the constant Weil
sheaf `ℚ̄_ℓ`, `ℚ̄_ℓ(1) = ℤ_ℓ(1) ⊗_{ℤ_ℓ} ℚ̄_ℓ` is the constant sheaf `ℚ̄_ℓ` whose Weil structure is
multiplied by the scalar `χ_ℓ(σ)` by which the geometric Frobenius acts on roots of unity, and
`ℚ̄_ℓ(n + 2) = ℚ̄_ℓ(1) ⊗ ℚ̄_ℓ(n + 1)`. (blueprint: `definition-tate-twists`) -/
noncomputable def tateTwistSheafNat : ℕ → WeilSheaf k₀ l X
  | 0 => adicConstant k₀ l X
  | 1 => (adicConstant k₀ l X).constantTwist (cyclotomicUnit k₀ l)
  | n + 2 => ((adicConstant k₀ l X).constantTwist (cyclotomicUnit k₀ l)).tensorObj
      (tateTwistSheafNat (n + 1)) (isLisse_adicConstant k₀ l X).constantTwist

/-- The non-negative Tate sheaves are lisse. -/
theorem isLisse_tateTwistSheafNat : ∀ n : ℕ, (tateTwistSheafNat k₀ l X n).IsLisse
  | 0 => isLisse_adicConstant k₀ l X
  | 1 => (isLisse_adicConstant k₀ l X).constantTwist
  | n + 2 => ProEtale.IsAdicLisseSheaf.ihom
      ((isLisse_adicConstant k₀ l X).constantTwist.dual) (isLisse_tateTwistSheafNat (n + 1))

/-- The Tate sheaves `ℚ̄_ℓ(m)` on a `k₀`-scheme `X`, for `m ∈ ℤ`: for `m ≥ 0` the tensor power
`ℚ̄_ℓ(1)^{⊗ m}` of `ℚ̄_ℓ(1) = ℤ_ℓ(1) ⊗_{ℤ_ℓ} ℚ̄_ℓ`, with `ℚ̄_ℓ(0) = ℚ̄_ℓ`, and for `m < 0` the dual
`[ℚ̄_ℓ(-m), ℚ̄_ℓ]`. These are lisse Weil sheaves, so that the derived tensor products and internal
homs of the blueprint are the underived ones. (blueprint: `definition-tate-twists`) -/
noncomputable def tateTwistSheaf : ℤ → WeilSheaf k₀ l X
  | (n : ℕ) => tateTwistSheafNat k₀ l X n
  | .negSucc n => (tateTwistSheafNat k₀ l X (n + 1)).dual (isLisse_tateTwistSheafNat k₀ l X _)

/-- The Tate sheaves are lisse. -/
theorem isLisse_tateTwistSheaf : ∀ m : ℤ, (tateTwistSheaf k₀ l X m).IsLisse
  | (n : ℕ) => isLisse_tateTwistSheafNat k₀ l X n
  | .negSucc n => (isLisse_tateTwistSheafNat k₀ l X (n + 1)).dual

/-- `ℚ̄_ℓ(0)` is the constant Weil sheaf `ℚ̄_ℓ`. -/
theorem tateTwistSheaf_zero : tateTwistSheaf k₀ l X 0 = adicConstant k₀ l X :=
  rfl

/-- `ℚ̄_ℓ(1)` is the constant Weil twist `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)}`
(`AlgebraicGeometry.WeilSheaf.constantTwist`). This holds by definition. -/
theorem tateTwistSheaf_one :
    tateTwistSheaf k₀ l X 1 = (adicConstant k₀ l X).constantTwist (cyclotomicUnit k₀ l) :=
  rfl

end

end WeilSheaf

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- The Tate twist `K ↦ K(m) = K ⊗^L ℚ̄_ℓ(m)` of Weil complexes on a `k₀`-scheme `X`, the derived
tensor product with the Tate sheaf `ℚ̄_ℓ(m)` (`AlgebraicGeometry.WeilSheaf.tateTwistSheaf`).
(blueprint: `definition-tate-twists`) -/
noncomputable def tateTwist (m : ℤ) : WeilComplex k₀ l X ⥤ WeilComplex k₀ l X :=
  tensorLisse (WeilSheaf.tateTwistSheaf k₀ l X m) (WeilSheaf.isLisse_tateTwistSheaf k₀ l X m)

instance (m : ℤ) : (tateTwist k₀ l X m).Additive := by
  unfold tateTwist
  infer_instance

noncomputable instance (m : ℤ) : (tateTwist k₀ l X m).CommShift ℤ := by
  unfold tateTwist
  infer_instance

/-- The Tate twist of Weil complexes is a triangulated functor. -/
instance (m : ℤ) : (tateTwist k₀ l X m).IsTriangulated := by
  unfold tateTwist
  infer_instance

end WeilComplex

end AlgebraicGeometry
