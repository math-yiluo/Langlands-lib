/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule
public import WeilConjectures.ZetaLinearAlgebra.Pairing

/-!
# Trace–cup structures on graded Frobenius modules

Let `H : ℤ → FrobeniusModule K` be a `ℤ`-graded family of Frobenius modules over a field `K`,
for instance the `ℓ`-adic cohomology groups `H^i(X ⊗ k̄, ℚ̄_ℓ)` of a scheme `X` over a finite field
with their geometric Frobenius. A *trace–cup structure* of degree `n` and multiplier `c` on `H`
consists of

* a graded-commutative cup product `⌣ : H^i × H^j ⟶ H^{i+j}` compatible with Frobenius, and
* a trace `tr : H^n ⟶ K` on which Frobenius acts by `c`, i.e. `tr (F z) = c * tr z`.

Its *trace–cup pairings* are `⟨x, y⟩ = tr (x ⌣ y) : H^i × H^j ⟶ K` for `i + j = n`. For the
cohomology of a smooth proper geometrically connected variety of dimension `d` over `𝔽_q` the
degree is `n = 2d`, the multiplier is `c = q^d` (Frobenius acts on `ℚ̄_ℓ(-d)` by `q^d`), and
Poincaré duality says that the trace is an isomorphism and the pairings are perfect.

This file develops the linear algebra consequences of such a structure: the Frobenius
similitude of the pairings, their graded commutativity, and, when the pairings are perfect, the
Frobenius-equivariant duality `H^j ≅ (H^i)^∨(-d)` and the reciprocity `α ↦ c / α` of the
eigenvalues of Frobenius.

## Main definitions

- `FrobeniusModule.TraceCup`: a trace–cup structure on a graded family of Frobenius modules.
- `FrobeniusModule.TraceCup.pairing`: its trace–cup pairing `⟨x, y⟩ = tr (x ⌣ y)`.
- `FrobeniusModule.TraceCup.IsPerfect`: the trace is bijective and every pairing is perfect.

## Main statements

- `FrobeniusModule.TraceCup.pairing_frobenius`: `⟨F x, F y⟩ = c * ⟨x, y⟩`.
- `FrobeniusModule.TraceCup.pairing_frobeniusEnd_pow`: `⟨F^r x, F^r y⟩ = c^r * ⟨x, y⟩`.
- `FrobeniusModule.TraceCup.pairing_comm`: `⟨y, x⟩ = (-1)^{ij} ⟨x, y⟩`, and
  `FrobeniusModule.TraceCup.pairing_comm_of_eq_two_mul`: `⟨y, x⟩ = (-1)^i ⟨x, y⟩` in even degree.
- `FrobeniusModule.TraceCup.nonempty_equiv_dual_rescale`: a perfect pairing induces a
  Frobenius-equivariant isomorphism `H^j ≅ (H^i)^∨` with Frobenius rescaled by `c`.
- `FrobeniusModule.TraceCup.roots_charpoly_frobeniusEnd`: the eigenvalues of Frobenius on `H^j`
  are the `c / α` for the eigenvalues `α` on `H^i`, with multiplicity.
-/

@[expose] public section

universe w v

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- A *trace–cup structure* of degree `n` and multiplier `c` on a `ℤ`-graded family `H` of
Frobenius modules: a cup product `⌣ : H^i × H^j ⟶ H^k` for `i + j = k`, which commutes with
Frobenius and is graded commutative, `y ⌣ x = (-1)^{ij} x ⌣ y`, together with a trace
`tr : H^n ⟶ K` on which Frobenius acts by `c`, i.e. `tr (F z) = c * tr z`.

The target degree `k` of the cup product is an index with `i + j = k`, rather than `i + j`
itself, so that `x ⌣ y` and `y ⌣ x` land in the same Frobenius module `H k`. -/
structure TraceCup (H : ℤ → FrobeniusModule.{max w v, v} K) (n : ℤ) (c : K) where
  /-- The cup product `⌣ : H^i × H^j ⟶ H^k`, for `i + j = k`. -/
  cup (i j k : ℤ) (h : i + j = k) : (H i).carrier →ₗ[K] (H j).carrier →ₗ[K] (H k).carrier
  /-- The cup product commutes with Frobenius: `F x ⌣ F y = F (x ⌣ y)`. -/
  cup_frobenius (i j k : ℤ) (h : i + j = k) (x : (H i).carrier) (y : (H j).carrier) :
    cup i j k h ((H i).frobenius x) ((H j).frobenius y) = (H k).frobenius (cup i j k h x y)
  /-- The cup product is graded commutative: `y ⌣ x = (-1)^{ij} x ⌣ y`. -/
  cup_comm (i j k : ℤ) (h : i + j = k) (x : (H i).carrier) (y : (H j).carrier) :
    cup j i k ((add_comm j i).trans h) y x = (i * j).negOnePow • cup i j k h x y
  /-- The trace `tr : H^n ⟶ K`. -/
  trace : (H n).carrier →ₗ[K] K
  /-- Frobenius acts on the target of the trace by `c`: `tr (F z) = c * tr z`. -/
  trace_frobenius (z : (H n).carrier) : trace ((H n).frobenius z) = c * trace z

namespace TraceCup

variable {H : ℤ → FrobeniusModule.{max w v, v} K} {n : ℤ} {c : K} (T : TraceCup H n c)

/-- The *trace–cup pairing* `⟨x, y⟩ = tr (x ⌣ y) : H^i × H^j ⟶ K` of a trace–cup structure, for
complementary degrees `i + j = n`. -/
noncomputable def pairing (i j : ℤ) (h : i + j = n) :
    (H i).carrier →ₗ[K] (H j).carrier →ₗ[K] K :=
  (T.cup i j n h).compr₂ T.trace

lemma pairing_apply (i j : ℤ) (h : i + j = n) (x : (H i).carrier) (y : (H j).carrier) :
    T.pairing i j h x y = T.trace (T.cup i j n h x y) :=
  rfl

/-- **Frobenius similitude.** The trace–cup pairing multiplies by the multiplier `c` under
Frobenius: `⟨F x, F y⟩ = c * ⟨x, y⟩`. -/
theorem pairing_frobenius (i j : ℤ) (h : i + j = n) (x : (H i).carrier) (y : (H j).carrier) :
    T.pairing i j h ((H i).frobenius x) ((H j).frobenius y) = c * T.pairing i j h x y := by
  rw [pairing_apply, cup_frobenius, trace_frobenius, pairing_apply]

/-- **Iterated Frobenius similitude.** `⟨F^r x, F^r y⟩ = c^r * ⟨x, y⟩`. -/
theorem pairing_frobeniusEnd_pow (i j : ℤ) (h : i + j = n) (r : ℕ) (x : (H i).carrier)
    (y : (H j).carrier) :
    T.pairing i j h (((H i).frobeniusEnd ^ r) x) (((H j).frobeniusEnd ^ r) y) =
      c ^ r * T.pairing i j h x y := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ' (H i).frobeniusEnd, pow_succ' (H j).frobeniusEnd, Module.End.mul_apply,
      Module.End.mul_apply]
    exact (T.pairing_frobenius i j h _ _).trans (by rw [ih, pow_succ', mul_assoc])

/-- **Graded commutativity of the pairing.** `⟨y, x⟩ = (-1)^{ij} ⟨x, y⟩`. -/
theorem pairing_comm (i j : ℤ) (h : i + j = n) (x : (H i).carrier) (y : (H j).carrier) :
    T.pairing j i ((add_comm j i).trans h) y x = (i * j).negOnePow • T.pairing i j h x y := by
  rw [pairing_apply, cup_comm, pairing_apply, Units.smul_def, Units.smul_def, map_zsmul]

/-- **Graded commutativity in even degree.** If the degree `n = 2 * m` of the trace is even,
then `⟨y, x⟩ = (-1)^i ⟨x, y⟩` for `x ∈ H^i` and `y ∈ H^j`, since `i * j ≡ i` modulo `2`. -/
theorem pairing_comm_of_eq_two_mul {m : ℤ} (hn : n = 2 * m) (i j : ℤ) (h : i + j = n)
    (x : (H i).carrier) (y : (H j).carrier) :
    T.pairing j i ((add_comm j i).trans h) y x = i.negOnePow • T.pairing i j h x y := by
  rw [pairing_comm _ i j h, (Int.negOnePow_eq_iff _ _).2]
  obtain rfl : j = 2 * m - i := by omega
  have : i * (2 * m - i) - i = 2 * (m * i) - i * (i + 1) := by ring
  rw [this]
  exact (even_two_mul _).sub (Int.even_mul_succ_self i)

/-- A trace–cup structure is *perfect* if its trace is an isomorphism and its pairings in all
complementary degrees are perfect. This is the conclusion of Poincaré duality. -/
structure IsPerfect : Prop where
  /-- The trace `tr : H^n ⟶ K` is an isomorphism. -/
  bijective_trace : Function.Bijective T.trace
  /-- The trace–cup pairings `H^i × H^j ⟶ K`, `i + j = n`, are perfect. -/
  isPerfPair_pairing (i j : ℤ) (h : i + j = n) : (T.pairing i j h).IsPerfPair

variable {T}

/-- **Equivariant duality.** If the trace–cup pairing `H^i × H^j ⟶ K` is perfect, then
`y ↦ ⟨-, y⟩` is an isomorphism `H^j ≅ (H^i)^∨` which intertwines the Frobenius of `H^j` with the
contragredient Frobenius `(F^{-1})^∨` of `H^i` rescaled by the multiplier `c`. For `c = q^d`
the target is the Tate twist `(H^i)^∨(-d)`. -/
theorem nonempty_equiv_dual_rescale (hc : c ≠ 0) (i j : ℤ) (h : i + j = n)
    (hp : (T.pairing i j h).IsPerfPair) :
    Nonempty ((H j).Equiv (((H i).dual).rescale c)) := by
  refine ⟨⟨(T.pairing i j h).flip.toPerfPair, fun y ↦ LinearMap.ext fun x ↦ ?_⟩⟩
  have hφ := frobeniusEnd_rescale_apply (M := (H i).dual) hc
    ((T.pairing i j h).flip.toPerfPair y)
  rw [frobeniusEnd] at hφ
  simp only [LinearEquiv.coe_coe] at hφ
  erw [hφ]
  change T.pairing i j h x ((H j).frobenius y) = c * T.pairing i j h ((H i).frobenius.symm x) y
  rw [← T.pairing_frobenius, LinearEquiv.apply_symm_apply]

/-- **Reciprocity of the eigenvalues.** If the trace–cup pairing `H^i × H^j ⟶ K` is perfect and
`c ≠ 0`, the eigenvalues of Frobenius on `H^j`, with multiplicity, are the `c / α` for the
eigenvalues `α` of Frobenius on `H^i`. -/
theorem roots_charpoly_frobeniusEnd [IsAlgClosed K] (hc : c ≠ 0) (i j : ℤ) (h : i + j = n)
    (hp : (T.pairing i j h).IsPerfPair) :
    (H j).frobeniusEnd.charpoly.roots =
      (H i).frobeniusEnd.charpoly.roots.map fun α ↦ c / α :=
  LinearMap.charpoly_roots_of_similitude (p := T.pairing i j h) hc
    (T.pairing_frobenius i j h)

end TraceCup

end FrobeniusModule
