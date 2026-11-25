/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BaseChangeField
public import WeilConjectures.WeilSheaf.BaseChangeField.Cohomology
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.CohomologyAdicConstant
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.TraceCupAdicConstant
public import WeilConjectures.WeilSheaf.TraceIsomorphism
public import WeilConjectures.ZetaLinearAlgebra.TraceCup

/-!
# Poincaré duality for smooth proper varieties over a finite field

Let `k₀ = 𝔽_q` be a finite field, `ℓ ≠ p` a prime and `X₀` a smooth proper geometrically
connected `k₀`-scheme of pure dimension `d`. Write `Hⁱ = Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for the cohomology of
the constant Weil sheaf `ℚ̄_ℓ` (`AlgebraicGeometry.WeilSheaf.cohomology`), with its geometric
Frobenius `F`. Poincaré duality says:

1. *Trace.* The trace `tr : H^{2d} ⟶ ℚ̄_ℓ(-d)` is an isomorphism.
2. *Finiteness.* Every `Hⁱ` is finite-dimensional, and `Hⁱ = 0` for `i ∉ [0, 2d]`.
3. *Pairing.* The trace–cup pairings `⟨x, y⟩ = tr (x ⌣ y) : Hⁱ × H^{2d-i} ⟶ ℚ̄_ℓ(-d)` are
   perfect and graded commutative, `⟨y, x⟩ = (-1)ⁱ ⟨x, y⟩`.
4. *Frobenius similitude.* `F` acts on `ℚ̄_ℓ(-d)` by `q^d`, and `⟨F x, F y⟩ = q^d ⟨x, y⟩`.
5. *Reciprocity.* `H^{2d-i} ≅ (Hⁱ)^∨(-d)` Frobenius-equivariantly, so the eigenvalues of `F`
   on `H^{2d-i}` are the `q^d / α` for the eigenvalues `α` of `F` on `Hⁱ`, with multiplicity.
6. *Base change.* For a finite extension `k₀'/k₀` of degree `r`, the geometric Frobenius of
   `k₀'` on the cohomology of `X₀ ×_{k₀} k₀'` is `F^r`, and `⟨F^r x, F^r y⟩ = (q^r)^d ⟨x, y⟩`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_traceCup_poincareDuality`
(`theorem-poincare-duality-frobenius`):
  the six clauses above, without graded commutativity.
- `AlgebraicGeometry.WeilSheaf.exists_traceCup_poincarePairing` (`corollary-cup-product-pairing`):
  the trace isomorphism, the perfect pairings and the equivalent equivariant duality
  isomorphisms, the Frobenius similitude, and graded commutativity.
- `AlgebraicGeometry.WeilSheaf.poincareDuality` (`theorem-poincare-duality-frobenius`): the six
clauses,
  with graded commutativity in clause (3).

## Implementation notes

*Coefficients.* The blueprint states the theorem with coefficients `ℚ_ℓ` and proves it at the
coefficient stage `ℚ̄_ℓ`. The `ℓ`-adic cohomology with Frobenius available in the repository is
that of Weil sheaves, whose coefficients are `ℚ̄_ℓ` (`AlgebraicGeometry.WeilSheaf`), so the
theorem is stated at `ℚ̄_ℓ`; the `ℚ_ℓ` statement follows by the flat base change
`Hⁱ(X, ℚ̄_ℓ) = Hⁱ(X, ℚ_ℓ) ⊗ ℚ̄_ℓ`, which the repository cannot state for lack of `ℚ_ℓ`-sheaves.

*The trace–cup structure.* The cup product and the trace map of `corollary-cup-product-pairing--1`
are defined in the repository for étale sheaves of `Λ`-modules
(`AlgebraicGeometry.Etale.cupProduct`, `AlgebraicGeometry.Etale.TateOrientation.untwistedTraceMap`),
not for Weil complexes, which have no tensor product of complexes, `Ra^!` or orientation yet. The
statements are therefore existential: there is a trace–cup structure (`FrobeniusModule.TraceCup`) on
the cohomology — a Frobenius-compatible graded-commutative cup product and a trace on which
Frobenius acts by `q^d` — whose trace and pairings have the asserted properties. The value line
`ℚ̄_ℓ(-d)` is `ℚ̄_ℓ` with Frobenius acting by `q^d`, as recorded by
`FrobeniusModule.TraceCup.trace_frobenius`.

*Complementary degrees.* The pairing in degrees `i` and `j` is indexed by `i j : ℤ` with
`i + j = 2 * d`, since `2 * d - (2 * d - i)` is not definitionally `i`. Outside `[0, 2d]` both
groups vanish and perfectness is automatic.

*Ingredients.* The theorem is deduced by linear algebra
(`WeilConjectures.ZetaLinearAlgebra.TraceCup`) from three statements about Weil sheaves:
`AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant` (vanishing outside
`[0, 2d]`, `lemma-perfect-complexes-geometric-point`, proved through the pro-étale cohomological
dimension of `ℚ̄_ℓ`), `AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_baseChangeField`
(the Frobenius of `k₀'` is `F^r`, proved by transporting Weil structures along the base change) and
`AlgebraicGeometry.WeilSheaf.exists_traceCup_isPerfect` (trace isomorphism and perfectness at
the coefficient stage `ℚ̄_ℓ`, `corollary-cup-product-pairing--1`,
`corollary-degreewise-duality-over-fields`, `theorem-poincare-duality--9`,
`theorem-poincare-duality-frobenius`). The last is built from the cup product of `ℚ̄_ℓ`-cohomology
transported from the finite levels, and its only open input is
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_adicConstant`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry


/-- `ℓ` stays different from the characteristic after a field extension of `k₀`. -/
lemma fact_ringChar_ne_of_algebra (k₀ : Type u) [Field k₀] {l : ℕ} [Fact (ringChar k₀ ≠ l)]
    (k₀' : Type u) [Field k₀'] [Algebra k₀ k₀'] : Fact (ringChar k₀' ≠ l) :=
  ⟨Algebra.ringChar_eq k₀ k₀' ▸ Fact.out⟩

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

section Ingredients

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `corollary-cup-product-pairing--1`, `corollary-degreewise-duality-over-fields`
(degreewise, with `K = ℚ̄_ℓ`, via `theorem-poincare-duality--9`) and
`theorem-poincare-duality-frobenius` (a), at the coefficient stage `ℚ̄_ℓ`: for `X` smooth proper
geometrically connected of pure dimension `d` over `k₀`, the cohomology `H^• = H^•(X ⊗ k̄, ℚ̄_ℓ)`
carries a trace–cup structure — the graded-commutative cup product of
`corollary-cup-product-pairing--1`, compatible with Frobenius, and the trace
`tr : H^{2d} ⟶ ℚ̄_ℓ(-d)`, on whose target Frobenius acts by `q^d` — whose trace is an isomorphism
and whose pairings `⟨x, y⟩ = tr (x ⌣ y)` are perfect. -/
theorem exists_traceCup_isPerfect (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ T : FrobeniusModule.TraceCup.{u + 1} (adicConstant k₀ l X).cohomology (2 * d)
      ((Nat.card k₀ : PadicAlgCl l) ^ d), T.IsPerfect := by
  obtain ⟨-, -, -, hprop⟩ := traceIsomorphism_adicConstant k₀ l X d
  obtain ⟨tr, htr⟩ := hprop ‹_›
  exact exists_traceCup_isPerfect_of_linearEquiv X d tr htr

/-- Blueprint `prose-10-19` (the geometric-Frobenius convention
`Frob_{q^r} = Frob_q^r`), for the Weil structures of `definition-weil-structure` and the Frobenius
operators of `definition-frobenius-operator--1`: for a finite extension `k₀'/k₀` of degree `r`, the
cohomology of the base change `X ×_{k₀} k₀'` is that of `X`, the geometric Frobenius of `k₀'`
corresponding to the `r`-th power `F^r` of the geometric Frobenius of `k₀`. This is item (6) of
the proof of `theorem-poincare-duality-frobenius`; see
`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_adicConstant_baseChangeField`. -/
theorem exists_linearEquiv_cohomology_baseChangeField
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (k₀' : Type u) [Field k₀'] [Finite k₀'] [Algebra k₀ k₀'] (i : ℤ) :
    haveI := fact_ringChar_ne_of_algebra (l := l) k₀ k₀'
    ∃ e : ((adicConstant k₀' l (X.baseChangeField k₀ k₀')).cohomology i).carrier ≃ₗ[PadicAlgCl l]
        ((adicConstant k₀ l X).cohomology i).carrier,
      ∀ x, e (((adicConstant k₀' l (X.baseChangeField k₀ k₀')).cohomology i).frobenius x) =
        (((adicConstant k₀ l X).cohomology i).frobeniusEnd ^ Module.finrank k₀ k₀') (e x) :=
  haveI := fact_ringChar_ne_of_algebra (l := l) k₀ k₀'
  exists_linearEquiv_cohomology_adicConstant_baseChangeField k₀ l X k₀' i

end Ingredients

section PoincareDuality

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- The cohomology `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf, with its geometric Frobenius. -/
local notation "𝐇" => WeilSheaf.cohomology (adicConstant k₀ l X)

/-- The multiplier `q^d` by which Frobenius acts on `ℚ̄_ℓ(-d)`. -/
local notation "𝐪" => (Nat.card k₀ : PadicAlgCl l) ^ d

/-- Blueprint `theorem-poincare-duality-frobenius`: Poincaré duality for smooth proper schemes.

Let `X` be smooth, proper and geometrically connected of pure dimension `d` over the finite
field `k₀ = 𝔽_q`, and write `Hⁱ = Hⁱ(X ⊗ k̄, ℚ̄_ℓ)`, with geometric Frobenius `F`. There is a
trace–cup structure on `H^•` — a cup product and the trace `tr : H^{2d} ⟶ ℚ̄_ℓ(-d)`, with
pairings `⟨x, y⟩ = tr (x ⌣ y)` — such that:

1. (Trace) `tr` is an isomorphism;
2. (Finiteness) every `Hⁱ` is finite-dimensional, and `Hⁱ = 0` for `i ∉ [0, 2d]`;
3. (Pairing) the pairings `Hⁱ × H^j ⟶ ℚ̄_ℓ(-d)`, `i + j = 2d`, are perfect;
4. (Frobenius similitude) `F` acts on `ℚ̄_ℓ(-d)` by `q^d`, and `⟨F x, F y⟩ = q^d ⟨x, y⟩`;
5. (Reciprocity) `H^j ≅ (Hⁱ)^∨(-d)` Frobenius-equivariantly, and the eigenvalues of `F` on
   `H^j` are the `q^d / α`, with multiplicity, for the eigenvalues `α` of `F` on `Hⁱ`;
6. (Base change) for a finite extension `k₀'/k₀` of degree `r`, the cohomology of
   `X ×_{k₀} k₀'` is `H^•` with the geometric Frobenius of `k₀'` acting as `F^r`, and
   `⟨F^r x, F^r y⟩ = (q^r)^d ⟨x, y⟩` with `q^r = #k₀'`; the pairings, being the same, remain
   perfect.

See the module docstring for the coefficients `ℚ̄_ℓ` and the existential form. -/
theorem exists_traceCup_poincareDuality :
    ∃ T : FrobeniusModule.TraceCup.{u + 1} 𝐇 (2 * d) 𝐪,
      Function.Bijective T.trace ∧
      (∀ i, FiniteDimensional (PadicAlgCl l) (𝐇 i).carrier) ∧
      (∀ i : ℤ, i < 0 ∨ 2 * d < i → Subsingleton (𝐇 i).carrier) ∧
      (∀ (i j : ℤ) (h : i + j = 2 * d), (T.pairing i j h).IsPerfPair) ∧
      (∀ z, T.trace ((𝐇 (2 * d)).frobenius z) = 𝐪 * T.trace z) ∧
      (∀ (i j : ℤ) (h : i + j = 2 * d) x y,
        T.pairing i j h ((𝐇 i).frobenius x) ((𝐇 j).frobenius y) = 𝐪 * T.pairing i j h x y) ∧
      (∀ (i j : ℤ) (_ : i + j = 2 * d),
        Nonempty ((𝐇 j).Equiv (((𝐇 i).dual).tateTwist (Nat.card k₀) (-d))) ∧
        (𝐇 j).frobeniusEnd.charpoly.roots =
          (𝐇 i).frobeniusEnd.charpoly.roots.map fun α ↦ 𝐪 / α) ∧
      ∀ (k₀' : Type u) [Field k₀'] [Finite k₀'] [Algebra k₀ k₀'],
        haveI := fact_ringChar_ne_of_algebra (l := l) k₀ k₀'
        (∀ i, ∃ e : ((adicConstant k₀' l (X.baseChangeField k₀ k₀')).cohomology i).carrier ≃ₗ[
            PadicAlgCl l] (𝐇 i).carrier,
          ∀ x, e (((adicConstant k₀' l (X.baseChangeField k₀ k₀')).cohomology i).frobenius x) =
            ((𝐇 i).frobeniusEnd ^ Module.finrank k₀ k₀') (e x)) ∧
        ∀ (i j : ℤ) (h : i + j = 2 * d) x y,
          T.pairing i j h (((𝐇 i).frobeniusEnd ^ Module.finrank k₀ k₀') x)
              (((𝐇 j).frobeniusEnd ^ Module.finrank k₀ k₀') y) =
            (Nat.card k₀' : PadicAlgCl l) ^ d * T.pairing i j h x y := by
  obtain ⟨T, hT⟩ := exists_traceCup_isPerfect k₀ l X d
  have hq : 𝐪 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have htw (i : ℤ) : ((𝐇 i).dual).tateTwist (Nat.card k₀) (-d) = ((𝐇 i).dual).rescale 𝐪 := by
    rw [FrobeniusModule.tateTwist, neg_neg, zpow_natCast]
  refine ⟨T, hT.bijective_trace, fun _ ↦ inferInstance,
    fun _ hi ↦ subsingleton_cohomology_adicConstant k₀ l X d hi, hT.isPerfPair_pairing,
    T.trace_frobenius, T.pairing_frobenius, fun i j h ↦ ⟨htw i ▸
      T.nonempty_equiv_dual_rescale hq i j h (hT.isPerfPair_pairing i j h),
      T.roots_charpoly_frobeniusEnd hq i j h (hT.isPerfPair_pairing i j h)⟩,
    fun k₀' _ _ _ ↦ ⟨exists_linearEquiv_cohomology_baseChangeField k₀ l X k₀',
      fun i j h x y ↦ ?_⟩⟩
  rw [T.pairing_frobeniusEnd_pow]
  congr 1
  rw [Module.natCard_eq_pow_finrank (K := k₀) (V := k₀'), Nat.cast_pow, ← pow_mul, ← pow_mul,
    mul_comm d]

/-- Blueprint `corollary-cup-product-pairing`: Poincaré duality and Frobenius similitude.

For `X` smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, with
`Hⁱ = Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` and geometric Frobenius `F`, there is a trace–cup structure on `H^•`,
with pairings `⟨x, y⟩ = tr (x ⌣ y)`, such that the trace `tr : H^{2d} ⟶ ℚ̄_ℓ(-d)` is an
isomorphism and, for `i + j = 2d`:

* the pairing `Hⁱ × H^j ⟶ ℚ̄_ℓ(-d)` is perfect, equivalently it induces a Frobenius-equivariant
  isomorphism `H^j ≅ (Hⁱ)^∨(-d)`;
* `F` acts on `ℚ̄_ℓ(-d)` by `q^d`, and `⟨F x, F y⟩ = q^d ⟨x, y⟩`;
* graded commutativity gives `⟨y, x⟩ = (-1)ⁱ ⟨x, y⟩`; in middle degree `i = j = d` the pairing
  is `(-1)^d`-symmetric. -/
theorem exists_traceCup_poincarePairing :
    ∃ T : FrobeniusModule.TraceCup.{u + 1} 𝐇 (2 * d) 𝐪,
      Function.Bijective T.trace ∧
      (∀ z, T.trace ((𝐇 (2 * d)).frobenius z) = 𝐪 * T.trace z) ∧
      ∀ (i j : ℤ) (h : i + j = 2 * d),
        (T.pairing i j h).IsPerfPair ∧
        Nonempty ((𝐇 j).Equiv (((𝐇 i).dual).tateTwist (Nat.card k₀) (-d))) ∧
        (∀ x y,
          T.pairing i j h ((𝐇 i).frobenius x) ((𝐇 j).frobenius y) = 𝐪 * T.pairing i j h x y) ∧
        ∀ x y, T.pairing j i ((add_comm j i).trans h) y x = i.negOnePow • T.pairing i j h x y := by
  obtain ⟨T, htr, -, -, hp, hF, hsim, hrec, -⟩ := exists_traceCup_poincareDuality k₀ l X d
  exact ⟨T, htr, hF, fun i j h ↦ ⟨hp i j h, (hrec i j h).1, hsim i j h,
    T.pairing_comm_of_eq_two_mul rfl i j h⟩⟩

/-- Blueprint `theorem-poincare-duality-frobenius`: Poincaré duality.

For `X` smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, with
`Hⁱ = Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` and geometric Frobenius `F`, there is a trace–cup structure on `H^•`,
with trace `tr : H^{2d} ⟶ ℚ̄_ℓ(-d)` and pairings `⟨x, y⟩ = tr (x ⌣ y)`, such that:

1. (Trace) `tr` is an isomorphism;
2. (Finiteness) every `Hⁱ` is finite-dimensional, and `Hⁱ = 0` for `i ∉ [0, 2d]`;
3. (Pairing) for `i + j = 2d` the pairing `Hⁱ × H^j ⟶ ℚ̄_ℓ(-d)` is perfect, and
   `⟨y, x⟩ = (-1)ⁱ ⟨x, y⟩`;
4. (Frobenius similitude) `F` acts on `ℚ̄_ℓ(-d)` by `q^d`, and `⟨F x, F y⟩ = q^d ⟨x, y⟩`;
5. (Reciprocity) `H^j ≅ (Hⁱ)^∨(-d)` Frobenius-equivariantly, with the eigenvalues `q^d / α` on
   the left for the eigenvalues `α` of `F` on `Hⁱ`, with multiplicity;
6. (Base change) for a finite extension `k₀'/k₀` of degree `r`, the geometric Frobenius of
   `k₀'` on the cohomology of `X ×_{k₀} k₀'` is `F^r`, the pairings remain perfect, and
   `⟨F^r x, F^r y⟩ = (q^r)^d ⟨x, y⟩`, where `q^r = #k₀'`. -/
theorem poincareDuality :
    ∃ T : FrobeniusModule.TraceCup.{u + 1} 𝐇 (2 * d) 𝐪,
      Function.Bijective T.trace ∧
      (∀ i, FiniteDimensional (PadicAlgCl l) (𝐇 i).carrier) ∧
      (∀ i : ℤ, i < 0 ∨ 2 * d < i → Subsingleton (𝐇 i).carrier) ∧
      (∀ (i j : ℤ) (h : i + j = 2 * d), (T.pairing i j h).IsPerfPair ∧
        ∀ x y, T.pairing j i ((add_comm j i).trans h) y x = i.negOnePow • T.pairing i j h x y) ∧
      (∀ z, T.trace ((𝐇 (2 * d)).frobenius z) = 𝐪 * T.trace z) ∧
      (∀ (i j : ℤ) (h : i + j = 2 * d) x y,
        T.pairing i j h ((𝐇 i).frobenius x) ((𝐇 j).frobenius y) = 𝐪 * T.pairing i j h x y) ∧
      (∀ (i j : ℤ) (_ : i + j = 2 * d),
        Nonempty ((𝐇 j).Equiv (((𝐇 i).dual).tateTwist (Nat.card k₀) (-d))) ∧
        (𝐇 j).frobeniusEnd.charpoly.roots =
          (𝐇 i).frobeniusEnd.charpoly.roots.map fun α ↦ 𝐪 / α) ∧
      ∀ (k₀' : Type u) [Field k₀'] [Finite k₀'] [Algebra k₀ k₀'],
        haveI := fact_ringChar_ne_of_algebra (l := l) k₀ k₀'
        (∀ i, ∃ e : ((adicConstant k₀' l (X.baseChangeField k₀ k₀')).cohomology i).carrier ≃ₗ[
            PadicAlgCl l] (𝐇 i).carrier,
          ∀ x, e (((adicConstant k₀' l (X.baseChangeField k₀ k₀')).cohomology i).frobenius x) =
            ((𝐇 i).frobeniusEnd ^ Module.finrank k₀ k₀') (e x)) ∧
        (∀ (i j : ℤ) (h : i + j = 2 * d), (T.pairing i j h).IsPerfPair) ∧
        ∀ (i j : ℤ) (h : i + j = 2 * d) x y,
          T.pairing i j h (((𝐇 i).frobeniusEnd ^ Module.finrank k₀ k₀') x)
              (((𝐇 j).frobeniusEnd ^ Module.finrank k₀ k₀') y) =
            (Nat.card k₀' : PadicAlgCl l) ^ d * T.pairing i j h x y := by
  obtain ⟨T, htr, hfin, hvan, hp, hF, hsim, hrec, hbc⟩ := exists_traceCup_poincareDuality k₀ l X d
  exact ⟨T, htr, hfin, hvan, fun i j h ↦ ⟨hp i j h,
    T.pairing_comm_of_eq_two_mul rfl i j h⟩, hF, hsim, hrec,
    fun k₀' _ _ _ ↦ ⟨(hbc k₀').1, hp, (hbc k₀').2⟩⟩

end PoincareDuality

end WeilSheaf

end AlgebraicGeometry
