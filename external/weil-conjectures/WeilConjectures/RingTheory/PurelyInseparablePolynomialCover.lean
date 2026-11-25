/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import WeilConjectures.RingTheory.FiniteFractionRootSubstitution

/-!
# A coefficient-root cover for a purely inseparable polynomial field extension

Source: Stacks Project, Algebra, Lemma 10.161.13 (Tag 032O), second assertion.
-/

@[expose] public section

universe u
set_option autoImplicit false

private theorem extend_from_basis_roots
    (F L M : Type u) [Field F] [Field L] [Field M] [Algebra F L]
    (p n m : ℕ) [Fact p.Prime] [CharP M p]
    (b : Module.Basis (Fin m) F L) (φ : L →+* F)
    (hφ : ∀ c : F, φ (algebraMap F L c) = c ^ (p ^ n))
    (h : F →+* M) (z : Fin m → M) (hz : ∀ i, z i ^ (p ^ n) = h (φ (b i))) :
    ∃ f : L →+* M, ∀ c : F, f (algebraMap F L c) = h c := by
  classical
  let f₀ (y : L) : M := ∑ i, h (b.repr y i) * z i
  have hp (y : L) : f₀ y ^ (p ^ n) = h (φ y) := by
    dsimp only [f₀]
    rw [sum_pow_char_pow]
    simp only [mul_pow, hz, ← map_pow, ← map_mul, ← map_sum]
    congr 1
    conv_rhs => rw [← b.sum_repr y]
    simp only [map_sum, Algebra.smul_def, map_mul, hφ]
  have hinj : Function.Injective (fun x : M ↦ x ^ (p ^ n)) :=
    (iterateFrobenius M p n).injective
  let f : L →+* M :=
    { toFun := f₀
      map_zero' := hinj (by simp only [hp, map_zero, zero_pow (pow_ne_zero n
        (Fact.out : p.Prime).ne_zero)])
      map_one' := hinj (by simp [hp])
      map_add' := fun x y ↦ hinj (by
        dsimp only
        rw [hp, add_pow_char_pow, hp, hp, map_add, map_add])
      map_mul' := fun x y ↦ hinj (by
        dsimp only
        rw [hp, mul_pow, hp, hp, map_mul, map_mul]) }
  refine ⟨f, fun c ↦ hinj ?_⟩
  change f₀ (algebraMap F L c) ^ (p ^ n) = (h c) ^ (p ^ n)
  rw [hp, hφ, map_pow]

/-- A finite purely inseparable extension of `Frac(R[X])` embeds in the fraction
field of a polynomial ring over the integral closure of R in a finite coefficient
extension. The map sends X to a positive power of the new variable. No Japanese,
Noetherian, or normality hypothesis on R is required.

Source: Stacks Project, Algebra, Lemma 10.161.13 (Tag 032O), coefficient-root cover
in the proof of the second assertion.
(blueprint: lem-weil-pbc-purely-inseparable-polynomial-cover).

Proof: Put F = Frac(R[X]). The finite purely inseparable extension has a common
exponent n. Its descended iterated Frobenius is a ring map φ : L → F satisfying
φ(c) = c^(p^n) for c in F. Choose a finite F-basis b of L. Apply the finite-fraction
root-substitution theorem to the family φ(b_i): it constructs a finite coefficient
extension E, the substitution map h : F → Frac(A[T]) with A = integralClosure R E,
and elements z_i with z_i^(p^n) = h(φ(b_i)). Explicitly set
f(y) = Σ_i h((b.repr y)_i) z_i. The Frobenius sum and product identities and the
basis expansion show f(y)^(p^n) = h(φ(y)). Since iterated Frobenius is injective in
the target field, this identity proves that f preserves zero, one, addition and
multiplication, and f(c) = h(c) for every c in F. The scalar-tower identity and the
substitution formula for h give the displayed equation on R[X]. The exponent
q = p^n is positive, and every construction preserves the universe of R. -/
theorem exists_purelyInseparable_polynomial_cover
    (R : Type u) [CommRing R] [IsDomain R]
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing (Polynomial R)) p]
    (L : Type u) [Field L] [Algebra (FractionRing (Polynomial R)) L]
    [Algebra (Polynomial R) L] [IsScalarTower (Polynomial R) (FractionRing (Polynomial R)) L]
    [FiniteDimensional (FractionRing (Polynomial R)) L]
    [IsPurelyInseparable (FractionRing (Polynomial R)) L] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra (FractionRing R) E) (_ : Algebra R E)
      (_ : IsScalarTower R (FractionRing R) E) (_ : FiniteDimensional (FractionRing R) E),
    ∃ q : ℕ, 0 < q ∧
      ∃ f : L →+* FractionRing (Polynomial (integralClosure R E)),
        ∀ a : Polynomial R,
          f (algebraMap (Polynomial R) L a) =
            algebraMap (Polynomial (integralClosure R E))
              (FractionRing (Polynomial (integralClosure R E)))
              (Polynomial.eval₂RingHom
                (Polynomial.C.comp (algebraMap R (integralClosure R E)))
                (Polynomial.X ^ q) a) := by
  classical
  let F := FractionRing (Polynomial R)
  let n := IsPurelyInseparable.exponent F L
  let φ : L →+* F := IsPurelyInseparable.iterateFrobenius F L p (le_refl n)
  let b := Module.finBasis F L
  obtain ⟨E, hE, aKE, aRE, ht, hfin, h, hpoly, hroots⟩ :=
    exists_finite_fraction_root_substitution R p n (Module.finrank F L)
      (fun i ↦ φ (b i))
  let := hE
  let := aKE
  let := aRE
  let := ht
  let := hfin
  let M := FractionRing (Polynomial (integralClosure R E))
  have : CharP M p := charP_of_injective_ringHom h.injective p
  choose z hz using hroots
  obtain ⟨f, hf⟩ := extend_from_basis_roots F L M p n (Module.finrank F L) b φ
    (IsPurelyInseparable.iterateFrobenius_algebraMap L p (le_refl n)) h z hz
  refine ⟨E, hE, aKE, aRE, ht, hfin, p ^ n, pow_pos (Fact.out : p.Prime).pos _,
    f, ?_⟩
  intro a
  rw [IsScalarTower.algebraMap_apply (Polynomial R) F L, hf]
  exact hpoly a
