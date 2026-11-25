/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis

/-!
# Kähler differentials of a polynomial algebra over an algebra

Source: Stacks Project, Algebra, Tags 00RS, 00RV and 00RX
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace KaehlerDifferential

/-- The canonical decomposition of the differentials of `A[z₁, …, zₑ]` over `R`, and
its finite free rank consequence. Source: Stacks Project, Algebra, Tags 00RS
(`lemma-exact-sequence-differentials`), 00RV (`lemma-differentials-base-change`), and
00RX (`lemma-differentials-polynomial-ring`)
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof:
Write `B = A[z₁, …, zₑ]`, `u = mapBaseChange R A B`, and `v = map R A B B`.
The polynomial algebra `B` is formally smooth over `A`, so `H₁(L_{B/A}) = 0`.
The Jacobi–Zariski sequence (Stacks Tag 00S2) therefore makes `u` injective.
The first fundamental sequence (Tag 00RS) gives `ker v = range u`.
The polynomial basis (Tag 00RX) identifies `Ω[B⁄A]` with `Bᵉ`. Let
`s(b) = ∑ j, b j • d_R zⱼ`; then `v(s(b))` is the inverse basis-coordinate map.
Thus `(x,b) ↦ u(x) + s(b)` is injective: applying `v` determines `b`, and
injectivity of `u` determines `x`. It is surjective: for `ω`, take the coordinates
`b` of `v(ω)`; then `ω - s(b)` lies in `ker v = range u`.
Finally extend the given `Fin d` basis to `B`, take its product with the standard
`Fin e` basis, transport through the constructed equivalence, and reindex by
`Fin d ⊕ Fin e ≃ Fin (d+e)`. The argument also covers `e = 0`, `d = 0`, and zero rings.
-/
theorem exists_polynomial_extension_equiv
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] (e : ℕ) :
    (∃ E : ((MvPolynomial (Fin e) A ⊗[A] KaehlerDifferential R A) ×
        (Fin e → MvPolynomial (Fin e) A)) ≃ₗ[MvPolynomial (Fin e) A]
          KaehlerDifferential R (MvPolynomial (Fin e) A),
      ∀ (x : MvPolynomial (Fin e) A ⊗[A] KaehlerDifferential R A)
        (b : Fin e → MvPolynomial (Fin e) A),
        E (x, b) = mapBaseChange R A (MvPolynomial (Fin e) A) x +
          ∑ j : Fin e, b j • D R (MvPolynomial (Fin e) A) (MvPolynomial.X j)) ∧
    (∀ d : ℕ, Nonempty (Module.Basis (Fin d) A (KaehlerDifferential R A)) →
      Nonempty (Module.Basis (Fin (d + e)) (MvPolynomial (Fin e) A)
        (KaehlerDifferential R (MvPolynomial (Fin e) A)))) := by
  classical
  let B := MvPolynomial (Fin e) A
  let u := mapBaseChange R A B
  let v := map R A B B
  have hu : Function.Injective u := by
    apply (LinearMap.injective_iff_eq_zero_of_exact
      (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B)).mpr
    ext x
    simp only [Subsingleton.elim x 0, map_zero]
  let s : (Fin e → B) →ₗ[B] KaehlerDifferential R B :=
    { toFun := fun b ↦ ∑ j : Fin e, b j • D R B (MvPolynomial.X j)
      map_add' := by intro b c; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro a b; simp [mul_smul, Finset.smul_sum] }
  let q := (mvPolynomialBasis A (Fin e)).equivFun
  have hvs (b : Fin e → B) : v (s b) = q.symm b := by
    simp [s, v, Module.Basis.equivFun_symm_apply, q, B]
  have hvu (x : B ⊗[A] KaehlerDifferential R A) : v (u x) = 0 :=
    (exact_mapBaseChange_map R A B (u x)).mpr ⟨x, rfl⟩
  let f : ((B ⊗[A] KaehlerDifferential R A) × (Fin e → B)) →ₗ[B]
      KaehlerDifferential R B :=
    u.comp (LinearMap.fst B _ _) + s.comp (LinearMap.snd B _ _)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hb : x.2 = y.2 := q.symm.injective (by
        simpa only [f, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.fst_apply, LinearMap.snd_apply, map_add, hvu, hvs, zero_add]
          using congrArg v h)
      exact Prod.ext (hu (by
        simpa only [f, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.fst_apply, LinearMap.snd_apply, hb, add_left_inj] using h)) hb
    · intro ω
      let b := q (v ω)
      obtain ⟨x, hx⟩ := (exact_mapBaseChange_map R A B (ω - s b)).mp (by
        rw [map_sub, hvs]; simp [b, v])
      exact ⟨(x, b), by
        change u x + s b = ω
        rw [hx, sub_add_cancel]⟩
  let E := LinearEquiv.ofBijective f hf
  refine ⟨⟨E, fun x b ↦ rfl⟩, ?_⟩
  intro d ⟨basis⟩
  exact ⟨(((basis.baseChange B).prod (Pi.basisFun B (Fin e))).map E).reindex
    finSumFinEquiv⟩

end KaehlerDifferential
