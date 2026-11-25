/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup

/-!
# The Kronecker square of `GL_n` is polynomial

The homomorphism `g ↦ g ⊗ₖ g : GL n k →* GL (n × n) k`, which describes the action of `GL n k` on
the tensor square `kⁿ ⊗ kⁿ`, is given by polynomials in the matrix entries: it is induced by an
algebra map of coordinate rings `k[GL (n × n)] → k[GL n]`, namely evaluation at the Kronecker
square of the generic matrix.

## Main results

- `Matrix.GeneralLinearGroup.exists_algHom_comp_eq_evalAlgHom_kroneckerHom`: the Kronecker square
  is polynomial.

## Blueprint

`Matrix.GeneralLinearGroup.exists_algHom_comp_eq_evalAlgHom_kroneckerHom` is part of
`lemma-restriction-normal-subgroup`.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

/-- The Kronecker square `g ↦ g ⊗ₖ g : GL n k →* GL (n × n) k` is given by polynomials: there is
an algebra map `φ` of coordinate rings with `evalAlgHom (g ⊗ₖ g) = evalAlgHom g ∘ φ`.
(blueprint: `lemma-restriction-normal-subgroup`) -/
theorem exists_algHom_comp_eq_evalAlgHom_kroneckerHom :
    ∃ φ : CoordinateRing (n × n) k →ₐ[k] CoordinateRing n k,
      ∀ g : GL n k, (evalAlgHom g).comp φ = evalAlgHom (kroneckerHom (g, g)) := by
  refine ⟨evalAlgHom (kroneckerHom (genericUnit n k, genericUnit n k)), fun g ↦ ?_⟩
  rw [← evalAlgHom_map, ← kroneckerHom_map]
  have : map (evalAlgHom (k := k) g).toRingHom (genericUnit n k) = g := by
    ext i j
    simp
  rw [this]

end Matrix.GeneralLinearGroup
