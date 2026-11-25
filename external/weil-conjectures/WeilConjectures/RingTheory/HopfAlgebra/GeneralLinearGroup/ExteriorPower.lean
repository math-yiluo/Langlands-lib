/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.ExteriorPower.Basis
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup

/-!
# Exterior powers of `GL_n` are polynomial

The exterior power `⋀^s : GL n k →* GL (powersetCard n s) k` is given by polynomials in the
matrix entries: it is induced by an algebra map of coordinate rings
`k[GL (powersetCard n s)] → k[GL n]`, namely evaluation at the exterior power of the generic
matrix.

## Main results

- `Matrix.GeneralLinearGroup.exists_algHom_comp_eq_evalAlgHom_exteriorPower`: the exterior power
  is polynomial.

## Blueprint

`Matrix.GeneralLinearGroup.exists_algHom_comp_eq_evalAlgHom_exteriorPower` is part of
`lemma-restriction-normal-subgroup`.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [LinearOrder n] {k : Type*} [Field k]

/-- The exterior power `GL n k →* GL (powersetCard n s) k` is given by polynomials: there is an
algebra map `φ` of coordinate rings with `evalAlgHom (⋀^s g) = evalAlgHom g ∘ φ`.
(blueprint: `lemma-restriction-normal-subgroup`) -/
theorem exists_algHom_comp_eq_evalAlgHom_exteriorPower (s : ℕ) :
    ∃ φ : CoordinateRing (Set.powersetCard n s) k →ₐ[k] CoordinateRing n k,
      ∀ g : GL n k, (evalAlgHom g).comp φ = evalAlgHom (exteriorPower s g) := by
  refine ⟨evalAlgHom (exteriorPower s (genericUnit n k)), fun g ↦ ?_⟩
  rw [← evalAlgHom_map, ← exteriorPower_map]
  congr 2
  ext i j
  simp

end Matrix.GeneralLinearGroup
