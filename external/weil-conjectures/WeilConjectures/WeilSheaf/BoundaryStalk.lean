/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.LowerStarTensorPow
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# Boundary stalks of middle extensions of lisse Weil sheaves

Let `j : U₀ ⟶ C₀` be a dense open immersion into a smooth curve over `k₀` and `F` a lisse Weil
sheaf on `U₀`. At a closed point `x` of `C₀` the stalk of the middle extension `j_* F` is the
module of inertia invariants of the geometric generic stalk `F_η̄`, Frobenius-equivariantly
(blueprint `lemma-boundary-stalk--1`). In particular, if `v` is an eigenvector of the
local Frobenius on `(j_* F)_x̄`, then `v ^ {⊗ k}` is an inertia invariant eigenvector of
`F^{⊗ k}`, so the `k`-th powers of the boundary eigenvalues of `j_* F` are boundary eigenvalues
of `j_* (F^{⊗ k})`.

The proof avoids inertia groups: it is the case of an open immersion of
`AlgebraicGeometry.WeilSheaf.hasEigenvalue_stalkAt_lowerStar_tensorPow`, which builds the
eigenvector `v^{⊗ k}` from Frobenius-compatible pairings `j_* F ⊗ j_* F^{⊗ k} ⟶ j_* F^{⊗ (k + 1)}`
and shows that it is nonzero by a germ computation.

## Main statements

- `AlgebraicGeometry.WeilSheaf.hasEigenvalue_stalk_directImage_tensorPow`: powers of boundary
  eigenvalues are boundary eigenvalues of tensor powers.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Powers of boundary eigenvalues.** Let `j : U₀ ⟶ C₀` be a quasi-compact open immersion of
`k₀`-schemes, `F` a lisse Weil sheaf on `U₀` and `x` a closed point of `C₀`. If `α` is an
eigenvalue of the local Frobenius on the stalk `(j_* F)_x̄`, then `α ^ k` is an eigenvalue of the
local Frobenius on `(j_* (F^{⊗ k}))_x̄` for every `k`.

The eigenvector `v ^ {⊗ k}` is built from the pairings `j_* F ⊗ j_* F^{⊗ k} ⟶ j_* F^{⊗ (k + 1)}`
and is nonzero since `v` is the germ of a section `σ` of the lisse sheaf `F` over a pro-étale
neighbourhood, whose tensor powers do not vanish
(`AlgebraicGeometry.WeilSheaf.hasEigenvalue_stalkAt_lowerStar_tensorPow`).
(blueprint: `proposition-weights-j-boundary-points--1`, Step 4) -/
theorem hasEigenvalue_stalk_directImage_tensorPow {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l U} (hF : F.IsLisse)
    (x : C.finitePoints) {α : PadicAlgCl l}
    (hα : (((directImage j).obj F).stalk x).frobeniusEnd.HasEigenvalue α) (k : ℕ) :
    (((directImage j).obj (F.tensorPow hF k)).stalk x).frobeniusEnd.HasEigenvalue (α ^ k) :=
  hasEigenvalue_stalkAt_lowerStar_tensorPow j _ hF _ _ hα k

end AlgebraicGeometry.WeilSheaf
