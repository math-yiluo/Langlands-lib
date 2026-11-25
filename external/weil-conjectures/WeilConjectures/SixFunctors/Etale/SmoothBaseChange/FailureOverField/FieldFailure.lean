/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Counterexamples to base change over a field

The data of a counterexample to `BC(p, Λ, q)` living over a field, after an affine base change
of `p`, bundled as `AlgebraicGeometry.Etale.FieldFailure`. That such a counterexample exists as
soon as `BC(p, Λ, q)` fails is proved in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection`.

## Main definitions

- `AlgebraicGeometry.Etale.FieldFailure`: a counterexample to `BC(p, Λ, q)` living over a
  field, after an affine base change of `p`.

## Main statements

- `AlgebraicGeometry.Etale.FieldFailure.isAffineHom_a`: if `S` is separated, the base change
  `S' ⟶ S` of such a counterexample is affine.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section FieldFailure

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- A counterexample to `BC(p, Λ, q)` living over a field: an affine scheme `S'` over `S`,
the base change `p' : X' ⟶ S'` of `p` along it, a field `K` over `S'`, and a sheaf `F`
of `Λ`-modules on `(Spec K)_ét` for which the degree-`q` base-change map of the geometric
fibre square is not an isomorphism. The two squares are stacked:

```
Y' -----e-----> Spec K
|                 |
h                 g
v                 v
X' -----p'-----> S'
|                 |
b                 a
v                 v
X ------p------>  S
```

When `S` is separated the base change `a : S' ⟶ S` is affine, see
`AlgebraicGeometry.Etale.FieldFailure.isAffineHom_a`. -/
structure Etale.FieldFailure (q : ℤ) where
  /-- the affine base of the counterexample -/
  S' : Scheme.{u}
  [isAffine : IsAffine S']
  /-- the base change morphism -/
  a : S' ⟶ S
  /-- the total space of the base change of `p` -/
  X' : Scheme.{u}
  /-- the base change of `p` -/
  p' : X' ⟶ S'
  /-- the morphism covering `a` -/
  b : X' ⟶ X
  /-- `p'` is the base change of `p` along `a` -/
  isPullback : IsPullback b p' p a
  /-- the field over which the failure happens -/
  K : Type u
  [field : Field K]
  /-- the point of `S'` -/
  g : Spec (CommRingCat.of K) ⟶ S'
  /-- the fibre of `p'` over that point -/
  Y' : Scheme.{u}
  /-- the projection of the fibre to the point -/
  e : Y' ⟶ Spec (CommRingCat.of K)
  /-- the projection of the fibre to `X'` -/
  h : Y' ⟶ X'
  /-- the fibre square is Cartesian -/
  isPullback_fibre : IsPullback e h g p'
  /-- the coefficient sheaf witnessing the failure -/
  F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  /-- the base-change map is not an isomorphism -/
  not_isIso : ¬ IsIso (Etale.baseChangeHomologyMap Λ isPullback_fibre q F)

variable {Λ p} in
/-- Blueprint `lemma-reduction-field--1` (last clause): if `S` is separated, the base change
`S' ⟶ S` of a counterexample over a field is affine, since `S'` is affine. -/
lemma Etale.FieldFailure.isAffineHom_a [S.IsSeparated] {q : ℤ} (F : Etale.FieldFailure Λ p q) :
    IsAffineHom F.a :=
  have := F.isAffine
  have : IsAffineHom (F.a ≫ terminal.from S) := by
    rw [terminal.comp_from]
    infer_instance
  IsAffineHom.of_comp F.a (terminal.from S)

end FieldFailure

end AlgebraicGeometry
