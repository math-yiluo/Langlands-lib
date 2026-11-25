/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange.BCProperty

/-!
# A failure of base change produces an integral normal base

Blueprint `lemma-kunneth-finite-direct-image--1` (Stacks 0F1D): if `BC(f, n, q - 1)` holds and
`BC(f, n, q)` fails for some `q ≥ 1`, there is a base change of `f` to an affine, integral, normal
scheme `S'` with algebraically closed function field and an algebraically closed field `K` over the
function field such that `R^q h_* (ℤ/d) ≠ 0` on the fibre over `Spec K` for some `d ∣ n`. This is
the failure lemma `AlgebraicGeometry.Etale.exists_isPullback_not_isZero_higherDirectImage` (Stacks
0F08) of the smooth base change theorem, read in the language of
`AlgebraicGeometry.Etale.KunnethBaseChangeProperty`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- Blueprint `lemma-kunneth-finite-direct-image--1`: failure of base change produces an integral
normal base.

Let `f : X ⟶ S` be a morphism of schemes and `n` an integer invertible on `S`. If for some
`q ≥ 1` the base change property `BC(f, n, q - 1)` holds but `BC(f, n, q)` does not, there are
cartesian squares
```
X <-b- X' <-h- Y
|      |       |
f      f'      e
v      v       v
S <-a- S' <--- Spec K
```
with `S'` affine, integral and normal with algebraically closed function field, `K` an
algebraically closed field over that function field, `Spec K ⟶ S'` the induced map to the
generic point, and an integer `d ∣ n` with `R^q h_* (ℤ/d) ≠ 0`.

As in Stacks (Tag 0F08, used in the proof of Tag 0F1D), the field `K` is an algebraically closed
extension of the function field `K'` of `S'`, rather than `K'` itself as in the blueprint
statement. -/
theorem Etale.exists_isPullback_not_isZero_higherDirectImage_of_kunnethBaseChangeProperty
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.KunnethBaseChangeProperty f n (q - 1))
    (hfail : ¬ Etale.KunnethBaseChangeProperty f n q) :
    ∃ (S' X' : Scheme.{u}) (a : S' ⟶ S) (b : X' ⟶ X) (f' : X' ⟶ S') (_ : IsPullback b f' f a)
      (_ : IsAffine S') (_ : IsIntegral S')
      (_ : ∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x))
      (_ : IsAlgClosed S'.functionField) (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (i : S'.functionField ⟶ CommRingCat.of K) (Y : Scheme.{u}) (e : Y ⟶ Spec (.of K))
      (h : Y ⟶ X') (_ : IsPullback e h (Spec.map i ≫ S'.fromSpecStalk (genericPoint S')) f')
      (d : ℕ), d ∣ n ∧ ¬ IsZero (Etale.higherDirectImage (ULift.{u + 1} (ZMod n)) h q
        (Etale.constantModSheaf (ULift.{u + 1} (ZMod n)) Y d)) := by
  have hfail' : ¬ Etale.UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f q := by
    intro H
    refine hfail fun q' hq' ↦ ?_
    rcases hq'.lt_or_eq with h | rfl
    · exact hprev q' (by omega)
    · exact H
  have hΛ : ((n : ℕ) : ULift.{u + 1} (ZMod n)) = 0 := by
    ext
    simp
  exact Etale.exists_isPullback_not_isZero_higherDirectImage _ f n hn hΛ q hq
    (fun q' hq' ↦ hprev q' (by omega)) hfail'

end AlgebraicGeometry
