/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# The induction statements for base change along open immersions

The proof of blueprint `corollary-open-direct-image-over-field--2` (base change for an open
immersion `j : U ⟶ X` of schemes of finite type over a field, along the projection `X ×_K Y ⟶ X`) is
an induction on `dim X + dim Y`. This file records the two statements through which the induction
runs:

* `AlgebraicGeometry.Etale.OpenImmersionBaseChangeBelow Λ N`: the statement of
  `corollary-open-direct-image-over-field--2` for all data with `dim X + dim Y < N`;
* `AlgebraicGeometry.Etale.OpenImmersionBaseChangeAtNonClosed Λ N`: for all data with
  `dim X + dim Y ≤ N`, the base change maps are isomorphisms on the geometric stalks at the
  non-closed points of `X ×_K Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The statement of blueprint `corollary-open-direct-image-over-field--2` for all data with
`dim X + dim Y < N`: for every field `K`, every integer `n` invertible in `K` and killing `Λ`, every
open immersion `j : U ⟶ X` of schemes of finite type over `K`, every scheme `Y` of finite type over
`K` with `dim X + dim Y < N`, and the cartesian squares `W = X ×_K Y`, `V = U ×_X W`, the degree-`i`
base change maps `q₁⁻¹ R^i j_* F ⟶ R^i h_* e⁻¹ F` are isomorphisms. -/
def Etale.OpenImmersionBaseChangeBelow (N : WithBot ℕ∞) : Prop :=
  ∀ ⦃K : Type u⦄ [Field K] ⦃X U Y W V : Scheme.{u}⦄ (aX : X ⟶ Spec (.of K))
    (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y)
    (_ : IsPullback q₁ q₂ aX aY) (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ)
    (_ : IsUnit (n : K)) (_ : (n : Λ) = 0),
    topologicalKrullDim X + topologicalKrullDim Y < N →
      ∀ (i : ℤ) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso (Etale.baseChangeHomologyMap Λ sq i F)

/-- For all data as in `AlgebraicGeometry.Etale.OpenImmersionBaseChangeBelow` with
`dim X + dim Y ≤ N`, the degree-`i` base change maps are isomorphisms on the geometric stalks at
all non-closed points of `W = X ×_K Y`. -/
def Etale.OpenImmersionBaseChangeAtNonClosed (N : WithBot ℕ∞) : Prop :=
  ∀ ⦃K : Type u⦄ [Field K] ⦃X U Y W V : Scheme.{u}⦄ (aX : X ⟶ Spec (.of K))
    (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y)
    (_ : IsPullback q₁ q₂ aX aY) (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ)
    (_ : IsUnit (n : K)) (_ : (n : Λ) = 0),
    topologicalKrullDim X + topologicalKrullDim Y ≤ N →
      ∀ (z : W), ¬ IsClosed ({z} : Set W) →
        ∀ (i : ℤ) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          IsIso ((W.uliftPointSmallEtale z).sheafFiber.map
            (Etale.baseChangeHomologyMap Λ sq i F))

/-- The statement of blueprint `corollary-open-direct-image-over-field--2` for all data with
`dim X + dim Y ≤ N`. -/
def Etale.OpenImmersionBaseChangeAtMost (N : WithBot ℕ∞) : Prop :=
  ∀ ⦃K : Type u⦄ [Field K] ⦃X U Y W V : Scheme.{u}⦄ (aX : X ⟶ Spec (.of K))
    (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y)
    (_ : IsPullback q₁ q₂ aX aY) (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ)
    (_ : IsUnit (n : K)) (_ : (n : Λ) = 0),
    topologicalKrullDim X + topologicalKrullDim Y ≤ N →
      ∀ (i : ℤ) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso (Etale.baseChangeHomologyMap Λ sq i F)

variable {Λ}

lemma Etale.OpenImmersionBaseChangeBelow.mono {N M : WithBot ℕ∞} (hNM : N ≤ M)
    (H : Etale.OpenImmersionBaseChangeBelow Λ M) : Etale.OpenImmersionBaseChangeBelow Λ N :=
  fun _ _ _ _ _ _ _ aX aY _ _ _ _ j _ q₁ q₂ hW e h sq n hn hΛ hdim ↦
    H aX aY j q₁ q₂ hW e h sq n hn hΛ (hdim.trans_le hNM)

end AlgebraicGeometry
