/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import Mathlib.Topology.JacobsonSpace

/-!

# Charts for Deligne's induction for the change of trait

Geometric inputs of the proof of `NearbyCyclesModel.traitChangeInvariance`:

* `AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace.exists_isAffineOpen`: the charts of a
  morphism locally embedding into affine spaces may be taken on affine opens;
* `AlgebraicGeometry.AffineSpace.isImmersion_lift_isPullback_map`: a chart restricts to a chart of
  a cartesian fibre;
* `AlgebraicGeometry.not_isClosed_singleton_of_isOpenImmersion`: a point of an open of a Jacobson
  scheme which is not closed in the scheme is not closed in the open.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The charts of a morphism locally embedding into affine spaces may be taken on affine opens:
shrink the chart to an affine open neighbourhood of the point. -/
lemma Scheme.Hom.LocallyEmbedsInAffineSpace.exists_isAffineOpen {T S : Scheme.{u}}
    {q : T ⟶ S} {m : ℕ} (h : q.LocallyEmbedsInAffineSpace m) (x : T) :
    ∃ (U : T.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (ι : Type u) (_ : Finite ι)
      (c : U.toScheme ⟶ 𝔸(ι; S)), Nat.card ι ≤ m ∧ IsImmersion c ∧
        c ≫ 𝔸(ι; S) ↘ S = U.ι ≫ q := by
  obtain ⟨V, hx, ι, hι, c, hc, hi, hq⟩ := h x
  obtain ⟨U, hU, hxU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens hx
  refine ⟨U, hU, hxU, ι, hι, T.homOfLE hUV ≫ c, hc, inferInstance, ?_⟩
  rw [Category.assoc, hq, Scheme.homOfLE_ι_assoc]

/-- **A chart restricts to a cartesian fibre.** If `i : X ⟶ Z` is the base change of `q : Z ⟶ S`
along `t : S' ⟶ S` and `c : Z ⟶ 𝔸(ι; S)` is an immersion over `S`, then the induced morphism
`X ⟶ 𝔸(ι; S') = 𝔸(ι; S) ×_S S'` is an immersion, being the base change of `c`. -/
lemma AffineSpace.isImmersion_lift_isPullback_map {X Z S S' : Scheme.{u}} {ι : Type u}
    {i : X ⟶ Z} {p : X ⟶ S'} {q : Z ⟶ S} {t : S' ⟶ S} (h : IsPullback i p q t)
    (c : Z ⟶ 𝔸(ι; S)) [IsImmersion c] (hc : c ≫ 𝔸(ι; S) ↘ S = q) :
    IsImmersion ((AffineSpace.isPullback_map (n := ι) t).lift (i ≫ c) p
      (by rw [Category.assoc, hc, h.w])) := by
  subst hc
  exact MorphismProperty.of_isPullback (IsPullback.of_bot' h (AffineSpace.isPullback_map t))
    inferInstance

/-- In a Jacobson scheme, a point of an open subscheme whose image is not closed is not closed in
the open subscheme: a closed point of an open is locally closed, hence closed. -/
lemma not_isClosed_singleton_of_isOpenImmersion {U X : Scheme.{u}} [JacobsonSpace X]
    (f : U ⟶ X) [IsOpenImmersion f] {x : U} (hx : ¬ IsClosed ({f x} : Set X)) :
    ¬ IsClosed ({x} : Set U) := fun h ↦ hx <| isClosed_singleton_of_isLocallyClosed_singleton <| by
  rw [← Set.image_singleton]
  exact h.isLocallyClosed.image f.isOpenEmbedding.isInducing
    f.isOpenEmbedding.isOpen_range.isLocallyClosed

end AlgebraicGeometry
