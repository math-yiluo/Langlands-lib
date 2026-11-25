/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FrobeniusContracting
public import WeilConjectures.Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.TraceFormula.CurveLocal.Model
public import WeilConjectures.TraceFormula.Frobenius

/-!

# The strictly local model at a Frobenius fixed point

Let `X` be a separated quasi-compact smooth curve over an algebraically closed field `k`, with a
model `X₀` over a finite field `k₀` and model Frobenius `Φ` (`IsModelFrobenius Φ f₀ p`), and let
`x` be a rational point of `X` fixed by the iterate `Φ_m`, `m ≥ 1`. Then `(X, Φ_m, x)` is a
strictly local model in the sense of `AlgebraicGeometry.Etale.CurveLocalModel`
(`AlgebraicGeometry.Etale.CurveLocalModel.ofModelFrobenius`): the contraction
`Φ_m^♯ 𝔪_x ⊆ 𝔪_x²` is `AlgebraicGeometry.map_maximalIdeal_stalkMap_le_sq_of_isFrobenius`
(blueprint `lemma-local-term-restriction-map--1`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale.CurveLocalModel

open ProEtale.CondensedRing

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Over (Spec (.of k))}
  [QuasiCompact X.hom] [IsSeparated X.hom] [SmoothOfRelativeDimension 1 X.hom]
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- **The strictly local model at a Frobenius fixed point** (blueprint
`lemma-local-term-restriction-map--1`): for the model Frobenius `Φ` of a smooth curve `X` over `k`,
`m ≥ 1` and a rational point `x` fixed by `Φ_m`, the curve `X` with the endomorphism `Φ_m` and
the fixed point `x`. The contraction `Φ_m^♯ 𝔪_x ⊆ 𝔪_x²` holds since
`Φ_m^♯ (t - a) = (t - a)^{q^m}` in a local coordinate. -/
noncomputable def ofModelFrobenius (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) : CurveLocalModel k where
  X := X.left
  f := X.hom
  h := (frobeniusIterate Φ m).left
  h_comp := Over.w (frobeniusIterate Φ m)
  y := x.left
  y_comp := Over.w x
  y_comp_h := congrArg CommaMorphism.left hx
  map_maximalIdeal_le := by
    obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
    refine map_maximalIdeal_stalkMap_le_sq_of_isFrobenius hΦ.isPullback hm (hF₀.pow f₀ m)
      (Over.w (frobeniusIterate Φ m)) ?_ x.left (Over.w x) (congrArg CommaMorphism.left hx) _
    rw [frobeniusIterate_left]
    exact End.asHom_pow_comp_eq_comp_asHom_pow hp m

variable (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m) (x : RationalPoint X)
  (hx : x ≫ frobeniusIterate Φ m = x)

omit [IsAlgClosed k] in
@[simp]
lemma ofModelFrobenius_X : (ofModelFrobenius hΦ hm x hx).X = X.left :=
  rfl

omit [IsAlgClosed k] in
@[simp]
lemma ofModelFrobenius_f : (ofModelFrobenius hΦ hm x hx).f = X.hom :=
  rfl

omit [IsAlgClosed k] in
@[simp]
lemma ofModelFrobenius_h : (ofModelFrobenius hΦ hm x hx).h = (frobeniusIterate Φ m).left :=
  rfl

omit [IsAlgClosed k] in
@[simp]
lemma ofModelFrobenius_y : (ofModelFrobenius hΦ hm x hx).y = x.left :=
  rfl

end AlgebraicGeometry.Etale.CurveLocalModel
