/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitSmoothSurface
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationSmoothSurface
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.RingTheory.TangentConeInitialForms
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.AlgebraicGeometry.BlowupChartLimitColimit
public import WeilConjectures.AlgebraicGeometry.BlowupChartLimitCoordinates
public import WeilConjectures.AlgebraicGeometry.BlowupChartLimitLift

/-!
# The charts of the blow-up of the strict localization of a smooth surface

Let `S` be a smooth surface over an algebraically closed field `k` and `t` a `k`-point of `S`,
with strict localization `T = Spec R`, `R = 𝒪^{sh}_{S,t}` (blueprint
`lemma-vanishing-restrictions-after-blowing-up--1`). Then `R` is a regular local ring of dimension
`2` with residue field `k`, and there is a regular system of parameters `(x₀, y₀)` of `R`, coming
from étale coordinates of `S` at `t`, such that for every `a ∈ k` every open subscheme
`Spec (R[T]/(xT - y))[1/u]` of the chart of the blow-up of `T` at `t` for `x = x₀ + a y₀`,
`y = y₀` is an étale limit with affine transition maps of smooth `k`-surfaces (blueprint
`lemma-vanishing-restrictions-after-blowing-up--1` (1)): it is the base change to `T` of the
corresponding chart of the blow-up of an affine étale neighbourhood `V` of `t` in `S`, which is
étale over the affine plane, and `T` is the limit of the affine étale neighbourhoods of `t` over
`V`.

## Main results

- `AlgebraicGeometry.Scheme.exists_isEtaleLimitOfSmoothSurfaces_blowupChart`: the charts of the
  blow-up are étale limits of smooth surfaces.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Over (Spec (.of k)))
  (t : Spec (.of k) ⟶ S.left)

variable [SmoothOfRelativeDimension 2 S.hom]

/-- **The charts of the blow-up of the strict localization of a smooth surface are étale limits
of smooth surfaces** (blueprint `lemma-vanishing-restrictions-after-blowing-up--1` (1), in a chart).
There is a regular system of parameters `(x₀, y₀)` of `R = 𝒪^{sh}_{S,t}` such that for every `a ∈ k`
and every `u` in the chart `R[T]/(xT - y)`, `x = x₀ + a y₀`, `y = y₀`, of the blow-up of `Spec R` at
its closed point, the `k`-scheme `Spec (R[T]/(xT - y))[1/u]` is an étale limit of smooth
surfaces. -/
theorem exists_isEtaleLimitOfSmoothSurfaces_blowupChart (ht : t ≫ S.hom = 𝟙 _) :
    letI := strictHenselizationAlgebra S t
    ∃ x₀ y₀ : strictHenselization t,
      maximalIdeal (strictHenselization t) = Ideal.span {x₀, y₀} ∧
      ∀ (a : k) (u : blowupChart (x₀ + algebraMap k (strictHenselization t) a * y₀) y₀),
        IsEtaleLimitOfSmoothSurfaces (Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap k (Localization.Away u))))) := by
  let := strictHenselizationAlgebra S t
  obtain ⟨j₀, g, hg, hgC, hmax⟩ := exists_etaleCoordinates_strictHenselization S t ht
  have : IsCofiltered (SmallModel.{u} (strictHenselizationNeighbourhoods t)) :=
    (strictHenselizationAffineProperties t).2.1
  let D := strictHenselizationAffineDiagram t
  let c := smallStrictHenselizationCocone t
  have hc : IsColimit c := isColimitSmallStrictHenselizationCocone t
  have hD : ∀ ⦃i j : (SmallModel.{u} (strictHenselizationNeighbourhoods t))ᵒᵖ⦄ (f : i ⟶ j),
      (D.map f).hom.Etale := fun _ _ f ↦ etale_strictHenselizationAffineDiagram_map t f
  let ι₀ : D.obj (Opposite.op j₀) ⟶ strictHenselization t := c.ι.app (Opposite.op j₀)
  let x₀ : strictHenselization t := ι₀.hom (g.hom (MvPolynomial.X 0))
  let y₀ : strictHenselization t := ι₀.hom (g.hom (MvPolynomial.X 1))
  refine ⟨x₀, y₀, hmax, fun a u ↦ ?_⟩
  -- the coordinates `x = x₀ + a y₀`, `y = y₀` at the stage `j₀`
  let g' : CommRingCat.of (MvPolynomial (Fin 2) k) ⟶ D.obj (Opposite.op j₀) :=
    CommRingCat.ofHom (g.hom.comp (affineSubst a 0 0).toRingHom)
  have hg' : g'.hom.Etale := etale_comp_affineSubst hg a 0 0
  have hx : ι₀.hom (g'.hom (MvPolynomial.X 0)) =
      x₀ + algebraMap k (strictHenselization t) a * y₀ := by
    simp [g', x₀, y₀, ← hgC, ι₀]
    rfl
  have hy : ι₀.hom (g'.hom (MvPolynomial.X 1)) = y₀ := by
    simp [g', y₀]
    rfl
  obtain ⟨k₁, f, uA, hx₁, hy₁, rfl⟩ := exists_blowupChart_lift hc (Opposite.op j₀) hx hy u
  -- the chart over the stage `k₁`, whose base change to `R` is the given chart
  let g₁ : CommRingCat.of (MvPolynomial (Fin 2) k) ⟶ D.obj k₁ := g' ≫ D.map f
  have hg₁ : g₁.hom.Etale := RingHom.Etale.stableUnderComposition _ _ hg' (hD f)
  let : Algebra k c.pt := strictHenselizationAlgebra S t
  have hk (r : k) : (c.ι.app k₁).hom (g₁.hom (MvPolynomial.C r)) = algebraMap k c.pt r := by
    have h₁ := congr($(c.w f).hom (g'.hom (MvPolynomial.C r)))
    have h₂ : (c.ι.app (Opposite.op j₀)).hom (g'.hom (MvPolynomial.C r)) =
        (c.ι.app (Opposite.op j₀)).hom (g.hom (MvPolynomial.C r)) := by
      simp [g']
      rfl
    exact h₁.trans (h₂.trans (hgC r))
  exact isEtaleLimitOfSmoothSurfaces_blowupChart_away_of_isColimit hc hD k₁ g₁ hg₁ hk hx₁ hy₁ uA

end AlgebraicGeometry.Scheme
