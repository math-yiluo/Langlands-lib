/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.ProetaleTopologicalInvariance

/-!
# Topological invariance of the small pro-étale topos

Let `r : X ⟶ Y` be a universal homeomorphism of schemes. Base change `V ↦ V ×_Y X` along `r`
exhibits the small pro-étale site of `Y` as a dense subsite of that of `X`
(`AlgebraicGeometry.Scheme.ProEt.isDenseSubsite_overPullback`): it preserves and reflects
pro-étale coverings, because `r` and all its base changes are homeomorphisms, and it is locally
essentially surjective, locally full and locally faithful. Hence
the pushforward `r_*` and the pullback `r^*` are mutually quasi-inverse equivalences of the
categories of pro-étale sheaves. This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`, where the
corresponding statement for the small étale site is [Stacks 04DZ].

## Main statements

- `AlgebraicGeometry.ProEtale.isEquivalence_lowerStar_of_isUniversalHomeomorphism`: the
  pushforward along a universal homeomorphism is an equivalence of categories of pro-étale
  sheaves.
- `AlgebraicGeometry.ProEtale.isEquivalence_upperStar_of_isUniversalHomeomorphism`: so is the
  pullback, being left adjoint to it.

## Implementation notes

`ProEtale.isEquivalence_lowerStar_of_isUniversalHomeomorphism` is the comparison lemma
(`CategoryTheory.Functor.IsDenseSubsite`) applied to the dense subsite of
`WeilConjectures.AlgebraicGeometry.Sites.ProetaleTopologicalInvariance`. Unlike the étale case
(`AlgebraicGeometry.Scheme.Hom.isEquivalence_etale`), base change is not shown to be an
equivalence of the underlying categories of the small pro-étale sites.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r]

/-- **Topological invariance of the small pro-étale topos**: for a universal homeomorphism
`r : X ⟶ Y`, the pushforward `r_*`, restriction along base change `V ↦ V ×_Y X`, is an
equivalence between the categories of `A`-valued pro-étale sheaves on `X` and on `Y`, base
change being a dense subsite (blueprint: `lemma-comparison-via-relative-frobenius--1`). -/
theorem isEquivalence_lowerStar_of_isUniversalHomeomorphism : ((r)_*[A]).IsEquivalence := by
  have := Scheme.ProEt.isDenseSubsite_overPullback r
  have : ∀ V, HasLimitsOfShape
      (StructuredArrow V (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).op) A := fun _ ↦
    have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
    inferInstance
  unfold lowerStar
  infer_instance

/-- **Topological invariance of the small pro-étale topos**: for a universal homeomorphism
`r : X ⟶ Y`, the pullback `r^*` is an equivalence between the categories of `A`-valued
pro-étale sheaves on `Y` and on `X`, being left adjoint to the equivalence `r_*`
(blueprint: `lemma-comparison-via-relative-frobenius--1`). -/
theorem isEquivalence_upperStar_of_isUniversalHomeomorphism : ((r)^*[A]).IsEquivalence :=
  have := isEquivalence_lowerStar_of_isUniversalHomeomorphism A r
  (upperStarLowerStarAdjunction A r).isEquivalence_left_of_isEquivalence_right

end AlgebraicGeometry.ProEtale
