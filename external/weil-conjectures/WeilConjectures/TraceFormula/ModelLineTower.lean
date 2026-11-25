/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineTower
public import WeilConjectures.TraceFormula.CoefficientMorphismPushforward
public import WeilConjectures.TraceFormula.ModelProjectiveImmersion

/-!

# Morphisms of models into towers of projective lines

Let `Φ` be the model Frobenius of `X = X₀ ×_{k₀} k`. A `k₀`-morphism `f₀' : X₀ ⟶ P` to a scheme
`P` of finite type over `k₀` base-changes to a morphism `f : X ⟶ Y = P ×_{k₀} k`, commuting with
the model Frobenii (`ProEtale.CondensedRing.IsModelFrobenius.exists_comp_eq_comp`). Two cases are
used in the proof of the trace formula for Frobenius correspondences (blueprint
`theorem-trace-formula-frobenius-correspondence`):

* an immersion `X₀ ⟶ ℙ¹_{k₀} ×_{k₀} ⋯ ×_{k₀} ℙ¹_{k₀}` of an affine model
  (`AlgebraicGeometry.Scheme.exists_isImmersion_projectiveLineTower`), whose fibres over the
  rational points of `Y` are empty or a point
  (`ProEtale.CondensedRing.isClosedImmersion_pullback_hom_of_isImmersion`);
* the projections `ℙ¹_B ⟶ B` of the tower, whose fibres over the rational points are proper
  smooth curves (`ProEtale.CondensedRing.smoothOfRelativeDimension_pullback_hom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} {Φ : X ⟶ X}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}

/-- **Morphisms of models base-change** (blueprint
`lemma-comparison-via-relative-frobenius--text-1`, `lemma-comparison-via-relative-frobenius`): for
the model Frobenius `Φ` of `X = X₀ ×_{k₀} k` and a `k₀`-morphism `f₀' : X₀ ⟶ P` to a scheme `P` of
finite type over `k₀`, the base change `Y = P ×_{k₀} k` carries the model Frobenius `Φ_Y` of `P`,
and `f₀'` base-changes to a morphism `f : X ⟶ Y` with `Φ ≫ f = f ≫ Φ_Y`, the base change of `f₀'`
along the projections. -/
theorem IsModelFrobenius.exists_comp_eq_comp (hΦ : IsModelFrobenius Φ f₀ p)
    (P : Over (Spec (.of k₀))) [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [IsSeparated P.hom] (f₀' : X₀ ⟶ P.left) (hcomp : f₀' ≫ P.hom = f₀) :
    ∃ (Y : Over (Spec (.of k))) (_ : LocallyOfFiniteType Y.hom) (_ : QuasiCompact Y.hom)
      (_ : IsSeparated Y.hom) (pY : Y.left ⟶ P.left) (ΦY : Y ⟶ Y) (f : X ⟶ Y),
      IsModelFrobenius ΦY P.hom pY ∧ Φ ≫ f = f ≫ ΦY ∧ f.left ≫ pY = p ≫ f₀' ∧
        IsPullback f.left p pY f₀' := by
  obtain ⟨Y, _, _, _, pY, ΦY, hY⟩ : ∃ (Y : Over (Spec (.of k))) (_ : LocallyOfFiniteType Y.hom)
      (_ : QuasiCompact Y.hom) (_ : IsSeparated Y.hom) (pY : Y.left ⟶ P.left) (ΦY : Y ⟶ Y),
      IsModelFrobenius ΦY P.hom pY :=
    ⟨_, inferInstanceAs (LocallyOfFiniteType (pullback.snd P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))))),
      inferInstanceAs (QuasiCompact (pullback.snd P.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))))),
      inferInstanceAs (IsSeparated (pullback.snd P.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))))), _, _,
      isModelFrobenius_modelFrobenius_one P⟩
  have hw : (p ≫ f₀') ≫ P.hom = X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) := by
    rw [Category.assoc, hcomp]
    exact hΦ.isPullback.w
  let f : X ⟶ Y := Over.homMk (hY.isPullback.lift _ _ hw) (hY.isPullback.lift_snd _ _ hw)
  have hfp : f.left ≫ pY = p ≫ f₀' := hY.isPullback.lift_fst _ _ hw
  refine ⟨Y, inferInstance, inferInstance, inferInstance, pY, ΦY, f, hY, ?_, hfp,
    hΦ.isPullback_left hY hfp hcomp⟩
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  obtain ⟨FY, hFY, hpY⟩ := hY.exists_isFrobenius
  ext1
  refine hY.isPullback.hom_ext ?_ ?_
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hfp, hpY,
      reassoc_of% hfp, reassoc_of% hp, hF₀.comp_eq_comp f₀ hFY f₀']
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, Over.w f, Over.w ΦY,
      Over.w f, Over.w Φ]

variable {Y : Over (Spec (.of k))}

/-- The fibres of a morphism `f : X ⟶ Y` over `k` whose underlying morphism is an immersion are
empty or a point: the structure morphism of the fibre at a rational point is a closed immersion
into `Spec k`. -/
lemma isClosedImmersion_pullback_hom_of_isImmersion (f : X ⟶ Y) [IsImmersion f.left]
    (y : RationalPoint Y) : IsClosedImmersion (pullback f y).hom := by
  have : IsImmersion (pullback f y).hom :=
    MorphismProperty.of_isPullback (isPullback_pullbackFst_left f y) ‹_›
  exact isClosedImmersion_of_isImmersion_spec_field _

/-- The fibres of a smooth morphism of relative dimension one over the rational points are smooth
of relative dimension one. -/
lemma smoothOfRelativeDimension_pullback_hom (f : X ⟶ Y)
    [SmoothOfRelativeDimension 1 f.left] (y : RationalPoint Y) :
    SmoothOfRelativeDimension 1 (pullback f y).hom :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
    (isPullback_pullbackFst_left f y) ‹_›

/-- The fibres of a proper morphism over the rational points are proper. -/
lemma isProper_pullback_hom (f : X ⟶ Y) [IsProper f.left] (y : RationalPoint Y) :
    IsProper (pullback f y).hom :=
  MorphismProperty.of_isPullback (isPullback_pullbackFst_left f y) ‹_›

end AlgebraicGeometry.ProEtale.CondensedRing
