/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
public import WeilConjectures.TraceFormula.BaseChange.Basic
public import WeilConjectures.TraceFormula.FibreModel

/-!

# Affine models embed into proper models

Let `Φ` be the model Frobenius of an affine model `X₀` of `X = X₀ ×_{k₀} k`, of finite type over
the finite field `k₀`. An immersion `X₀ ⟶ ℙ^N_{k₀}` over `k₀`
(`AlgebraicGeometry.exists_isImmersion_projectiveSpace`) base changes to a morphism `f : X ⟶ Y`
to the proper scheme `Y = ℙ^N_k` with its model Frobenius, commuting with the model Frobenii,
whose fibres over the rational points of `Y` are empty or a point, hence proper (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Steps 2–4, where the compactification of the
affine line plays this role).

## Main results

- `ProEtale.CondensedRing.IsModelFrobenius.exists_isProper_pullback`: an affine model embeds
  into a proper model, with proper fibres.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- An immersion into the spectrum of a field is a closed immersion: its range is closed, since
the spectrum of a field is a point. -/
lemma isClosedImmersion_of_isImmersion_spec_field {K : Type u} [Field K] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of K)) [IsImmersion f] : IsClosedImmersion f :=
  have : Unique (Spec (.of K)) := inferInstanceAs (Unique (PrimeSpectrum K))
  .of_isPreimmersion f (isClosed_discrete _)

namespace ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {Φ : X ⟶ X}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- **An affine model embeds into a proper model** (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Steps 2–4): for the model Frobenius `Φ` of an
affine model `X₀` of finite type over `k₀`, there are a proper `Y` over `k` with the model
Frobenius `Φ_Y` of a model `Y₀` of finite type over `k₀` and a morphism `f : X ⟶ Y`, the base
change of a `k₀`-morphism `f₀ : X₀ ⟶ Y₀`, with `Φ ≫ f = f ≫ Φ_Y`, whose fibres over the rational
points of `Y` are proper over `k`. -/
theorem IsModelFrobenius.exists_isProper_pullback [IsAlgClosed k] [LocallyOfFiniteType f₀]
    [IsAffine X₀] (hΦ : IsModelFrobenius Φ f₀ p) :
    ∃ (Y : Over (Spec (.of k))) (_ : LocallyOfFiniteType Y.hom) (_ : QuasiCompact Y.hom)
      (_ : IsSeparated Y.hom) (Y₀ : Scheme.{u}) (fY₀ : Y₀ ⟶ Spec (.of k₀)) (pY : Y.left ⟶ Y₀)
      (ΦY : Y ⟶ Y) (f : X ⟶ Y) (f₀' : X₀ ⟶ Y₀),
      IsProper Y.hom ∧ LocallyOfFiniteType fY₀ ∧ IsModelFrobenius ΦY fY₀ pY ∧
        Φ ≫ f = f ≫ ΦY ∧ f.left ≫ pY = p ≫ f₀' ∧ f₀' ≫ fY₀ = f₀ ∧
        ∀ y : RationalPoint Y, IsProper (pullback f y).hom := by
  obtain ⟨P, _, f₀', hf₀', hcomp⟩ : ∃ (P : Over (Spec (.of k₀))) (_ : IsProper P.hom)
      (f₀' : X₀ ⟶ P.left), IsImmersion f₀' ∧ f₀' ≫ P.hom = f₀ := by
    obtain ⟨N, _, f₀', hf₀', hcomp⟩ := exists_isImmersion_projectiveSpace f₀
    exact ⟨Over.mk (ℙ(N; Spec (.of k₀)) ↘ Spec (.of k₀)),
      inferInstanceAs (IsProper (ℙ(N; Spec (.of k₀)) ↘ Spec (.of k₀))), f₀', hf₀', hcomp⟩
  obtain ⟨Y, _, pY, ΦY, hY⟩ : ∃ (Y : Over (Spec (.of k))) (_ : IsProper Y.hom)
      (pY : Y.left ⟶ P.left) (ΦY : Y ⟶ Y), IsModelFrobenius ΦY P.hom pY :=
    ⟨_, inferInstanceAs (IsProper (pullback.snd P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))))), _, _,
      isModelFrobenius_modelFrobenius_one P⟩
  have hw : (p ≫ f₀') ≫ P.hom = X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) := by
    rw [Category.assoc, hcomp]
    exact hΦ.isPullback.w
  let f : X ⟶ Y := Over.homMk (hY.isPullback.lift _ _ hw) (hY.isPullback.lift_snd _ _ hw)
  have hfp : f.left ≫ pY = p ≫ f₀' := hY.isPullback.lift_fst _ _ hw
  refine ⟨Y, inferInstance, inferInstance, inferInstance, _, P.hom, pY, ΦY, f, f₀',
    inferInstance, inferInstance, hY, ?_, hfp, hcomp, fun y ↦ ?_⟩
  · obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
    obtain ⟨FY, hFY, hpY⟩ := hY.exists_isFrobenius
    ext1
    refine hY.isPullback.hom_ext ?_ ?_
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hfp, hpY,
        reassoc_of% hfp, reassoc_of% hp, hF₀.comp_eq_comp f₀ hFY f₀']
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, Over.w f, Over.w ΦY,
        Over.w f, Over.w Φ]
  · have hf := hΦ.isPullback_left hY hfp hcomp
    have : IsImmersion f.left := MorphismProperty.of_isPullback hf.flip hf₀'
    have hZ := (IsPullback.of_hasPullback f y).map (Over.forget _)
    simp only [Over.forget_map] at hZ
    have : IsImmersion (pullback.snd f y).left := MorphismProperty.of_isPullback hZ this
    have := isClosedImmersion_of_isImmersion_spec_field (pullback.snd f y).left
    rw [← Over.w (pullback.snd f y)]
    exact inferInstanceAs (IsProper ((pullback.snd f y).left ≫ 𝟙 _))

end ProEtale.CondensedRing

end AlgebraicGeometry
