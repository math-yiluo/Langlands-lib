/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality
public import WeilConjectures.SixFunctors.BaseChange.UniversalHomeomorphism
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The base-change property and universal homeomorphisms

Étale cohomology is insensitive to universal homeomorphisms. For the base-change property
`BC(p, Λ, q)` of `AlgebraicGeometry.Etale.BaseChangeProperty` this gives:

* a universal homeomorphism satisfies `BC` in every degree
  (`AlgebraicGeometry.Etale.baseChangeProperty_of_isUniversalHomeomorphism`);
* `BC(u ≫ p)` implies `BC(p)` for a universal homeomorphism `u`
  (`AlgebraicGeometry.Etale.BaseChangeProperty.of_comp_isUniversalHomeomorphism`);
* `BC(p')` implies `BC(p)` for the base change `p'` of `p` along a universal homeomorphism
  (`AlgebraicGeometry.Etale.BaseChangeProperty.of_isPullback_of_isUniversalHomeomorphism`),

together with the corresponding statements for the universal base-change property. These are
the reductions "replace `K` by its perfect closure and `X` by its reduction" of the proof of
blueprint `lemma-kunneth-field-coefficients--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X S : Scheme.{u}}

/-- A universal homeomorphism `p` satisfies the base-change property `BC(p, Λ, q)` in every
degree: the derived base-change map along a universal homeomorphism is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism`). -/
theorem Etale.baseChangeProperty_of_isUniversalHomeomorphism (p : X ⟶ S)
    [IsUniversalHomeomorphism p] (q : ℤ) : Etale.BaseChangeProperty Λ p q := by
  intro T Y g e h _ _ sq F
  rw [Etale.isIso_baseChangeHomologyMap_iff, Etale.baseChange_eq_derivedBaseChangeMapPlus]
  have := Etale.isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism
    (ModuleCat.{u + 1} Λ) sq
  infer_instance

variable {Λ}

/-- If `u` is a universal homeomorphism and `BC(u ≫ p, Λ, q)` holds, then `BC(p, Λ, q)` holds.

The base-change map of a square on `u ≫ p` is the pullback along `u` of the base-change map of
the square on `p`, followed by the base-change map of a square on `u`, which is an isomorphism;
and the pullback along a universal homeomorphism is an equivalence, so it reflects
isomorphisms. -/
theorem Etale.BaseChangeProperty.of_comp_isUniversalHomeomorphism {X' : Scheme.{u}} {p : X ⟶ S}
    (u : X' ⟶ X) [IsUniversalHomeomorphism u] {q : ℤ}
    (H : Etale.BaseChangeProperty Λ (u ≫ p) q) : Etale.BaseChangeProperty Λ p q := by
  intro T Y g e h _ _ sq F
  have sq₁ : IsPullback (pullback.fst h u) (pullback.snd h u) h u := IsPullback.of_hasPullback h u
  have sq' : IsPullback (pullback.fst h u ≫ e) (pullback.snd h u) g (u ≫ p) :=
    sq₁.paste_horiz sq
  have htot := H g _ _ sq' F
  rw [Etale.isIso_baseChangeHomologyMap_iff] at htot ⊢
  rw [Etale.baseChange_app_paste_horiz Λ sq.toCommSq sq₁.toCommSq sq'.toCommSq] at htot
  simp only [Functor.map_comp] at htot
  have h₁ : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₁.toCommSq).app
        (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    have := Etale.isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism
      (ModuleCat.{u + 1} Λ) sq₁
    infer_instance
  rw [isIso_comp_left_iff, isIso_comp_right_iff] at htot
  have h₅ : IsIso (((u)^*[ModuleCat.{u + 1} Λ]).map
      ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) :=
    (NatIso.isIso_map_iff (((u)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
      q) _).2 htot
  have := Etale.isEquivalence_upperStar (ModuleCat.{u + 1} Λ) u
  exact isIso_of_reflects_iso _ ((u)^*[ModuleCat.{u + 1} Λ])

/-- If `p'` is the base change of `p` along a universal homeomorphism `v` and `BC(p', Λ, q)`
holds, then `BC(p, Λ, q)` holds: `p' ≫ v = u ≫ p` with `u` the base change of `v`, a universal
homeomorphism, and `BC(p' ≫ v)` holds by composition
(`AlgebraicGeometry.Etale.BaseChangeProperty.comp`). -/
theorem Etale.BaseChangeProperty.of_isPullback_of_isUniversalHomeomorphism {S' X' : Scheme.{u}}
    {p : X ⟶ S} {v : S' ⟶ S} {u : X' ⟶ X} {p' : X' ⟶ S'} (hpb : IsPullback u p' p v)
    [IsUniversalHomeomorphism v] {q : ℤ} (H : Etale.BaseChangeProperty Λ p' q) :
    Etale.BaseChangeProperty Λ p q := by
  have : IsUniversalHomeomorphism u :=
    MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism) hpb.flip inferInstance
  have H' : Etale.BaseChangeProperty Λ (u ≫ p) q := by
    rw [hpb.w]
    exact Etale.BaseChangeProperty.comp Λ H
      (Etale.baseChangeProperty_of_isUniversalHomeomorphism (Λ := Λ) v q)
  intro T Y g e h _ _ sq F
  exact Etale.BaseChangeProperty.of_comp_isUniversalHomeomorphism u H' g e h sq F

/-- The universal form of
`AlgebraicGeometry.Etale.BaseChangeProperty.of_comp_isUniversalHomeomorphism`: if `u` is a
universal homeomorphism and `BC(u ≫ p)` holds universally, so does `BC(p)`. A base change of
`u ≫ p` is the composite of a base change of `u`, again a universal homeomorphism, and the
corresponding base change of `p`. -/
theorem Etale.UniversalBaseChangeProperty.of_comp_isUniversalHomeomorphism {X' : Scheme.{u}}
    {p : X ⟶ S} (u : X' ⟶ X) [IsUniversalHomeomorphism u] {q : ℤ}
    (H : Etale.UniversalBaseChangeProperty Λ (u ≫ p) q) :
    Etale.UniversalBaseChangeProperty Λ p q := by
  intro S'' X'' t b'' p'' hpb'' T Y g e h _ _ sq F
  have h₁ : IsPullback (pullback.fst u b'') (pullback.snd u b'') u b'' :=
    IsPullback.of_hasPullback u b''
  have : IsUniversalHomeomorphism (pullback.snd u b'') :=
    MorphismProperty.of_isPullback h₁ inferInstance
  have h₂ : IsPullback (pullback.fst u b'') (pullback.snd u b'' ≫ p'') (u ≫ p) t := by
    simpa using h₁.paste_vert hpb''
  exact Etale.BaseChangeProperty.of_comp_isUniversalHomeomorphism
    (pullback.snd u b'') (H t _ _ h₂) g e h sq F

/-- The universal form of
`AlgebraicGeometry.Etale.BaseChangeProperty.of_isPullback_of_isUniversalHomeomorphism`: if `p'`
is the base change of `p` along a universal homeomorphism and `BC(p')` holds universally, so
does `BC(p)`. -/
theorem Etale.UniversalBaseChangeProperty.of_isPullback_of_isUniversalHomeomorphism
    {S' X' : Scheme.{u}} {p : X ⟶ S} {v : S' ⟶ S} {u : X' ⟶ X} {p' : X' ⟶ S'}
    (hpb : IsPullback u p' p v) [IsUniversalHomeomorphism v] {q : ℤ}
    (H : Etale.UniversalBaseChangeProperty Λ p' q) :
    Etale.UniversalBaseChangeProperty Λ p q := by
  intro S'' X'' t b'' p'' hpb'' T Y g e h _ _ sq F
  -- the base change of `t` along `v`
  have hS : IsPullback (pullback.fst t v) (pullback.snd t v) t v := IsPullback.of_hasPullback t v
  have : IsUniversalHomeomorphism (pullback.fst t v) :=
    MorphismProperty.of_isPullback hS.flip inferInstance
  -- the base change of `p'` along `pullback.snd t v`
  have h₁ : IsPullback (pullback.fst p' (pullback.snd t v)) (pullback.snd p' (pullback.snd t v))
      p' (pullback.snd t v) := IsPullback.of_hasPullback _ _
  have hBC : Etale.BaseChangeProperty Λ (pullback.snd p' (pullback.snd t v)) q :=
    H (pullback.snd t v) _ _ h₁
  have hw : (pullback.fst p' (pullback.snd t v) ≫ u) ≫ p =
      (pullback.snd p' (pullback.snd t v) ≫ pullback.fst t v) ≫ t := by
    rw [Category.assoc, hpb.w, ← Category.assoc, h₁.w, Category.assoc, Category.assoc, hS.w]
  let l : pullback p' (pullback.snd t v) ⟶ X'' :=
    hpb''.lift (pullback.fst p' (pullback.snd t v) ≫ u)
      (pullback.snd p' (pullback.snd t v) ≫ pullback.fst t v) hw
  have hl₁ : l ≫ b'' = pullback.fst p' (pullback.snd t v) ≫ u := hpb''.lift_fst _ _ _
  have hl₂ : l ≫ p'' = pullback.snd p' (pullback.snd t v) ≫ pullback.fst t v :=
    hpb''.lift_snd _ _ _
  have hbig : IsPullback (l ≫ b'') (pullback.snd p' (pullback.snd t v)) p
      (pullback.fst t v ≫ t) := by
    rw [hl₁, hS.w]
    exact h₁.paste_horiz hpb
  have hA : IsPullback l (pullback.snd p' (pullback.snd t v)) p'' (pullback.fst t v) :=
    IsPullback.of_right hbig hl₂ hpb''
  exact Etale.BaseChangeProperty.of_isPullback_of_isUniversalHomeomorphism hA hBC g e h sq F

end AlgebraicGeometry
