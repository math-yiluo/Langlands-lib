/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.SepReduction
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.ProjSepClosed
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.ProjStalks
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Base change along open immersions: the projective case

This file contains the "projective case" of the proof of blueprint
`corollary-open-direct-image-over-field--2`: if `Y` is proper (e.g. projective) over `K` and the
base change map is an isomorphism on the geometric stalks at all non-closed points of `X ×_K Y`,
then it is an isomorphism. After the reduction to a separably closed ground field (blueprint
`corollary-open-direct-image-over-field--2`), the cone `Q` of the derived base change map is
supported on closed points, so it vanishes as soon as its cohomology does (blueprint
`corollary-open-direct-image-over-field--2`), and the base change map induces an isomorphism on
cohomology by the Künneth formula with one proper factor (blueprint
`lemma-kunneth-finite-direct-image--1`).

The hypothesis on the stalks at non-closed points passes to the base change to `K^sep`
(`AlgebraicGeometry.Etale.isIso_sheafFiber_baseChangeHomologyMap_cube_iff`), since the
integral morphism `(X ×_K Y)_{K^sep} ⟶ X ×_K Y` maps non-closed points to non-closed points
(`AlgebraicGeometry.Scheme.Hom.not_isClosed_singleton_apply_of_isIntegralHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

/-- An integral morphism maps non-closed points to non-closed points: a specialization of `x`
inside the fibre of a closed point `f x` is trivial
(`AlgebraicGeometry.Scheme.Hom.eq_of_specializes_of_apply_eq_of_isIntegralHom`). -/
lemma Scheme.Hom.not_isClosed_singleton_apply_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] {x : X} (hx : ¬ IsClosed ({x} : Set X)) : ¬ IsClosed ({f x} : Set Y) := by
  intro hc
  refine hx (closure_subset_iff_isClosed.1 fun w hw ↦ ?_)
  have hs : x ⤳ w := specializes_iff_mem_closure.2 hw
  have hfw : f w ∈ closure ({f x} : Set Y) :=
    specializes_iff_mem_closure.1 (hs.map f.continuous)
  rw [hc.closure_eq, Set.mem_singleton_iff] at hfw
  exact (f.eq_of_specializes_of_apply_eq_of_isIntegralHom hs hfw.symm).symm

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Proof of blueprint `corollary-open-direct-image-over-field--2`, the projective case: for `Y`
proper over `K`, if the base change map at `F` is an isomorphism on the geometric stalks at all
non-closed points of `W = X ×_K Y`, then it is an isomorphism. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isProper_of_forall_not_isClosed {K : Type u}
    [Field K] {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsProper aY]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ z : W, ¬ IsClosed ({z} : Set W) → ∀ i : ℤ,
      IsIso ((W.uliftPointSmallEtale z).sheafFiber.map (Etale.baseChangeHomologyMap Λ sq i F)))
    (i : ℤ) : IsIso (Etale.baseChangeHomologyMap Λ sq i F) := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hnK : (n : K) ≠ 0 := hn.ne_zero
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : QuasiCompact h := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq inferInstance
  have := Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero_of_ne_zero n hn₀ hΛ hnK F
  have := Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero_of_ne_zero n hn₀ hΛ hnK
    ((e)^*[ModuleCat.{u + 1} Λ].obj F)
  -- the base change of everything to `L = K^sep`
  let ι := Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))
  have hX := IsPullback.of_hasPullback aX ι
  have hU := IsPullback.of_hasPullback j (pullback.fst aX ι)
  have hW' := IsPullback.of_hasPullback q₁ (pullback.fst aX ι)
  have hV := IsPullback.of_hasPullback h (pullback.fst q₁ (pullback.fst aX ι))
  have hY := IsPullback.of_hasPullback aY ι
  set u := pullback.fst aX ι
  set aX' := pullback.snd aX ι
  set uU := pullback.fst j u
  set j' := pullback.snd j u
  set uW := pullback.fst q₁ u
  set q₁' := pullback.snd q₁ u
  set uV := pullback.fst h uW
  set h' := pullback.snd h uW
  set aY' := pullback.snd aY ι
  let e' : pullback h uW ⟶ pullback j u := pullback.lift (uV ≫ e) (h' ≫ q₁') (by
    rw [Category.assoc, sq.w, reassoc_of% hV.w, hW'.w, Category.assoc])
  have he : e' ≫ uU = uV ≫ e := pullback.lift_fst _ _ _
  have sq' : IsPullback e' h' j' q₁' := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hU
    rw [he, ← hW'.w]
    exact hV.paste_horiz sq
  let q₂' : pullback q₁ u ⟶ pullback aY ι := pullback.lift (uW ≫ q₂) (q₁' ≫ aX') (by
    rw [Category.assoc, ← hW.w, reassoc_of% hW'.w, hX.w, Category.assoc])
  have hWL : IsPullback q₁' q₂' aX' aY' := by
    refine (IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hY).flip
    rw [pullback.lift_fst, ← hX.w]
    exact hW'.paste_horiz hW.flip
  -- the hypothesis at the non-closed points of `W_L`
  have hT (q : ℤ) : IsIso (Etale.baseChangeHomologyMap Λ hU q F) :=
    Etale.isIso_baseChangeHomologyMap_of_fieldExtension Λ aX j u aX' hX hU q F
  have hX' (q : ℤ) : IsIso (Etale.baseChangeHomologyMap Λ hV q
      ((e)^*[ModuleCat.{u + 1} Λ].obj F)) :=
    Etale.isIso_baseChangeHomologyMap_of_fieldExtension Λ (q₁ ≫ aX) h uW (q₁' ≫ aX')
      (hW'.paste_vert hX) hV q _
  have : IsIntegralHom ι :=
    IsIntegralHom.SpecMap_iff.2 fun x ↦ Algebra.IsIntegral.isIntegral (R := K) x
  have : IsIntegralHom u := MorphismProperty.of_isPullback hX.flip inferInstance
  have : IsIntegralHom uW := MorphismProperty.of_isPullback hW'.flip inferInstance
  have hF' (z' : (pullback q₁ u : Scheme.{u}))
      (hz' : ¬ IsClosed ({z'} : Set (pullback q₁ u : Scheme.{u}))) (k : ℤ) :
      IsIso (((pullback q₁ u).uliftPointSmallEtale z').sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq' k ((uU)^*[ModuleCat.{u + 1} Λ].obj F))) := by
    refine (Etale.isIso_sheafFiber_baseChangeHomologyMap_cube_iff Λ sq hU sq' hV hW'.w.symm he F
      hT hX' ((pullback q₁ u).algClosurePoint z') k).2 ?_
    refine Etale.isIso_sheafFiber_map_of_apply_eq Λ _ (W.algClosurePoint (uW z')) _ ?_
      (hF _ (uW.not_isClosed_singleton_apply_of_isIntegralHom hz') k)
    simp
  have hnL : IsUnit (n : SeparableClosure K) := by
    simpa using hn.map (algebraMap K (SeparableClosure K))
  exact Etale.isIso_baseChangeHomologyMap_of_isIso_fieldExtension Λ aX j q₁ e h sq u aX' hX uU
    j' hU uW q₁' hW' uV e' h' hV sq' he n hn hΛ i F
    (Etale.isIso_baseChangeHomologyMap_of_isProper_of_isSepClosed Λ aX' aY' j' q₁' q₂' hWL e' h'
      sq' n hnL hΛ _ hF' i)

end AlgebraicGeometry
