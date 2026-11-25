/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.ClosedRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.Projective
public import WeilConjectures.AlgebraicGeometry.ProjectiveMorphism

/-!
# Base change along open immersions: the minimal counterexample

This file contains the "minimal counterexample" step of the proof of blueprint
`corollary-open-direct-image-over-field--2`: if, for all data with `dim X + dim Y ≤ N`, the base
change maps are isomorphisms on the geometric stalks at non-closed points, then they are
isomorphisms. To check the stalk at a closed point `z`, restrict to affine open neighbourhoods `X₀`
and `Y₀` of the images of `z` (étale base change), compactify `Y₀` into a projective `K`-scheme of
the same dimension (blueprint `corollary-open-direct-image-over-field--2`), and apply the projective
case.

In the formalisation, the restriction to the affine open neighbourhoods is done by étale
locality of the base change map
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_etale_cover`),
applied to the open cover of `X ×_K Y` by the products `X₀ ×_K Y₀` of affine opens; on each
of them the base change map is the restriction of the base change map over `X₀ ×_K Ȳ`, which
is an isomorphism by the projective case.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The minimal counterexample step of blueprint `corollary-open-direct-image-over-field--2` for an
affine second factor: if the base change maps are isomorphisms on the geometric stalks at non-closed
points for all data with `dim X + dim Y ≤ N`, then `corollary-open-direct-image-over-field--2` holds
for data with `dim X + dim Y ≤ N` and `Y` affine. Compactify `Y` into a projective `K`-scheme `Ȳ` of
the same dimension (blueprint `corollary-open-direct-image-over-field--2`), apply the projective
case to `X ×_K Ȳ`, and restrict to the open subscheme `X ×_K Y`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_atNonClosed_of_isAffine {N : WithBot ℕ∞}
    (H : Etale.OpenImmersionBaseChangeAtNonClosed Λ N) {K : Type u} [Field K]
    {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [IsAffine Y]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0) (hdim : topologicalKrullDim X + topologicalKrullDim Y ≤ N) (i : ℤ)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq i F) := by
  obtain ⟨Y', aY', jY, _, _, hcomm, -, hdimY'⟩ :=
    exists_isHProjective_compactification_of_isAffine aY
  have := isProper_of_isHProjective aY'
  have hW' := IsPullback.of_hasPullback aX aY'
  let α : W ⟶ pullback aX aY' :=
    pullback.lift q₁ (q₂ ≫ jY) (by rw [Category.assoc, hcomm]; exact hW.w)
  have sqα : IsPullback α q₂ (pullback.snd aX aY') jY :=
    IsPullback.of_right (by rw [pullback.lift_fst, hcomm]; exact hW) (pullback.lift_snd _ _ _)
      hW'
  have : IsOpenImmersion α := MorphismProperty.of_isPullback sqα.flip inferInstance
  have sq₂ := IsPullback.of_hasPullback j (pullback.fst aX aY')
  have hF₂ := Etale.isIso_baseChangeHomologyMap_of_isProper_of_forall_not_isClosed Λ aX aY' j
    (pullback.fst aX aY') (pullback.snd aX aY') hW' _ _ sq₂ n hn hΛ F
    (fun z hz i ↦ H aX aY' j _ _ hW' _ _ sq₂ n hn hΛ (by rwa [hdimY']) z hz i F) i
  have sq₁ : IsPullback
      (sq₂.lift e (h ≫ α) (by rw [Category.assoc, pullback.lift_fst]; exact sq.w))
      h (pullback.snd j (pullback.fst aX aY')) α :=
    IsPullback.of_right (by rw [sq₂.lift_fst, pullback.lift_fst]; exact sq) (sq₂.lift_snd _ _ _)
      sq₂
  exact Etale.isIso_baseChangeHomologyMap_of_etale_restriction Λ sq₂ sq₁ sq (sq₂.lift_fst _ _ _)
    (pullback.lift_fst _ _ _) i F hF₂

/-- Proof of blueprint `corollary-open-direct-image-over-field--2`, the minimal counterexample: if
for all data with `dim X + dim Y ≤ N` the base change maps are isomorphisms on the geometric stalks
at the non-closed points of `X ×_K Y`, then `corollary-open-direct-image-over-field--2` holds for
all data with `dim X + dim Y ≤ N`. -/
theorem Etale.openImmersionBaseChangeAtMost_of_atNonClosed {N : WithBot ℕ∞}
    (H : Etale.OpenImmersionBaseChangeAtNonClosed Λ N) :
    Etale.OpenImmersionBaseChangeAtMost Λ N := by
  intro K _ X U Y W V aX aY _ _ _ _ j _ q₁ q₂ hW e h sq n hn hΛ hdim i F
  let ιX (z : W) : X.affineCover.X (X.affineCover.idx (q₁ z)) ⟶ X := X.affineCover.f _
  let ιY (z : W) : Y.affineCover.X (Y.affineCover.idx (q₂ z)) ⟶ Y := Y.affineCover.f _
  let s (z : W) : pullback q₁ (ιX z) ⟶ Y := pullback.fst q₁ (ιX z) ≫ q₂
  let a (z : W) : pullback (s z) (ιY z) ⟶ W := pullback.fst _ _ ≫ pullback.fst _ _
  let f (z : W) : pullback (s z) (ιY z) ⟶ _ := pullback.fst _ _ ≫ pullback.snd q₁ (ιX z)
  have (z : W) : Etale (a z) := by
    dsimp [a]
    infer_instance
  refine Etale.isIso_baseChangeHomologyMap_of_etale_cover Λ a ?_ f ιX ?_
    (fun z ↦ pullback.fst j (ιX z)) (fun z ↦ pullback.snd j (ιX z))
    (fun z ↦ IsPullback.of_hasPullback _ _) (fun z ↦ pullback.fst (pullback.snd j (ιX z)) (f z))
    (fun z ↦ pullback.snd _ (f z)) (fun z ↦ IsPullback.of_hasPullback _ _) sq i F fun z ↦ ?_
  · intro w
    obtain ⟨x₀, hx₀⟩ := X.affineCover.covers (q₁ w)
    obtain ⟨p₁, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q₁) (g := ιX w) w x₀
      hx₀.symm
    obtain ⟨y₀, hy₀⟩ := Y.affineCover.covers (q₂ w)
    obtain ⟨p₂, hp₂, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s w) (g := ιY w) p₁ y₀
      (by simp [s, hp₁, ιY, hy₀])
    exact ⟨w, p₂, by simp [a, hp₂, hp₁]⟩
  · intro z
    simp only [f, a, Category.assoc, pullback.condition]
  · have hW₀ : IsPullback (f z) (pullback.snd (s z) (ιY z)) (ιX z ≫ aX) (ιY z ≫ aY) :=
      (IsPullback.of_hasPullback (s z) (ιY z)).paste_horiz
        ((IsPullback.of_hasPullback q₁ (ιX z)).paste_horiz hW.flip).flip
    have : QuasiCompact (ιX z ≫ aX) :=
      (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
    exact Etale.isIso_baseChangeHomologyMap_of_atNonClosed_of_isAffine H (ιX z ≫ aX)
      (ιY z ≫ aY) (pullback.snd j (ιX z)) (f z) _ hW₀ _ _ (IsPullback.of_hasPullback _ _) n hn
      hΛ ((add_le_add (ιX z).isOpenEmbedding.isInducing.topologicalKrullDim_le
        (ιY z).isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hdim) i _

end AlgebraicGeometry
