/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The pushforward along a closed immersion is fully faithful, for any coefficients

Let `i : Z ⟶ X` be a closed immersion. The base change functor `i.Etale : X.Etale ⥤ Z.Etale`,
`V ↦ V ×_X Z`, along which the pushforward `i_*` of étale sheaves is defined, is

- *cover-dense*: every étale `Z`-scheme is covered by base changes of étale `X`-schemes, since
  étale morphisms lift locally along a closed immersion
  (`AlgebraicGeometry.Etale.exists_isPullback_of_isClosedImmersion`);
- *locally full*: a morphism `f : U ×_X Z ⟶ V ×_X Z` of étale `Z`-schemes is, locally on
  `U ×_X Z`, the base change of a morphism of étale `X`-schemes. Its graph is a section of the
  étale projection `(U ×_X V) ×_X Z ⟶ U ×_X Z`, hence an open immersion; its image is the trace
  of an open `W` of `U ×_X V`, and the second projection `W ⟶ V` lifts `f` on `W ×_X Z`, which
  maps isomorphically onto `U ×_X Z`;
- *locally faithful*: two morphisms of étale `X`-schemes which agree after base change to `Z`
  agree on an open containing the preimage of `Z`, the locus where two morphisms to an
  unramified `X`-scheme agree being open.

By `CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous` and
`CategoryTheory.Functor.IsCoverDense.faithful_sheafPushforwardContinuous` the pushforward `i_*`
is then fully faithful, for sheaves with values in an arbitrary category `A`. This refines
`AlgebraicGeometry.Etale.fullyFaithfulLowerStar`, which is proved by evaluating at geometric
points and needs `A` to be concrete.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isCoverDense_etale_of_isClosedImmersion`
- `AlgebraicGeometry.Scheme.Hom.isLocallyFull_etale_of_isClosedImmersion`
- `AlgebraicGeometry.Scheme.Hom.isLocallyFaithful_etale_of_isClosedImmersion`
- `AlgebraicGeometry.Etale.full_lowerStar_of_isClosedImmersion`,
  `AlgebraicGeometry.Etale.faithful_lowerStar_of_isClosedImmersion`: `i_*` is fully faithful.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Base change along a closed immersion `i : Z ⟶ X` is cover-dense for the small étale
topology of `Z`: every point of an étale `Z`-scheme `W` has an open neighbourhood which is the
base change `V ×_X Z` of an étale `X`-scheme `V`
(`AlgebraicGeometry.Etale.exists_isPullback_of_isClosedImmersion`). -/
instance Scheme.Hom.isCoverDense_etale_of_isClosedImmersion :
    i.Etale.IsCoverDense Z.smallEtaleTopology where
  is_cover W := by
    rw [Scheme.mem_smallEtaleTopology_iff]
    intro w
    obtain ⟨W₀, hw, V, q, hq, a, hpb⟩ := Etale.exists_isPullback_of_isClosedImmersion i W.hom w
    let g : i.Etale.obj (Scheme.Etale.mk q) ⟶ W :=
      MorphismProperty.Over.homMk (hpb.isoPullback.inv ≫ W₀.ι) (by
        rw [Category.assoc, Iso.inv_comp_eq]
        exact hpb.isoPullback_hom_snd.symm)
    refine ⟨_, g, Presieve.in_coverByImage _ _, hpb.isoPullback.hom ⟨w, hw⟩, ?_⟩
    change (hpb.isoPullback.hom ≫ hpb.isoPullback.inv ≫ W₀.ι) ⟨w, hw⟩ = w
    simp

/-- Base change along a closed immersion `i : Z ⟶ X` is locally full for the small étale
topology of `Z`. Given `f : U ×_X Z ⟶ V ×_X Z` over `Z`, its graph
`Γ : U ×_X Z ⟶ P ×_X Z`, for `P = U ×_X V`, is a section of the étale base change of the
projection `p : P ⟶ U`, hence an open immersion. Its range is the trace of an open `W` of `P`,
because `P ×_X Z ⟶ P` is a closed embedding. Then `W ⟶ P ⟶ V` lifts `W ×_X Z ⟶ U ×_X Z ⟶ V ×_X Z`,
and `W ×_X Z ⟶ U ×_X Z` is surjective, being split by `Γ`. -/
instance Scheme.Hom.isLocallyFull_etale_of_isClosedImmersion :
    i.Etale.IsLocallyFull Z.smallEtaleTopology where
  functorPushforward_imageSieve_mem {U V} f := by
    rw [Scheme.mem_smallEtaleTopology_iff]
    intro x
    -- the fibre product `P = U ×_X V`, an étale `X`-scheme, with its two projections
    let P : X.Etale := Scheme.Etale.mk (pullback.fst U.hom V.hom ≫ U.hom)
    let p : P ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom V.hom) rfl
    let q : P ⟶ V := MorphismProperty.Over.homMk (pullback.snd U.hom V.hom)
      pullback.condition.symm
    have hf : f.left ≫ pullback.snd V.hom i = pullback.snd U.hom i := f.w
    -- the graph `Γ : U ×_X Z ⟶ P ×_X Z` of `f`, a section of the base change of `p`
    let Γ : (i.Etale.obj U).left ⟶ (i.Etale.obj P).left :=
      pullback.lift (pullback.lift (pullback.fst U.hom i) (f.left ≫ pullback.fst V.hom i)
        (by
          rw [pullback.condition, Category.assoc, pullback.condition]
          exact ((reassoc_of% hf) i).symm))
        (pullback.snd U.hom i) (by
          change _ ≫ pullback.fst U.hom V.hom ≫ U.hom = _
          rw [pullback.lift_fst_assoc, pullback.condition])
    have hΓp : Γ ≫ (i.Etale.map p).left = 𝟙 _ := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_fst]
        simp [Γ, p]
      · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_snd]
        simp [Γ]
    have hΓq : Γ ≫ (i.Etale.map q).left = f.left := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_fst]
        simp [Γ, q]
      · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_snd]
        simp [Γ, hf]
    have : IsOpenImmersion Γ := by
      have : IsOpenImmersion (Γ ≫ (i.Etale.map p).left) := by rw [hΓp]; infer_instance
      exact FormallyUnramified.isOpenImmersion_of_comp (i.Etale.map p).left Γ
    -- the range of `Γ` is the trace on `P ×_X Z` of an open `S` of `P`
    obtain ⟨S, hS, hSΓ⟩ := (pullback.fst P.hom i).isClosedEmbedding.isInducing.isOpen_iff.1
      Γ.isOpenEmbedding.isOpen_range
    let S' : P.left.Opens := ⟨S, hS⟩
    let W : X.Etale := Scheme.Etale.mk (S'.ι ≫ P.hom)
    let ι : W ⟶ P := MorphismProperty.Over.homMk S'.ι rfl
    -- `ι ×_X Z` lands in the range of `Γ`
    have hrange : Set.range (i.Etale.map ι).left.base ⊆ Set.range Γ.base := by
      rintro _ ⟨y, rfl⟩
      rw [← hSΓ]
      change ((i.Etale.map ι).left ≫ pullback.fst P.hom i) y ∈ S
      rw [Scheme.Hom.etale_map_left_comp_fst]
      exact (Scheme.Opens.range_ι S').subset ⟨_, rfl⟩
    have hm := IsOpenImmersion.lift_fac Γ _ hrange
    refine ⟨i.Etale.obj W, i.Etale.map ι ≫ i.Etale.map p, ⟨W, ι ≫ p, 𝟙 _, ⟨ι ≫ q, ?_⟩, by simp⟩, ?_⟩
    · rw [Functor.map_comp, Functor.map_comp]
      refine MorphismProperty.Over.Hom.ext ?_
      change (i.Etale.map ι).left ≫ (i.Etale.map q).left =
        ((i.Etale.map ι).left ≫ (i.Etale.map p).left) ≫ f.left
      rw [← hm, Category.assoc, hΓq]
      simp only [Category.assoc]
      rw [reassoc_of% hΓp]
    · -- a section `σ` of `(ι ≫ p) ×_X Z` through which `Γ` factors
      have hr : Set.range (Γ ≫ pullback.fst P.hom i).base ⊆ Set.range S'.ι.base := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨z, rfl⟩
        change pullback.fst P.hom i (Γ z) ∈ S
        rw [← Set.mem_preimage, hSΓ]
        exact ⟨z, rfl⟩
      have hΓsnd : Γ ≫ pullback.snd P.hom i = pullback.snd U.hom i := pullback.lift_snd _ _ _
      let σ : (i.Etale.obj U).left ⟶ (i.Etale.obj W).left :=
        pullback.lift (IsOpenImmersion.lift S'.ι _ hr) (pullback.snd U.hom i) (by
          change _ ≫ S'.ι ≫ P.hom = _
          rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, pullback.condition,
            reassoc_of% hΓsnd])
      have hσ : σ ≫ (i.Etale.map ι).left = Γ := by
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_fst]
          change σ ≫ pullback.fst _ i ≫ S'.ι = _
          simp [σ]
        · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_snd]
          simp [σ, hΓsnd]
      refine ⟨σ x, ?_⟩
      change (σ ≫ (i.Etale.map ι).left ≫ (i.Etale.map p).left) x = x
      rw [reassoc_of% hσ, hΓp]
      rfl

/-- Base change along a closed immersion `i : Z ⟶ X` is locally faithful for the small étale
topology of `Z`. If `f₁ f₂ : W ⟶ W'` agree after base change to `Z`, they agree on the open
`E` of `W` where they coincide (`AlgebraicGeometry.FormallyUnramified.eqLocus`, open as `W'`
is unramified over `X`). The projection `W ×_X Z ⟶ W` factors through `E`, so the base change
of `E ⟶ W`, which lies in the equalizer sieve, has a section, and the image of the equalizer
sieve contains the identity of `W ×_X Z`. -/
instance Scheme.Hom.isLocallyFaithful_etale_of_isClosedImmersion :
    i.Etale.IsLocallyFaithful Z.smallEtaleTopology where
  functorPushforward_equalizer_mem {W W'} f₁ f₂ hf := by
    have hc : f₁.left ≫ W'.hom = f₂.left ≫ W'.hom := by simp
    -- the open `E` of `W` on which `f₁` and `f₂` agree
    let E := FormallyUnramified.eqLocus W'.hom f₁.left f₂.left hc
    let e : Scheme.Etale.mk (E.ι ≫ W.hom) ⟶ W := MorphismProperty.Over.homMk E.ι rfl
    have he : Sieve.equalizer f₁ f₂ e :=
      MorphismProperty.Over.Hom.ext (FormallyUnramified.eqLocus_ι_comp_eq W'.hom f₁.left f₂.left hc)
    -- the projection `W ×_X Z ⟶ W` lands in `E`
    have hfst : pullback.fst W.hom i ≫ f₁.left = pullback.fst W.hom i ≫ f₂.left := by
      rw [← Scheme.Hom.etale_map_left_comp_fst, ← Scheme.Hom.etale_map_left_comp_fst]
      change (i.Etale.map f₁).left ≫ _ = (i.Etale.map f₂).left ≫ _
      rw [hf]
    have hr := FormallyUnramified.range_subset_eqLocus W'.hom f₁.left f₂.left hc _ hfst
    rw [← E.range_ι] at hr
    let l := IsOpenImmersion.lift E.ι (pullback.fst W.hom i) hr
    -- hence the base change of `e` has a section `s`
    let s : i.Etale.obj W ⟶ i.Etale.obj (Scheme.Etale.mk (E.ι ≫ W.hom)) :=
      MorphismProperty.Over.homMk (pullback.lift l (pullback.snd W.hom i) (by
        change l ≫ E.ι ≫ W.hom = _
        rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.condition]))
        (pullback.lift_snd _ _ _)
    have hs : s ≫ i.Etale.map e = 𝟙 _ := by
      refine MorphismProperty.Over.Hom.ext (pullback.hom_ext ?_ ?_)
      · change (s.left ≫ (i.Etale.map e).left) ≫ _ = _
        rw [Category.assoc, Scheme.Hom.etale_map_left_comp_fst]
        change pullback.lift l _ _ ≫ pullback.fst _ i ≫ E.ι = 𝟙 _ ≫ _
        rw [pullback.lift_fst_assoc, IsOpenImmersion.lift_fac, Category.id_comp]
      · change (s.left ≫ (i.Etale.map e).left) ≫ _ = _
        rw [Category.assoc, Scheme.Hom.etale_map_left_comp_snd]
        change pullback.lift l _ _ ≫ pullback.snd _ i = 𝟙 _ ≫ _
        rw [pullback.lift_snd, Category.id_comp]
    convert (Z.smallEtaleTopology).top_mem (i.Etale.obj W)
    rw [Sieve.id_mem_iff_eq_top.symm]
    exact ⟨_, e, s, he, hs.symm⟩

namespace Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A]

/-- The pushforward along a closed immersion is full, for sheaves with values in any category:
base change along `i` is cover-dense and locally full. -/
instance full_lowerStar_of_isClosedImmersion : (i)_*[A].Full := by
  have : (MorphismProperty.Over.pullback @Etale ⊤ i).IsCoverDense
      (Z.smallGrothendieckTopology @Etale) := Scheme.Hom.isCoverDense_etale_of_isClosedImmersion i
  have : (MorphismProperty.Over.pullback @Etale ⊤ i).IsLocallyFull
      (Z.smallGrothendieckTopology @Etale) :=
    Scheme.Hom.isLocallyFull_etale_of_isClosedImmersion i
  exact inferInstanceAs ((MorphismProperty.Over.pullback @Etale ⊤ i).sheafPushforwardContinuous A
    (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).Full

/-- The pushforward along a closed immersion is faithful, for sheaves with values in any
category: base change along `i` is cover-dense and locally full. -/
instance faithful_lowerStar_of_isClosedImmersion : (i)_*[A].Faithful := by
  have : (MorphismProperty.Over.pullback @Etale ⊤ i).IsCoverDense
      (Z.smallGrothendieckTopology @Etale) := Scheme.Hom.isCoverDense_etale_of_isClosedImmersion i
  have : (MorphismProperty.Over.pullback @Etale ⊤ i).IsLocallyFull
      (Z.smallGrothendieckTopology @Etale) :=
    Scheme.Hom.isLocallyFull_etale_of_isClosedImmersion i
  exact inferInstanceAs ((MorphismProperty.Over.pullback @Etale ⊤ i).sheafPushforwardContinuous A
    (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).Faithful

end Etale

end AlgebraicGeometry
