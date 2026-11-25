/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition

/-!
# Base change for smooth duality from the étale and affine-line cases

Steps 2 and 3 of the proof of blueprint `proposition-exceptional-inverse-image-smooth-morphism--6`
(in the form of the proof of `proposition-exceptional-inverse-image-smooth-morphism`): the canonical
base change map `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) of a smooth morphism `f` is an
isomorphism *provided* it is one for

* étale morphisms (`AlgebraicGeometry.Etale.EtaleBaseChange`): the elementary case (c) of the
  blueprint, where `Re^! ≅ Le^*` with counit the sum over the geometric sheets of `e_!`;
* the affine-line projections `𝔸¹_S ⟶ S` over bases on which the exponent of `Λ` is
  invertible (`AlgebraicGeometry.Etale.AffineLineBaseChange`): the elementary case (a), from the
  explicit projective-line adjunction `proposition-adjunction-projective-line--1` and its
  compatibility with base change (`lemma-cycle-class-cartier-divisor`,
  `lemma-cohomology-projective-line-trace`).

The open-immersion case (b) is proved
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right`).

* *Composition* (Step 2): the base change maps of a composite are composed from those of the
  factors (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff`); so the
  affine-space projections, `𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S} ⟶ 𝔸^d_S ⟶ S`, and the charts
  `V --e--> 𝔸^d_U --p_d--> U ⊆ Y` of the étale-local normal form of a smooth morphism satisfy
  base change.
* *Descent* (Step 3): the restriction of `β_f` to the base change of an open `V ⊆ X` is, through
  `Rv'^! ≅ Lv'^*`, the base change map of `V ⟶ X ⟶ Y`, and isomorphisms descend along the
  covering of `X'` by these opens.

The composition law for the base change maps is only available for quasi-compact base changes,
so the reduction is made for a quasi-separated base `Y`, where the affine opens of `X` and `Y`
have quasi-compact inclusions.

## Main definitions

- `AlgebraicGeometry.Etale.EtaleBaseChange`
- `AlgebraicGeometry.Etale.AffineLineBaseChange`

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_comp`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_cover`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_affineSpace`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_etale_of_affineLine`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **Base change for a composite.** Let `h = f ≫ g` and let `sq` be a cartesian square of `h`
with quasi-compact base change. If the base change maps of `f` and of the quasi-compact `g` are
isomorphisms for all their cartesian squares with quasi-compact base change, then so is the base
change map of `sq`: it is composed from those of the base changes of `f` and `g`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_comp
    {X Y Z X' Z' : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (w : f ≫ g = h)
    {c : Z' ⟶ Z} {h' : X' ⟶ Z'} {a : X' ⟶ X} (sq : IsPullback a h' h c)
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification h'] [QuasiCompact h'] [QuasiCompact g]
    (hf : ∀ ⦃X'' Y'' : Scheme.{u}⦄ {b : Y'' ⟶ Y} {f'' : X'' ⟶ Y''} {a'' : X'' ⟶ X}
      (sq : IsPullback a'' f'' f b) [HasCompactification f''] [QuasiCompact f''],
      IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq))
    (hg : ∀ ⦃Y'' Z'' : Scheme.{u}⦄ {c'' : Z'' ⟶ Z} {g'' : Y'' ⟶ Z''} {b'' : Y'' ⟶ Y}
      (sq : IsPullback b'' g'' g c'') [HasCompactification g''] [QuasiCompact g''],
      IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq)) :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  subst w
  have sqg := IsPullback.of_hasPullback g c
  have sqf := IsPullback.of_bot' sq sqg
  have w' := sqg.lift_snd (a ≫ f) h' (by rw [Category.assoc, sq.w])
  have : HasCompactification (pullback.snd g c) := .of_isPullback sqg
  have : HasCompactification (sqg.lift (a ≫ f) h' (by rw [Category.assoc, sq.w])) :=
    .of_isPullback sqf
  have : QuasiCompact (sqg.lift (a ≫ f) h' (by rw [Category.assoc, sq.w])) := by
    have : QuasiCompact (sqg.lift (a ≫ f) h' (by rw [Category.assoc, sq.w]) ≫
        pullback.snd g c) := by
      rw [w']
      infer_instance
    exact .of_comp _ (pullback.snd g c)
  have := hf sqf
  have := hg sqg
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  exact (isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff sqf sqg sq rfl w' K
    inferInstance).2 inferInstance

/-- **Base change descends along open covers.** Let `sq` be a cartesian square of `f` with
quasi-compact base change `f'`, and let `v_i : V_i ⟶ X` be quasi-compact open immersions whose
base changes `v'_i : V'_i ⟶ X'` cover `X'`. If the base change maps of the composites
`v_i ≫ f` are isomorphisms at `K`, then so is that of `f`: by the composition law and the
open-immersion case, `Rv'_i^!` of it is invertible, and `Rv'_i^! ≅ Lv'_i^*`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app_of_cover {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    {ι : Type u} {V V' : ι → Scheme.{u}} (v : ∀ i, V i ⟶ X) (v' : ∀ i, V' i ⟶ X')
    (a : ∀ i, V' i ⟶ V i) [∀ i, IsOpenImmersion (v i)] [∀ i, QuasiCompact (v i)]
    (sqv : ∀ i, IsPullback (a i) (v' i) (v i) g') (hv : ∀ x : X', ∃ (i : ι) (y : V' i),
      (v' i).base y = x)
    [∀ i, QuasiCompact (v' i)] [∀ i, HasCompactification (v i ≫ f)]
    [∀ i, HasCompactification (v' i ≫ f')]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : ∀ i, IsIso ((rightDerivedUpperShriekBaseChangeMap Λ ((sqv i).paste_vert sq)).app K)) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app K) := by
  have (i : ι) : IsOpenImmersion (v' i) := MorphismProperty.of_isPullback (sqv i) inferInstance
  have (i : ι) : HasCompactification (v i) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have (i : ι) : HasCompactification (v' i) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ v' hv _ fun i ↦ ?_
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ (sqv i)
  have h₂ := (isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff (sqv i) sq
    ((sqv i).paste_vert sq) rfl rfl K inferInstance).1 (h i)
  rw [NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ (v' i)),
    ← NatIso.isIso_map_iff (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ (v' i))]
  exact h₂

variable (Λ) in
/-- *Base change for étale morphisms*: for every quasi-compact étale morphism `e : V ⟶ W`
admitting a compactification and every cartesian square `g' ≫ e = e' ≫ g` with quasi-compact
`e'` admitting a compactification, the canonical base change map `Lg'^* Re^! ⟶ Re'^! Lg^*` is an
isomorphism. This is the elementary case (c) of the blueprint proof of
`proposition-exceptional-inverse-image-smooth-morphism`: `Re^! ≅ Le^*`, with counit the sum over the
geometric sheets of the extension by zero `e_!`, and both commute with base change. -/
def EtaleBaseChange : Prop :=
  ∀ ⦃V W V' W' : Scheme.{u}⦄ (e : V ⟶ W) [_root_.AlgebraicGeometry.Etale e] [QuasiCompact e]
    [HasCompactification e] {g : W' ⟶ W} {e' : V' ⟶ W'} {g' : V' ⟶ V}
    (sq : IsPullback g' e' e g) [HasCompactification e'] [QuasiCompact e'],
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq)

variable (Λ) in
/-- *Base change for affine-line projections*: for every scheme `S` on which the
exponent of `Λ` is invertible and every cartesian square of the projection `p : 𝔸¹_S ⟶ S` with
quasi-compact base change admitting a compactification, the canonical base change map
`Lg'^* Rp^! ⟶ Rp'^! Lg^*` is an isomorphism. This is the elementary case (a) of the blueprint
proof of `proposition-exceptional-inverse-image-smooth-morphism--6`: the unit and counit of the
affine-line adjunction `Rp_! ⊣ p^*(1)[2]` (from `proposition-adjunction-projective-line--1`) commute
with base change. -/
def AffineLineBaseChange : Prop :=
  ∀ ⦃S : Scheme.{u}⦄ [HasInvertibleExponent Λ S] ⦃S' P' : Scheme.{u}⦄
    {g : S' ⟶ S} {p' : P' ⟶ S'} {g' : P' ⟶ 𝔸(ULift.{u} (Fin 1); S)}
    (sq : IsPullback g' p' (𝔸(ULift.{u} (Fin 1); S) ↘ S) g) [HasCompactification p']
    [QuasiCompact p'], IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq)

/-- **Base change for affine-space projections from the affine line** (blueprint
`proposition-exceptional-inverse-image-smooth-morphism--6`, "for affine space by composing those
adjunctions"): if the affine-line projections satisfy base change, then so do the projections
`p_d : 𝔸^d_S ⟶ S` over bases on which the exponent of `Λ` is invertible. For `d = 0` the
projection is an isomorphism; for `d + 1` it is, through `𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`, the composite
of the affine-line projection over `𝔸^d_S` and of `p_d`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_affineSpace (h₁ : AffineLineBaseChange Λ)
    (d : ℕ) (S : Scheme.{u}) [HasInvertibleExponent Λ S] ⦃S' P' : Scheme.{u}⦄
    {g : S' ⟶ S} {p' : P' ⟶ S'} {g' : P' ⟶ 𝔸(ULift.{u} (Fin d); S)}
    (sq : IsPullback g' p' (𝔸(ULift.{u} (Fin d); S) ↘ S) g) [HasCompactification p']
    [QuasiCompact p'] : IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  induction d generalizing S' P' with
  | zero => exact isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ sq
  | succ d ih =>
    set φ : 𝔸(ULift.{u} (Fin (d + 1)); S) ≅ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) :=
      AffineSpace.reindexIso S ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
        (finSumFinEquiv.trans Equiv.ulift.symm)) ≪≫ AffineSpace.sumIso S
    set q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) ↘ 𝔸(ULift.{u} (Fin d); S)
    set p := 𝔸(ULift.{u} (Fin d); S) ↘ S
    have : HasCompactification (φ.hom ≫ q) := HasCompactification.comp_of_isOpenImmersion q φ.hom
    have h : (φ.hom ≫ q) ≫ p = 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S := by
      rw [Category.assoc, Iso.trans_hom, Category.assoc, AffineSpace.sumIso_hom_over_over,
        AffineSpace.reindexIso_hom, AffineSpace.reindex_over]
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin d); S) := .of_hom p
    refine isIso_rightDerivedUpperShriekBaseChangeMap_of_comp (φ.hom ≫ q) p h sq
      (fun _ _ _ _ _ sq' _ _ ↦ ?_) (fun _ _ _ _ _ sq' _ _ ↦ ih sq')
    exact isIso_rightDerivedUpperShriekBaseChangeMap_of_comp φ.hom q rfl sq'
      (fun _ _ _ _ _ sq'' _ _ ↦
        isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ sq'')
      (fun _ _ _ _ _ sq'' _ _ ↦ h₁ sq'')
section Chart

variable (hE : EtaleBaseChange Λ) (h₁ : AffineLineBaseChange Λ)
include hE h₁

/-- Base change on a chart of the étale-local normal form: if `f` restricted to an affine open
`V` of `X` is the composite `V --e--> 𝔸^d_U --p_d--> U ⊆ Y` of an étale morphism, an affine-space
projection over an affine open `U` of the quasi-separated `Y` on which the exponent of `Λ` is
invertible, and an open immersion, then `V ⟶ Y` satisfies base change. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_chart {X Y : Scheme.{u}}
    [QuasiSeparatedSpace Y] (f : X ⟶ Y) (d : ℕ) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (e : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); U.toScheme)) [_root_.AlgebraicGeometry.Etale e]
    (hfe : e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) = f.resLE U V hVU)
    [HasInvertibleExponent Λ U.toScheme] [HasCompactification (V.ι ≫ f)] ⦃X' Y' : Scheme.{u}⦄
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ V.toScheme} (sq : IsPullback g' f' (V.ι ≫ f) g)
    [HasCompactification f'] [QuasiCompact f'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : QuasiCompact e := quasiCompact_of_compactSpace e
  have : QuasiCompact U.ι := quasiCompact_of_compactSpace U.ι
  have : HasCompactification e := HasCompactification.of_isQuasiAffine e
  have : HasCompactification (e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme)) :=
    HasCompactification.of_isQuasiAffine _
  have : HasCompactification U.ι := (Compactification.ofIsOpenImmersion _).hasCompactification
  have w : (e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme)) ≫ U.ι = V.ι ≫ f := by
    rw [hfe, Scheme.Hom.resLE_comp_ι]
  refine isIso_rightDerivedUpperShriekBaseChangeMap_of_comp _ U.ι w sq
    (fun _ _ _ _ _ sq' _ _ ↦ ?_) (fun _ _ _ _ _ sq' _ _ ↦
      isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ sq')
  exact isIso_rightDerivedUpperShriekBaseChangeMap_of_comp e _ rfl sq'
    (fun _ _ _ _ _ sq'' _ _ ↦ hE e sq'')
    (fun _ _ _ _ _ sq'' _ _ ↦
      isIso_rightDerivedUpperShriekBaseChangeMap_affineSpace h₁ d U.toScheme sq'')

/-- Base change over a quasi-separated base on which the exponent of `Λ` is invertible: glue the
charts of the étale-local normal form (`AlgebraicGeometry.Etale.Smooth.exists_etale_to_affineSpace`)
along the covering of `X'` by the base changes of their sources
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_cover`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_hasInvertibleExponent {X Y : Scheme.{u}}
    [QuasiSeparatedSpace Y] [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] ⦃X' Y' : Scheme.{u}⦄ {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [HasCompactification f'] [QuasiCompact f'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  choose U V hU hV _ hxV hVU e he hfe using fun x : X ↦ Smooth.exists_etale_to_affineSpace f d x
  have (x : X) : IsAffine (V x).toScheme := hV x
  have (x : X) : QuasiCompact (V x).ι := quasiCompact_of_compactSpace _
  have (x : X) : HasCompactification ((V x).ι ≫ f) :=
    HasCompactification.comp_of_isOpenImmersion f _
  have (x : X) : HasCompactification (pullback.snd (V x).ι g' ≫ f') :=
    .of_isPullback ((IsPullback.of_hasPullback (V x).ι g').paste_vert sq)
  refine isIso_rightDerivedUpperShriekBaseChangeMap_app_of_cover sq (fun x ↦ (V x).ι)
    (fun x ↦ pullback.snd (V x).ι g') (fun x ↦ pullback.fst (V x).ι g')
    (fun x ↦ IsPullback.of_hasPullback _ _) (fun x' ↦ ?_) K (fun x ↦ ?_)
  · have hx' : x' ∈ Set.range (pullback.snd (V (g'.base x')).ι g') := by
      rw [IsOpenImmersion.range_pullbackSnd, Scheme.Opens.opensRange_ι]
      exact hxV (g'.base x')
    obtain ⟨y, hy⟩ := hx'
    exact ⟨_, y, hy⟩
  · have : HasInvertibleExponent Λ (U x).toScheme := .of_hom (U x).ι
    have := he x
    have := isIso_rightDerivedUpperShriekBaseChangeMap_chart hE h₁ f d (hU x) (hV x) (hVU x)
      (e x) (hfe x) ((IsPullback.of_hasPullback (V x).ι g').paste_vert sq)
    infer_instance

/-- **Base change for smooth morphisms from the étale and affine-line cases** (Steps 2 and 3 of
the proof of blueprint `proposition-exceptional-inverse-image-smooth-morphism--6`): if étale
morphisms and the affine-line projections satisfy base change
(`AlgebraicGeometry.Etale.EtaleBaseChange`, `AlgebraicGeometry.Etale.AffineLineBaseChange`), then
for every smooth `f : X ⟶ Y` of relative dimension `d` admitting a compactification, over a
quasi-separated `Y`, with the exponent of `Λ` invertible on `X`, and every cartesian square
`g' ≫ f = f' ≫ g` with quasi-compact `f'` admitting a compactification, the canonical base change
map `Lg'^* Rf^! ⟶ Rf'^! Lg^*` is an isomorphism.

The morphism `f` factors through the open subscheme `Y_n` of `Y` on which the exponent `n` of `Λ`
is a unit, `f = f₀ ≫ ι`, as `n` is a unit on `X`; the base change maps of `f₀` are isomorphisms
by `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_hasInvertibleExponent`,
those of the quasi-compact open immersion `ι` by the open-immersion case, and they compose. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_etale_of_affineLine {X Y : Scheme.{u}}
    [QuasiSeparatedSpace Y] [HasInvertibleExponent Λ X] (f : X ⟶ Y) [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] ⦃X' Y' : Scheme.{u}⦄ {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [HasCompactification f'] [QuasiCompact f'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  obtain ⟨n, hn, hnΛ, hnX⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := X)
  let Y₀ : Y.Opens := Y.basicOpen (n : Γ(Y, ⊤))
  have : HasInvertibleExponent Λ Y₀.toScheme := by
    refine ⟨n, hn, hnΛ, ?_⟩
    have h := RingedSpace.isUnit_res_basicOpen Y.toRingedSpace (n : Γ(Y, ⊤))
    have hle : Y₀.ι ''ᵁ ⊤ ≤ Y.basicOpen (n : Γ(Y, ⊤)) := by simp [Y₀]
    rw [← map_natCast Y₀.ι.appTop.hom, Scheme.Opens.ι_appTop]
    have h' := h.map (Y.presheaf.map (homOfLE hle).op).hom
    erw [← CommRingCat.comp_apply, ← Functor.map_comp] at h'
    exact h'
  have hf : Set.range f.base ⊆ Set.range Y₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change x ∈ f ⁻¹ᵁ Y.basicOpen (n : Γ(Y, ⊤))
    rw [Scheme.preimage_basicOpen, map_natCast, X.basicOpen_of_isUnit hnX]
    trivial
  have sq₀ := IsOpenImmersion.isPullback_lift_id f Y₀.ι hf
  have w : IsOpenImmersion.lift Y₀.ι f hf ≫ Y₀.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : HasCompactification (IsOpenImmersion.lift Y₀.ι f hf) := .of_isPullback sq₀.flip
  have : SmoothOfRelativeDimension d (IsOpenImmersion.lift Y₀.ι f hf) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback sq₀.flip
      ‹SmoothOfRelativeDimension d f›
  have : HasCompactification Y₀.ι := (Compactification.ofIsOpenImmersion _).hasCompactification
  have : QuasiSeparatedSpace Y₀.toScheme := quasiSeparatedSpace_of_quasiSeparated Y₀.ι
  exact isIso_rightDerivedUpperShriekBaseChangeMap_of_comp _ Y₀.ι w sq
    (fun _ _ _ _ _ sq' _ _ ↦
      isIso_rightDerivedUpperShriekBaseChangeMap_of_hasInvertibleExponent hE h₁ _ d sq')
    (fun _ _ _ _ _ sq' _ _ ↦
      isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ sq')

end Chart

end Etale

end AlgebraicGeometry
