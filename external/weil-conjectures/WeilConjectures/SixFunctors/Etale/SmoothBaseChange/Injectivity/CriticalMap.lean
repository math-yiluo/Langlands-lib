/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.LongExactSequence

/-!
# Injectivity of the critical base-change map

Once the base-change property `BC(p, Λ, q - 1)` of
`AlgebraicGeometry.Etale.BaseChangeProperty` is known, the degree-`q` base-change map is
automatically injective: embedding the coefficient sheaf in an injective sheaf and comparing
the two long exact sequences, the degree-`(q - 1)` hypothesis makes two of the vertical arrows
isomorphisms and exhibits the source of the degree-`q` map as the image of the connecting map.

The same diagram gives two statements about the cokernel of the base-change map, which are
what verifies the closed–open splitting hypothesis of the minimal-counterexample lemma in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField`: the cokernel for a
subsheaf `F ⊆ G` is contained in the cokernel for `G`, and if `G` is injective the cokernel
for `F` is contained in `R^q h_* e⁻¹ G`.

Consequently a failure of `BC(p, Λ, q)` is witnessed by a nonzero element of the cokernel in
a geometric stalk.

## Main statements

- `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`: the degree-`q` base-change map is a
  monomorphism as soon as `BC(p, Λ, q - 1)` holds.
- `AlgebraicGeometry.Etale.mono_cokernelMap`: the cokernel of the base-change map for a
  subsheaf `F ⊆ G` is contained in the cokernel for `G`.
- `AlgebraicGeometry.Etale.mono_cokernelDesc`: for `G` injective, the cokernel of the
  base-change map for `F ⊆ G` is contained in `R^q h_* e⁻¹ G`.
- `AlgebraicGeometry.Etale.UniversalBaseChangeProperty.mono_baseChangeHomologyMap_and_cokernel`:
  the three statements for every base change of `p`, when `BC(p, Λ, q - 1)` holds universally.

## Implementation notes

The proof follows the blueprint: embed `F` in an injective sheaf `I`, compare the long exact
sequences of `0 ⟶ F ⟶ I ⟶ I / F ⟶ 0` through the base-change maps, and use that the source
of the degree-`q` map vanishes on `I` and that the degree-`(q - 1)` maps are isomorphisms. The
long exact sequences are the homology sequences of the images of the distinguished triangle
`F₁[0] ⟶ F₂[0] ⟶ F₃[0] ⟶ F₁[1]` under the triangulated functors `p^* ∘ Rg_*` and
`Rh_* ∘ e^*`; the base-change maps form a morphism between them because the derived
base-change morphism commutes with the shifts (`AlgebraicGeometry.Etale.commShift_baseChange`).

## References

- Stacks Project, Lemma 59.88.2, <https://stacks.math.columbia.edu/tag/0F03>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}
  {T Y : Scheme.{u}} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- Blueprint `lemma-injectivity-base-change-map-degree` (1): Injectivity of the critical map.

Let `q ≥ 1` and assume `BC(p, Λ, q - 1)`. Then for every Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `g` quasi-compact quasi-separated and every sheaf `F` of `Λ`-modules on `T_ét`, the
degree-`q` base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is injective. -/
@[stacks 0F03]
theorem Etale.mono_baseChangeHomologyMap (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono (Etale.baseChangeHomologyMap Λ sq q F) := by
  have hS : (ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  obtain ⟨δS, δT, wS₁, wS₂, wT₁, -, hS₁, hS₂, hT₁, -, hδ⟩ :=
    Etale.exists_connecting_baseChangeHomologyMap Λ sq hS (q - 1) q (by lia)
  have := hprev g e h sq (Injective.under F)
  have := hprev g e h sq (cokernel (Injective.ι F))
  have hI := Etale.isZero_baseChangeSourceFunctor_obj_of_injective Λ p g (q := q) (by lia)
    (Injective.under F)
  have : Epi δS := hS₂.epi_f (hI.eq_of_tgt _ _)
  exact Abelian.mono_of_epi_of_epi_of_mono
    (ComposableArrows.homMk₂ (Etale.baseChangeHomologyMap Λ sq (q - 1) (Injective.under F))
      (Etale.baseChangeHomologyMap Λ sq (q - 1) (cokernel (Injective.ι F)))
      (Etale.baseChangeHomologyMap Λ sq q F)
      (Etale.baseChangeHomologyMap_naturality Λ sq (q - 1) _).symm hδ :
      ComposableArrows.mk₂ _ δS ⟶ ComposableArrows.mk₂ _ δT)
    hS₁.exact_toComposableArrows hT₁.exact_toComposableArrows
    (inferInstanceAs (Epi δS)) (inferInstanceAs (Epi (Etale.baseChangeHomologyMap Λ sq _ _)))
    (inferInstanceAs (Mono (Etale.baseChangeHomologyMap Λ sq _ _)))

/-- Blueprint `lemma-injectivity-base-change-map-degree` (3): the cokernel of the critical map sits
inside the higher direct image of an injective sheaf.

In the situation of `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`, if `F` is a
subsheaf of an injective sheaf `G`, then the map `R^q h_* e⁻¹ F ⟶ R^q h_* e⁻¹ G` kills the
image of the base-change map for `F` — the source of the base-change map for `G` vanishes,
`G` being injective and `q` positive — and the induced map from the cokernel is injective.
The vanishing that makes the map out of the cokernel exist is
`AlgebraicGeometry.Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective`. -/
@[stacks 0F03]
theorem Etale.mono_cokernelDesc (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] [Injective G] :
    Mono (cokernel.desc (Etale.baseChangeHomologyMap Λ sq q F)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq (by lia) α)) := by
  have hα := Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq (q := q) (by lia) α
  have hS : (ShortComplex.mk α (cokernel.π α) (cokernel.condition α)).ShortExact :=
    { exact := ShortComplex.exact_cokernel α }
  obtain ⟨δS, δT, -, wS₂, -, wT₂, -, hS₂, -, hT₂, hδ⟩ :=
    Etale.exists_connecting_baseChangeHomologyMap Λ sq hS (q - 1) q (by lia)
  have := hprev g e h sq (cokernel α)
  have hG := Etale.isZero_baseChangeSourceFunctor_obj_of_injective Λ p g (q := q) (by lia) G
  have : Epi δS := hS₂.epi_f (hG.eq_of_tgt _ _)
  let φ : ShortComplex.mk (Etale.baseChangeHomologyMap Λ sq (q - 1) (cokernel α) ≫ δT)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (by simp [wT₂]) ⟶
      ShortComplex.mk (Etale.baseChangeHomologyMap Λ sq q F)
        ((Etale.baseChangeTargetFunctor Λ e h q).map α) hα :=
    { τ₁ := δS
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [hδ] }
  refine ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 ?_).mono_cokernelDesc
  let ψ : ShortComplex.mk (Etale.baseChangeHomologyMap Λ sq (q - 1) (cokernel α) ≫ δT)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (by simp [wT₂]) ⟶ ShortComplex.mk _ _ wT₂ :=
    { τ₁ := Etale.baseChangeHomologyMap Λ sq (q - 1) (cokernel α)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 hT₂

/-- Blueprint `lemma-injectivity-base-change-map-degree` (2): the cokernel of the critical map grows
with the coefficient sheaf.

In the situation of `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`, if `F` is a
subsheaf of `G`, then the map induced on the cokernels of the two base-change maps by the
naturality `AlgebraicGeometry.Etale.baseChangeHomologyMap_naturality` is injective. -/
@[stacks 0F03]
theorem Etale.mono_cokernelMap (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] :
    Mono (cokernel.map (Etale.baseChangeHomologyMap Λ sq q F)
      (Etale.baseChangeHomologyMap Λ sq q G) ((Etale.baseChangeSourceFunctor Λ p g q).map α)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (Etale.baseChangeHomologyMap_naturality Λ sq q α)) := by
  have hzero {K : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
      (β : K ⟶ Injective.under G) :=
    Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq (q := q) (by lia) β
  have hfac : cokernel.map (Etale.baseChangeHomologyMap Λ sq q F)
      (Etale.baseChangeHomologyMap Λ sq q G) ((Etale.baseChangeSourceFunctor Λ p g q).map α)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (Etale.baseChangeHomologyMap_naturality Λ sq q α) ≫
      cokernel.desc _ _ (hzero (Injective.ι G)) =
        cokernel.desc _ _ (hzero (α ≫ Injective.ι G)) := by
    refine coequalizer.hom_ext ?_
    simp
  have := Etale.mono_cokernelDesc Λ q hq hprev sq (α ≫ Injective.ι G)
  rw [← hfac] at this
  exact mono_of_mono _ (cokernel.desc _ _ (hzero (Injective.ι G)))

/-- Blueprint `lemma-injectivity-base-change-map-degree`: Injectivity of the critical map and its
cokernel.

Assume that `BC(p, Λ, q - 1)` holds universally for some `q ≥ 1`, and let `p' : X' ⟶ S'` be
the base change of `p` along `a : S' ⟶ S`. Then for every Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X' -p'-> S'
```

with `g` quasi-compact quasi-separated:

1. the base-change map `p'⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is injective for every `F`;
2. for a subsheaf `F ⊆ G`, the cokernel of the base-change map for `F` injects into the one
   for `G`;
3. if moreover `G` is injective, the cokernel of the base-change map for `F` injects into
   `R^q h_* e⁻¹ G`.

Only `BC(p', Λ, q - 1)`, which is part of the universal hypothesis, enters, through
`AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`,
`AlgebraicGeometry.Etale.mono_cokernelMap` and `AlgebraicGeometry.Etale.mono_cokernelDesc`. -/
@[stacks 0F03]
theorem Etale.UniversalBaseChangeProperty.mono_baseChangeHomologyMap_and_cokernel {q : ℤ}
    (hq : 1 ≤ q) (huniv : Etale.UniversalBaseChangeProperty Λ p (q - 1)) {S' X' : Scheme.{u}}
    {a : S' ⟶ S} {b : X' ⟶ X} {p' : X' ⟶ S'} (hp : IsPullback b p' p a) {g : T ⟶ S'}
    {h : Y ⟶ X'} [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p') :
    (∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Mono (Etale.baseChangeHomologyMap Λ sq q F)) ∧
    (∀ {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (α : F ⟶ G) [Mono α],
      Mono (cokernel.map (Etale.baseChangeHomologyMap Λ sq q F)
        (Etale.baseChangeHomologyMap Λ sq q G) ((Etale.baseChangeSourceFunctor Λ p' g q).map α)
        ((Etale.baseChangeTargetFunctor Λ e h q).map α)
        (Etale.baseChangeHomologyMap_naturality Λ sq q α))) ∧
    (∀ {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (α : F ⟶ G) [Mono α]
      [Injective G],
      Mono (cokernel.desc (Etale.baseChangeHomologyMap Λ sq q F)
        ((Etale.baseChangeTargetFunctor Λ e h q).map α)
        (Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq (by lia) α))) :=
  have hprev : Etale.BaseChangeProperty Λ p' (q - 1) := huniv a b p' hp
  ⟨Etale.mono_baseChangeHomologyMap Λ q hq hprev sq,
    fun α _ ↦ Etale.mono_cokernelMap Λ q hq hprev sq α,
    fun α _ _ ↦ Etale.mono_cokernelDesc Λ q hq hprev sq α⟩

end AlgebraicGeometry
