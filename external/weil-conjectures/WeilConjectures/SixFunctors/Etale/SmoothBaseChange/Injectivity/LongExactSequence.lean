/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# The long exact sequences of the base-change map

For a Cartesian square on `p : X ⟶ S` along `g : T ⟶ S` and a short exact sequence of
coefficient sheaves on `T_ét`, the degree-`q` base-change maps
`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` form a morphism between the two long exact sequences of
higher direct images. The source of the base-change map vanishes on injective sheaves in
nonzero degrees. These are the inputs of the injectivity statements of
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap` and of the
dévissage of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage`.

## Main statements

- `AlgebraicGeometry.Etale.isZero_baseChangeSourceFunctor_obj_of_injective`: the source of
  the degree-`q` base-change map vanishes on injective sheaves for `q ≠ 0`.
- `AlgebraicGeometry.Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective`: for `q ≠ 0`,
  the base-change map followed by `R^q h_* e⁻¹` of a map into an injective sheaf is zero.
- `AlgebraicGeometry.Etale.exists_connecting_baseChangeHomologyMap`: the base-change maps
  form a morphism between the two long exact sequences attached to a short exact sequence of
  coefficient sheaves.

## Implementation notes

The long exact sequences are the homology sequences of the images of the distinguished triangle
`F₁[0] ⟶ F₂[0] ⟶ F₃[0] ⟶ F₁[1]` under the triangulated functors `p^* ∘ Rg_*` and
`Rh_* ∘ e^*`; the base-change maps form a morphism between them because the derived
base-change morphism commutes with the shifts (`AlgebraicGeometry.Etale.commShift_baseChange`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}
  {T Y : Scheme.{u}} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The source of the base-change map vanishes in nonzero degrees on an injective sheaf `I`:
the derived pushforward of `I` placed in degree `0` is `g_* I` placed in degree `0`, so
`p⁻¹ R^q g_* I = 0` for `q ≠ 0`. This is the injective-acyclicity input of the blueprint
lemma `lemma-injectivity-base-change-map-degree`. -/
lemma Etale.isZero_baseChangeSourceFunctor_obj_of_injective (p : X ⟶ S) (g : T ⟶ S) {q : ℤ}
    (hq : q ≠ 0) (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] :
    IsZero ((Etale.baseChangeSourceFunctor Λ p g q).obj I) := by
  let e := D+((p)^*[ModuleCat.{u + 1} Λ]).mapIso
      (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusObjSingleFunctorIso 0 I) ≪≫
    (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app _
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ q).mapIso e)
  rcases hq.lt_or_gt with hq | hq
  · exact DerivedCategory.Plus.isZero_homology_of_isGE
      ((DerivedCategory.Plus.singleFunctor _ 0).obj _) 0 q hq
  · exact DerivedCategory.Plus.isZero_homology_of_isLE
      ((DerivedCategory.Plus.singleFunctor _ 0).obj _) 0 q hq

/-- For `q ≠ 0` and a morphism `α : F ⟶ G` to an injective sheaf `G`, the composite
`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F ⟶ R^q h_* e⁻¹ G` of the base-change map with `R^q h_* e⁻¹ α`
vanishes: by naturality it factors through `p⁻¹ R^q g_* G`, which is zero. -/
lemma Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective (sq : IsPullback e h g p)
    {q : ℤ} (hq : q ≠ 0) {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Injective G] :
    Etale.baseChangeHomologyMap Λ sq q F ≫ (Etale.baseChangeTargetFunctor Λ e h q).map α =
      0 := by
  rw [Etale.baseChangeHomologyMap_naturality,
    (Etale.isZero_baseChangeSourceFunctor_obj_of_injective Λ p g hq G).eq_of_tgt
      ((Etale.baseChangeSourceFunctor Λ p g q).map α) 0, zero_comp]

/-- The two long exact sequences of the base-change map. For a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves of `Λ`-modules on `T_ét` and `n₀ + 1 = n₁`, there are
connecting maps `δS : p⁻¹ R^{n₀} g_* F₃ ⟶ p⁻¹ R^{n₁} g_* F₁` and
`δT : R^{n₀} h_* e⁻¹ F₃ ⟶ R^{n₁} h_* e⁻¹ F₁` making the two sequences

`p⁻¹ R^{n₀} g_* F₂ ⟶ p⁻¹ R^{n₀} g_* F₃ ⟶ p⁻¹ R^{n₁} g_* F₁ ⟶ p⁻¹ R^{n₁} g_* F₂`,
`R^{n₀} h_* e⁻¹ F₂ ⟶ R^{n₀} h_* e⁻¹ F₃ ⟶ R^{n₁} h_* e⁻¹ F₁ ⟶ R^{n₁} h_* e⁻¹ F₂`

exact, and such that the square

```
p⁻¹ R^{n₀} g_* F₃ --δS--> p⁻¹ R^{n₁} g_* F₁
        |                         |
  bc_{n₀} F₃                bc_{n₁} F₁
        v                         v
R^{n₀} h_* e⁻¹ F₃ --δT--> R^{n₁} h_* e⁻¹ F₁
```

of base-change maps commutes.

This is the long exact sequence input of the blueprint lemma
`lemma-injectivity-base-change-map-degree` (the blueprint lemma
`theorem-proper-base-change-classical-pro` of the proper base change chapter). It comes from the
distinguished triangle of the short exact sequence: its images under the triangulated functors
`p^* ∘ Rg_*` and `Rh_* ∘ e^*` are distinguished, and the derived base-change morphism
`AlgebraicGeometry.Etale.baseChange` is a morphism between them since it commutes with the shifts
(`AlgebraicGeometry.Etale.commShift_baseChange`). -/
theorem Etale.exists_connecting_baseChangeHomologyMap (sq : IsPullback e h g p)
    {E : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hE : E.ShortExact)
    (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    ∃ (δS : (Etale.baseChangeSourceFunctor Λ p g n₀).obj E.X₃ ⟶
        (Etale.baseChangeSourceFunctor Λ p g n₁).obj E.X₁)
      (δT : (Etale.baseChangeTargetFunctor Λ e h n₀).obj E.X₃ ⟶
        (Etale.baseChangeTargetFunctor Λ e h n₁).obj E.X₁)
      (wS₁ : (Etale.baseChangeSourceFunctor Λ p g n₀).map E.g ≫ δS = 0)
      (wS₂ : δS ≫ (Etale.baseChangeSourceFunctor Λ p g n₁).map E.f = 0)
      (wT₁ : (Etale.baseChangeTargetFunctor Λ e h n₀).map E.g ≫ δT = 0)
      (wT₂ : δT ≫ (Etale.baseChangeTargetFunctor Λ e h n₁).map E.f = 0),
      (ShortComplex.mk _ _ wS₁).Exact ∧ (ShortComplex.mk _ _ wS₂).Exact ∧
      (ShortComplex.mk _ _ wT₁).Exact ∧ (ShortComplex.mk _ _ wT₂).Exact ∧
      δS ≫ Etale.baseChangeHomologyMap Λ sq n₁ E.X₁ =
        Etale.baseChangeHomologyMap Λ sq n₀ E.X₃ ≫ δT :=
  -- The concrete functors are only passed as data with `rfl` equations: unifying them with
  -- the abstract composites directly makes the kernel unfold the derived functors. Both lemmas
  -- below accept the zero morphisms of the sheaf categories as they are, for the same reason.
  hE.exists_mk_singleTrianglePlus_distinguished.elim fun δ hδ ↦
  Functor.exists_homologySequenceδ_whiskerRight'
    (DerivedCategory.Plus.homologyFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq)
    (DerivedCategory.Plus.homologyFunctor _) (fun _ ↦ rfl) (Etale.baseChangeSourceFunctor Λ p g)
    (Etale.baseChangeTargetFunctor Λ e h) (Etale.baseChangeHomologyNatTrans Λ sq) rfl E δ hδ
    n₀ n₁ hn

end AlgebraicGeometry
