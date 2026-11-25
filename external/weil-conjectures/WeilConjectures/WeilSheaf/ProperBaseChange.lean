/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.WeilSheaf.ProperBaseChangeFunctor
public import WeilConjectures.WeilSheaf.TraceFunctionOps

/-!
# Proper base change for Weil complexes

For a cartesian square of `k₀`-schemes

```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```

with `f` proper, the base change isomorphism `g^* Rf_* K ≅ Rf'_* g'^* K` holds for Weil complexes
`K` on `X`, and taking cohomology sheaves, `g^* Rⁱf_* F ≅ Rⁱf'_* g'^* F` for Weil sheaves.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper`
  (`theorem-purity-higher-direct-images-under--2`, with the Weil structures of
  `sec-Weil-complexes`).
- `AlgebraicGeometry.WeilSheaf.nonempty_upperStar_higherLowerStar_iso_of_isProper`: the form for
  higher direct images of Weil sheaves.

## Implementation notes

The objectwise statement is the component of the natural isomorphism
`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Pullback commutes with placing a Weil sheaf in degree zero: `φ^* (F[0]) ≅ (φ^* F)[0]`, the
pullback of Weil complexes being induced by the exact pullback of pro-étale Weil sheaves. -/
noncomputable def WeilSheaf.upperStarToComplexIso {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l Y) :
    (WeilComplex.upperStar φ).obj (WeilSheaf.toComplex.obj F) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.upperStar φ).obj F) :=
  ObjectProperty.isoMk _
    (((ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategorySingleFunctor 0).app F.obj)

/-- The higher direct image `Rⁱφ_* F` is the `i`-th cohomology sheaf of `Rφ_*(F[0])`. Stated
as a lemma so that rewriting with it avoids unfolding `higherLowerStar` in the kernel. -/
theorem WeilSheaf.higherLowerStar_obj {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (i : ℕ) (F : WeilSheaf k₀ l X) :
    (WeilSheaf.higherLowerStar φ i).obj F = (WeilComplex.homologySheaf i).obj
      ((WeilComplex.derivedLowerStar φ).obj (WeilSheaf.toComplex.obj F)) :=
  rfl

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [X'.Over (Spec (CommRingCat.of k₀))]
  [Y'.Over (Spec (CommRingCat.of k₀))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
  [f'.IsOver (Spec (CommRingCat.of k₀))] [g'.IsOver (Spec (CommRingCat.of k₀))]
  [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f'] [QuasiSeparated f'] [LocallyOfFiniteType f']
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]

/-- **Proper base change for Weil complexes** (blueprint
`theorem-purity-higher-direct-images-under--2`, the base change isomorphism being a morphism of Weil
complexes by `sec-Weil-complexes`): for a cartesian square of `k₀`-schemes `X' = X ×_Y Y'` with
`f : X ⟶ Y` proper, and a Weil complex `K` on `X`, there is an isomorphism of Weil complexes
`g^* Rf_* K ≅ Rf'_* g'^* K`. -/
theorem WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper
    (hf : IsProper f) (h : IsPullback g' f' f g) (K : WeilComplex k₀ l X) :
    Nonempty ((WeilComplex.upperStar g).obj ((WeilComplex.derivedLowerStar f).obj K) ≅
      (WeilComplex.derivedLowerStar f').obj ((WeilComplex.upperStar g').obj K)) :=
  (WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper hf h).map (·.app K)

/-- **Proper base change for higher direct images**: for a cartesian square of `k₀`-schemes
`X' = X ×_Y Y'` with `f : X ⟶ Y` proper, and a Weil sheaf `F` on `X`, there is an isomorphism of
Weil sheaves `g^* Rⁱf_* F ≅ Rⁱf'_* g'^* F`: the cohomology sheaves of the proper base change
isomorphism of Weil complexes, the pullback of Weil complexes being induced by the exact pullback
of Weil sheaves. -/
theorem WeilSheaf.nonempty_upperStar_higherLowerStar_iso_of_isProper
    (hf : IsProper f) (h : IsPullback g' f' f g) (F : WeilSheaf k₀ l X) (i : ℕ) :
    Nonempty ((WeilSheaf.upperStar g).obj ((WeilSheaf.higherLowerStar f i).obj F) ≅
      (WeilSheaf.higherLowerStar f' i).obj ((WeilSheaf.upperStar g').obj F)) := by
  obtain ⟨e⟩ := WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper hf h
    (WeilSheaf.toComplex.obj F)
  rw [WeilSheaf.higherLowerStar_obj, WeilSheaf.higherLowerStar_obj]
  exact ⟨(WeilComplex.homologySheafUpperStarIso g i _).symm ≪≫
    (WeilComplex.homologySheaf i).mapIso
      (e ≪≫ (WeilComplex.derivedLowerStar f').mapIso (WeilSheaf.upperStarToComplexIso g' F))⟩

end AlgebraicGeometry
