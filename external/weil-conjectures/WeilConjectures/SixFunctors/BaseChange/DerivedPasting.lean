/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical

/-!
# Pasting laws for the derived base change map and composition of `IsBaseChangeIso`

The derived base change map `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` satisfies the
same pasting laws as the underived one (`WeilConjectures.SixFunctors.BaseChange.Pasting`).
For two squares pasted vertically

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
  |          |
  e'         e
  ↓          ↓
  Z' --k---> Z
```

the derived base change map of the pasted square is the composite
`k^* R(f ≫ e)_* ≅ k^* Re_* Rf_* ⟶ Re'_* g^* Rf_* ⟶ Re'_* Rf'_* g'^* ≅ R(f' ≫ e')_* g'^*` of the
derived base change maps of the two squares, modulo the composition isomorphisms
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'` of the derived pushforwards
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_vert`). The proof is by the
uniqueness principle `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_ext`: both sides are
computed on bounded below complexes by the underived base change maps, and the underived
pasting law `AlgebraicGeometry.Etale.baseChangeMap_paste_vert` identifies the results. The
horizontal pasting law `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_horiz` (modulo
the composition isomorphisms `AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the derived
pullbacks) is proved in the same way.

As a consequence, the proper base change property is stable under composition: if `f` and `e`
satisfy `AlgebraicGeometry.Etale.IsBaseChangeIso`, so does `f ≫ e`
(`AlgebraicGeometry.Etale.IsBaseChangeIso.comp`), since every cartesian square on `f ≫ e`
is the vertical pasting of cartesian squares on `e` and on `f`
(`CategoryTheory.IsPullback.paste_vert`).
(blueprint: `lemma-identity-pasting`, vertical pasting;
`lemma:weil-pbc-composition`, formal part)

For the identity square on `f` the derived base change map is the identity, modulo the identity
isomorphisms of the derived pullbacks (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_id`);
with the horizontal pasting law this is blueprint `lemma-identity-pasting--1`.

The vertical pasting law and the composition of `IsBaseChangeIso` are in
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`, the horizontal one in
`...DerivedPasting.Horizontal` and the identity square in `...DerivedPasting.Identity`; this
module imports all of them.
-/
