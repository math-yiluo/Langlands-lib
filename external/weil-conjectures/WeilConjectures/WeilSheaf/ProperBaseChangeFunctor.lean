/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.WeilSheaf.LowerStar
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Native.NativeProperNaturalBaseChange

/-!
# Proper base change for Weil complexes, as an isomorphism of functors

For a cartesian square of `k₀`-schemes
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
with `f` proper, the base change morphism `g^* Rf_* ⟶ Rf'_* g'^*` of Weil complexes is a natural
isomorphism (blueprint `theorem-purity-higher-direct-images-under--2`, the base change morphism
being a morphism of Weil complexes by `sec-Weil-complexes`). It is stated as the existence of a
natural isomorphism, in the form needed for the compatibilities of the direct image with compact
support (`WeilConjectures.WeilSheaf.LowerShriekIndependence`); the objectwise statement is
`AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

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

/-- **Proper base change for Weil complexes, naturally** (blueprint
`theorem-purity-higher-direct-images-under--2`, with the Weil structures of `sec-Weil-complexes`):
for a cartesian square of `k₀`-schemes `X' = X ×_Y Y'` with `f : X ⟶ Y` proper,
`g^* ∘ Rf_* ≅ Rf'_* ∘ g'^*` as functors of Weil complexes on `X`. -/
theorem WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper
    (hf : IsProper f) (h : IsPullback g' f' f g) :
    Nonempty (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) f ⋙ WeilComplex.upperStar g ≅
      WeilComplex.upperStar g' ⋙ WeilComplex.derivedLowerStar f') := by
  let : IsProper f := hf
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian Y' :=
    LocallyOfFiniteType.isLocallyNoetherian (Y' ↘ Spec (CommRingCat.of k₀))
  let sq : ChosenCartesianSquare g' f' f g :=
    { toCommSq := h.toCommSq
      isoPullback := h.isoPullback
      hom_fst := h.isoPullback_hom_fst
      hom_snd := h.isoPullback_hom_snd }
  obtain ⟨e⟩ := nativeWeil_proper_natural_baseChange k₀ l g' f' f g sq
  let P := WeilComplex.objectProperty k₀ l Y'
  let ef : WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) f ⋙
      (WeilComplex.objectProperty k₀ l Y).ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor :=
    ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  let ef' : WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) f' ⋙ P.ι ≅
      (WeilComplex.objectProperty k₀ l X').ι ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l f').rightDerivedFunctor :=
    ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  let eg : WeilComplex.upperStar (k₀ := k₀) (l := l) g ⋙ P.ι ≅
      (WeilComplex.objectProperty k₀ l Y).ι ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory :=
    ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  let eg' : WeilComplex.upperStar (k₀ := k₀) (l := l) g' ⋙ (WeilComplex.objectProperty k₀ l X').ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l g').mapDerivedCategory :=
    ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  refine ⟨(P.fullyFaithfulι.whiskeringRight _).preimageIso ?_⟩
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eg ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ef _ ≪≫
    Functor.associator _ _ _ ≪≫ e ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eg'.symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ef'.symm ≪≫ (Functor.associator _ _ _).symm

end AlgebraicGeometry
