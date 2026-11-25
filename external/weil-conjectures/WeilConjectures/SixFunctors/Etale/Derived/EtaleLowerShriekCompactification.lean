/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import WeilConjectures.SixFunctors.Etale.Derived.ClopenTransfer
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# The compactly supported direct image along an étale morphism

Let `e : X ⟶ Y` be étale and let `c = (X ⟶[j] Z ⟶[p] Y)` be a compactification of `e`. Write
`W = Z ×_Y X`, with projections `q_Z : W ⟶ Z` (étale) and `q : W ⟶ X` (proper). The graph
`σ = (j, 𝟙) : X ⟶ W` of `j` is a section of `q` which is both an open and a closed immersion
(`AlgebraicGeometry.Compactification.selfGraph`).

This file constructs the natural map `𝟭 ⟶ Le^* Rp_* Dj_!`
(`AlgebraicGeometry.Etale.compactificationEtaleUnit`), the candidate unit of an adjunction
`Rf_!(c) ⊣ Le^*`:

`K ⟶ Rq_* Lq^* K ⟶ Rq_* Lq_Z^* Dj_! K ≅ Le^* Rp_* Dj_! K`,

the last isomorphism being proper base change, and the middle map being "restrict to the graph
and extend by zero": `Lq^* K ⟶ Dσ_! Lσ^* Lq^* K ≅ Dσ_! Lσ^* Lq_Z^* Dj_! K ⟶ Lq_Z^* Dj_! K`, where
the first map comes from the adjunction `Lσ^* ⊣ Dσ_! ≅ Rσ_*` of the open and closed immersion
`σ`, and the last one is the counit of `Dσ_! ⊣ Lσ^*`
(`AlgebraicGeometry.Etale.compactificationEtaleGraphMap`).

Its transpose under the adjunction `De_! ⊣ Le^*` of the étale extension by zero is the comparison
`De_! ⟶ Rf_!(c)` (`AlgebraicGeometry.Etale.compactificationEtaleComparison`).

## Main definitions

- `AlgebraicGeometry.Compactification.selfGraph`
- `AlgebraicGeometry.Etale.compactificationEtaleGraphMap`
- `AlgebraicGeometry.Etale.compactificationEtaleUnit`
- `AlgebraicGeometry.Etale.compactificationEtaleComparison`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Compactification

variable {X Y : Scheme.{u}} {e : X ⟶ Y} (c : Compactification e)

/-- The graph `(j, 𝟙) : X ⟶ Z ×_Y X` of the open immersion `j : X ⟶ Z` of a compactification
of `e`. -/
noncomputable def selfGraph : X ⟶ pullback c.g e :=
  pullback.lift c.i (𝟙 X) (by rw [Category.id_comp, ← c.comm])

@[reassoc (attr := simp)]
lemma selfGraph_fst : c.selfGraph ≫ pullback.fst c.g e = c.i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma selfGraph_snd : c.selfGraph ≫ pullback.snd c.g e = 𝟙 X :=
  pullback.lift_snd _ _ _

instance : IsSplitMono c.selfGraph :=
  ⟨⟨⟨pullback.snd c.g e, c.selfGraph_snd⟩⟩⟩

/-- The graph is a closed immersion, being a section of the separated morphism
`Z ×_Y X ⟶ X`. -/
instance isClosedImmersion_selfGraph : IsClosedImmersion c.selfGraph := by
  have : IsProper c.g := c.isProper
  have : IsClosedImmersion (c.selfGraph ≫ pullback.snd c.g e) := by
    rw [selfGraph_snd]
    infer_instance
  exact IsClosedImmersion.of_comp c.selfGraph (pullback.snd c.g e)

/-- The graph is étale when `e` is: its composite with the étale projection `Z ×_Y X ⟶ Z` is the
open immersion `j`. -/
instance etale_selfGraph [_root_.AlgebraicGeometry.Etale e] :
    _root_.AlgebraicGeometry.Etale c.selfGraph := by
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : _root_.AlgebraicGeometry.Etale (c.selfGraph ≫ pullback.fst c.g e) := by
    rw [selfGraph_fst]
    infer_instance
  exact _root_.AlgebraicGeometry.Etale.of_comp c.selfGraph (pullback.fst c.g e)

/-- The graph is an open immersion when `e` is étale: it is a flat monomorphism locally of
finite presentation. -/
instance isOpenImmersion_selfGraph [_root_.AlgebraicGeometry.Etale e] :
    IsOpenImmersion c.selfGraph :=
  IsOpenImmersion.of_flat_of_mono c.selfGraph

end Compactification

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Construction

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)

/-- The isomorphism `Lq^* ⋙ Lσ^* ≅ Dj_! ⋙ Lq_Z^* ⋙ Lσ^*`: both sides are identified with the
identity, through `σ ≫ q = 𝟙` and `σ ≫ q_Z = j`, and the unit of `Dj_! ⊣ Lj^*`. -/
noncomputable def compactificationEtaleGraphIso :
    L((pullback.snd c.g e)^*[ModuleCat.{u + 1} Λ]) ⋙ L((c.selfGraph)^*[ModuleCat.{u + 1} Λ]) ≅
      (D((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ L((pullback.fst c.g e)^*[ModuleCat.{u + 1} Λ])) ⋙
        L((c.selfGraph)^*[ModuleCat.{u + 1} Λ]) :=
  have : IsOpenImmersion c.i := c.isOpenImmersion
  leftDerivedUpperStarCompSectionIso _ c.selfGraph (pullback.snd c.g e) c.selfGraph_snd ≪≫
    asIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i).unit ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp _ c.selfGraph (pullback.fst c.g e) c.i
      c.selfGraph_fst.symm) ≪≫
    (Functor.associator _ _ _).symm

/-- The map `Lq^* ⟶ Dj_! ⋙ Lq_Z^*` "restricting to the graph and extending by zero"
(`AlgebraicGeometry.Etale.clopenTransfer` of
`AlgebraicGeometry.Etale.compactificationEtaleGraphIso`):
`Lq^* K ⟶ Dσ_! Lσ^* Lq^* K ≅ Dσ_! Lσ^* Lq_Z^* Dj_! K ⟶ Lq_Z^* Dj_! K`. -/
noncomputable def compactificationEtaleGraphMap :
    L((pullback.snd c.g e)^*[ModuleCat.{u + 1} Λ]) ⟶
      D((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ L((pullback.fst c.g e)^*[ModuleCat.{u + 1} Λ]) where
  app N := clopenTransfer Λ ((compactificationEtaleGraphIso Λ e c).hom.app N)
  naturality N N' f := by
    have hn := (compactificationEtaleGraphIso Λ e c).hom.naturality f
    rw [← clopenTransfer_comp_left, ← clopenTransfer_comp_right]
    exact congrArg (clopenTransfer Λ) hn


instance : IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback c.g e).toCommSq) :=
  have : IsProper c.g := c.isProper
  isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite
    (IsPullback.of_hasPullback c.g e)

/-- The candidate unit `𝟭 ⟶ Rf_!(c) ⋙ Le^*` of an adjunction `Rf_!(c) ⊣ Le^*`:
`K ⟶ Rq_* Lq^* K ⟶ Rq_* Lq_Z^* Dj_! K ≅ Le^* Rp_* Dj_! K`. -/
noncomputable def compactificationEtaleUnit :
    𝟭 _ ⟶ Rf_!(c)[ModuleCat.{u + 1} Λ] ⋙ L((e)^*[ModuleCat.{u + 1} Λ]) :=
  (derivedUpperStarLowerStarAdjunction _ (pullback.snd c.g e)).unit ≫
    Functor.whiskerRight (compactificationEtaleGraphMap Λ e c) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (inv (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback c.g e).toCommSq)) ≫
    (Functor.associator _ _ _).inv

/-- The comparison `De_! ⟶ Rf_!(c)`: the transpose of
`AlgebraicGeometry.Etale.compactificationEtaleUnit` under `De_! ⊣ Le^*`. -/
noncomputable def compactificationEtaleComparison :
    D(etaleLowerShriek (ModuleCat.{u + 1} Λ) e inferInstance) ⟶ Rf_!(c)[ModuleCat.{u + 1} Λ] :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (compactificationEtaleUnit Λ e c) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (derivedEtaleLowerShriekAdjunction _ e).counit ≫
    (Functor.rightUnitor _).hom

end Construction

end Etale

end AlgebraicGeometry
