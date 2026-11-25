/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # The explicit locally closed graph model for étale compact support

Source: `WeilConjectures/SixFunctors/Etale/Derived/LowerShriekComposition.lean`,
`nonempty_iso_rightDerivedLowerShriekOfCompactification`, lines 193--268; Stacks Project,
Tag 0F7B, lemma `shriek-proper-and-open` (auxiliary; not a blueprint node).

The graph maps and the three constituent isomorphisms are explicit constructions. The
existence theorem supplies their properness and the specified endpoint comparison, without
choosing data from a postponed existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {X Y C U P : Scheme.{u}}
variable (a : X ⟶ U) (e : U ⟶ P) (π : P ⟶ Y) (j : X ⟶ C) (c : C ⟶ Y)
variable (h : (a ≫ e) ≫ π = j ≫ c)

/-- The map `v = (ea,j)` to `T = P ×_Y C`.
Source: `LowerShriekComposition.lean`, graph construction, lines 199--205
(auxiliary; not a blueprint node). -/
def locallyClosedGraphV : X ⟶ pullback π c :=
  pullback.lift (a ≫ e) j h

/-- The graph `s₁ = (v,1)` into `O₁ = T ×_C X`.
Source: `LowerShriekComposition.lean`, lines 206--212
(auxiliary; not a blueprint node). -/
def locallyClosedGraphS₁ : X ⟶ pullback (pullback.snd π c) j :=
  pullback.lift (locallyClosedGraphV a e π j c h) (𝟙 X)
    (by simp [locallyClosedGraphV])

/-- The graph `s₂ = (v,a)` into `O₂ = T ×_P U`.
Source: `LowerShriekComposition.lean`, lines 213--220
(auxiliary; not a blueprint node). -/
def locallyClosedGraphS₂ : X ⟶ pullback (pullback.fst π c) e :=
  pullback.lift (locallyClosedGraphV a e π j c h) a
    (by simp [locallyClosedGraphV])

/-- The common graph `s₁₂ = (s₁,s₂)` in `O₁₂ = O₁ ×_T O₂`.
Source: `LowerShriekComposition.lean`, lines 221--224
(auxiliary; not a blueprint node). -/
def locallyClosedGraphS₁₂ :
    X ⟶ pullback (pullback.fst (pullback.snd π c) j)
      (pullback.fst (pullback.fst π c) e) :=
  pullback.lift (locallyClosedGraphS₁ a e π j c h) (locallyClosedGraphS₂ a e π j c h)
    (by simp [locallyClosedGraphS₁, locallyClosedGraphS₂])

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable [IsOpenImmersion j] [IsProper c] [IsProper a] [IsOpenImmersion e] [IsProper π]

/-- The specified `B₁`, inserting `Rq₁_* Rs₁_* = R(1_X)_*` and applying the Cartesian
proper/open interchange for `O₁ = T ×_C X`.
Source: `LowerShriekComposition.lean`, `eA`, lines 237--249
(auxiliary; not a blueprint node). -/
def locallyClosedGraphSide₁ :
    D((j)_!open[ModuleCat.{u + 1} A]) ⋙ R((c)_*[ModuleCat.{u + 1} A]) ≅
      R((locallyClosedGraphS₁ a e π j c h)_*[ModuleCat.{u + 1} A]) ⋙
        D((pullback.fst (pullback.snd π c) j)_!open[ModuleCat.{u + 1} A]) ⋙
          R((pullback.fst π c ≫ π)_*[ModuleCat.{u + 1} A]) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight ((rightDerivedLowerStarIdIso A X).symm ≪≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (locallyClosedGraphS₁ a e π j c h) (pullback.snd (pullback.snd π c) j)
        (𝟙 X) (by simp [locallyClosedGraphS₁])).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A
        (IsPullback.of_hasPullback (pullback.snd π c) j).flip) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (pullback.snd π c) c (pullback.fst π c ≫ π) pullback.condition.symm))

/-- The specified `B₂`, inserting `Rq₂_* Rs₂_* = Ra_*` and applying the Cartesian
proper/open interchange for `O₂ = T ×_P U`.
Source: `LowerShriekComposition.lean`, `eB`, lines 250--260
(auxiliary; not a blueprint node). -/
def locallyClosedGraphSide₂ :
    R((a)_*[ModuleCat.{u + 1} A]) ⋙ D((e)_!open[ModuleCat.{u + 1} A]) ⋙
      R((π)_*[ModuleCat.{u + 1} A]) ≅
    R((locallyClosedGraphS₂ a e π j c h)_*[ModuleCat.{u + 1} A]) ⋙
      D((pullback.fst (pullback.fst π c) e)_!open[ModuleCat.{u + 1} A]) ⋙
        R((pullback.fst π c ≫ π)_*[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerRight (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
      (locallyClosedGraphS₂ a e π j c h) (pullback.snd (pullback.fst π c) e) a
      (by simp [locallyClosedGraphS₂])).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A
        (IsPullback.of_hasPullback (pullback.fst π c) e).flip) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (pullback.fst π c) π (pullback.fst π c ≫ π) rfl))

variable [IsProper (locallyClosedGraphS₁ a e π j c h)]
  [IsProper (locallyClosedGraphS₂ a e π j c h)]

/-- The specified `B₁₂`: invert the identity-top proper/open interchange over `O₁`,
compose the two open extensions, identify `b₁u₁ = b₂u₂`, split the open extensions over
`O₂`, and apply the identity-top interchange there.
Source: `LowerShriekComposition.lean`, `eGamma`, `eh`, `eC`, lines 225--236
(auxiliary; not a blueprint node). -/
def locallyClosedGraphMiddle :
    R((locallyClosedGraphS₁ a e π j c h)_*[ModuleCat.{u + 1} A]) ⋙
      D((pullback.fst (pullback.snd π c) j)_!open[ModuleCat.{u + 1} A]) ≅
    R((locallyClosedGraphS₂ a e π j c h)_*[ModuleCat.{u + 1} A]) ⋙
      D((pullback.fst (pullback.fst π c) e)_!open[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
        (locallyClosedGraphS₁₂ a e π j c h) _ (locallyClosedGraphS₁ a e π j c h)
        (by simp [locallyClosedGraphS₁₂])).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) _ _).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
          pullback.condition ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
        (locallyClosedGraphS₁₂ a e π j c h) _ (locallyClosedGraphS₂ a e π j c h)
        (by simp [locallyClosedGraphS₁₂])) _

/-- The explicit final comparison `B = B₂⁻¹ R(πp₁)_*(B₁₂) B₁`, including associators.
Source: `LowerShriekComposition.lean`, final composite, lines 261--262
(auxiliary; not a blueprint node). -/
def locallyClosedGraphIso :
    D((j)_!open[ModuleCat.{u + 1} A]) ⋙ R((c)_*[ModuleCat.{u + 1} A]) ≅
      R((a)_*[ModuleCat.{u + 1} A]) ⋙ D((e)_!open[ModuleCat.{u + 1} A]) ⋙
        R((π)_*[ModuleCat.{u + 1} A]) :=
  locallyClosedGraphSide₁ a e π j c h A ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (locallyClosedGraphMiddle a e π j c h A) _ ≪≫
    Functor.associator _ _ _ ≪≫ (locallyClosedGraphSide₂ a e π j c h A).symm

/-- The graph-model assertion, keeping the three properness witnesses and the comparison
with its specified normalization. These are the clauses of the graph-model theorem, not
an arbitrary choice of an endpoint isomorphism.
Source: `LowerShriekComposition.lean`, lines 193--268, and Stacks Tag 0F7B(b)
(auxiliary; not a blueprint node). -/
structure LocallyClosedGraphModel where
  [properS₁ : IsProper (locallyClosedGraphS₁ a e π j c h)]
  [properS₂ : IsProper (locallyClosedGraphS₂ a e π j c h)]
  properS₁₂ : IsProper (locallyClosedGraphS₁₂ a e π j c h)
  comparison : D((j)_!open[ModuleCat.{u + 1} A]) ⋙ R((c)_*[ModuleCat.{u + 1} A]) ≅
    R((a)_*[ModuleCat.{u + 1} A]) ⋙ D((e)_!open[ModuleCat.{u + 1} A]) ⋙
      R((π)_*[ModuleCat.{u + 1} A])
  comparison_eq : comparison = locallyClosedGraphIso a e π j c h A

/-- The proper-open-proper graph model and its explicitly normalized comparison exist
on ordinary unbounded small-étale module derived categories.

Source: `LowerShriekComposition.lean`, lines 193--268; Stacks Tag 0F7B(b)
(auxiliary; not a blueprint node).

Proof:
1. Use the universal property of `P ×_Y C` to construct `v = (ea,j)`. Base change makes
   `b₁,b₂` open and makes `p₁,p₂,q₁,q₂` proper, hence separated. The identities
   `s₁q₁ = 1_X` and `s₂q₂ = a` and proper-to-separated imply properness of `s₁,s₂`.
   This uses the fibre-product, open/proper-base-change, and proper-to-separated nodes.
2. Construct `s₁₂` by the pullback universal property. The open projections `u₁,u₂` are
   monomorphisms, so both squares with identity top arrow and right arrow `s₁,s₂` are
   Cartesian. Proper base change gives properness of `s₁₂`.
3. Descend exact open extension and its canonical composition and identity isomorphisms
   degreewise. Use the normalized direct-image compositors and identity comparison
   of the derived-pushforward-composition and ringed-derived-monoidal-comparisons nodes.
4. Insert `Rq₁_* Rs₁_* = R(1_X)_*` and `Rq₂_* Rs₂_* = Ra_*`. Apply the Cartesian
   proper/open interchange (lem-sf-etale-proper-open-tensor-square) for `p₂,j` and `p₁,e`.
   Composing direct images gives exactly `locallyClosedGraphSide₁` and `Side₂`.
5. The identity-top proper/open interchanges for `s₁,s₂` and the open compositors
   (proposition-composition-base-change-rf-shriek--1) give exactly `locallyClosedGraphMiddle` on the
   intersection: invert the first interchange, combine the open maps, use the pullback
   equality, split the open maps, and apply the second interchange.
6. Whisker this middle comparison by `R(πp₁)_*`, insert the associators, and compose
   with `B₁` and `B₂⁻¹`. This is `locallyClosedGraphIso`; every constituent is a natural
   isomorphism. Finite coefficients suffice, without quasi-compactness or Noetherianity.
   No tensor-compatibility assertion is made. -/
theorem etaleLocallyClosedGraphModel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y C U P : Scheme.{u}} {f : X ⟶ Y}
    (a : X ⟶ U) (e : U ⟶ P) (π : P ⟶ Y) (j : X ⟶ C) (c : C ⟶ Y)
    [IsOpenImmersion j] [IsProper c] [IsProper a] [IsOpenImmersion e] [IsProper π]
    (h₁ : j ≫ c = f) (h₂ : a ≫ e ≫ π = f) :
    Nonempty (LocallyClosedGraphModel a e π j c
      ((Category.assoc a e π).trans (h₂.trans h₁.symm)) A) := by
  let h := (Category.assoc a e π).trans (h₂.trans h₁.symm)
  have : IsProper (locallyClosedGraphS₁ a e π j c h ≫
      pullback.snd (pullback.snd π c) j) := by
    simpa only [locallyClosedGraphS₁, pullback.lift_snd] using
      (inferInstance : IsProper (𝟙 X))
  have : IsProper (locallyClosedGraphS₁ a e π j c h) :=
    IsProper.of_comp _ (pullback.snd (pullback.snd π c) j)
  have : IsProper (locallyClosedGraphS₂ a e π j c h ≫
      pullback.snd (pullback.fst π c) e) := by
    simpa only [locallyClosedGraphS₂, pullback.lift_snd] using
      (inferInstance : IsProper a)
  have : IsProper (locallyClosedGraphS₂ a e π j c h) :=
    IsProper.of_comp _ (pullback.snd (pullback.fst π c) e)
  have : IsProper (locallyClosedGraphS₁₂ a e π j c h ≫
      pullback.fst (pullback.fst (pullback.snd π c) j)
        (pullback.fst (pullback.fst π c) e)) := by
    simpa only [locallyClosedGraphS₁₂, pullback.lift_fst] using
      (inferInstance : IsProper (locallyClosedGraphS₁ a e π j c h))
  have hs₁₂ : IsProper (locallyClosedGraphS₁₂ a e π j c h) :=
    IsProper.of_comp _ (pullback.fst (pullback.fst (pullback.snd π c) j)
      (pullback.fst (pullback.fst π c) e))
  exact ⟨{
    properS₁₂ := hs₁₂
    comparison := locallyClosedGraphIso a e π j c h A
    comparison_eq := rfl }⟩

end AlgebraicGeometry.Etale
