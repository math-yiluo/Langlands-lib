/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Comparison

/-!
# The extension by zero and the pushforward vanish off an open immersion

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement`.

Let `j : U ⟶ X` and `k : W ⟶ X` be open immersions with **disjoint** ranges. This file proves
that both `k^* j_! F` and `k^* j_* F` are initial as sheaves on the small pro-étale site of
`W`, and deduces that `k^*` of the comparison `j_! ⟶ j_*` is an isomorphism.

Together with the `j^*` half (`j_!` fully faithful for an open immersion, proved in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful`),
this is the sheaf-theoretic input to the comparison `j_! ⟶ j_*` being an isomorphism for an open
immersion with closed range. It is the one place where the zero object of the abelian `A`
is consumed, and genuinely so: for `A = Type` and `k` with nonempty source, `k^* j_* F` has
singleton sections `F(∅)` while `k^* j_! F` is empty, so the comparison is not an
isomorphism there.

## The argument

Everything rests on one geometric fact: for `T` weakly étale over `W`, the fibre product
`T ×_X U` is **empty**, because the ranges of `j` and `k` are disjoint
(`AlgebraicGeometry.isEmpty_pullback_of_disjoint_range`). A sheaf has terminal sections over
an object with empty underlying scheme
(`AlgebraicGeometry.Scheme.ProEt.isTerminalSectionsOfIsEmpty`, itself the sheaf condition for
the empty covering), and with a zero object in `A` terminal means zero. Hence:

- `k^* j_* F` has zero sections, since `(k^* j_* F)(T) = F(T ×_X U) = F(∅)`. A sheaf with zero
  sections is both initial and terminal.
- `k^* j_! F` is initial, and this is proved **without computing any of its sections** — `j_!`
  is a sheafification, which is exactly what makes the naive route hard. Instead, for every `H`,
  the two adjunctions give
  `Hom(k^* j_! F, H) ≃ Hom(j_! F, k_* H) ≃ Hom(F, j^* k_* H)`, and `j^* k_* H` has zero sections
  by the same computation with the roles of `j` and `k` exchanged. So the Hom-set is a singleton.

Both being initial, the comparison between them is *the* map out of an initial object, hence an
isomorphism.

## Main results

- `AlgebraicGeometry.ProEtale.isZero_openImmersionRestriction_lowerStar` and
  `AlgebraicGeometry.ProEtale.isInitial_openImmersionRestriction_openImmersionLowerShriek`: the
  two vanishing statements.
- `AlgebraicGeometry.ProEtale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar`:
  `k^*` of the comparison is an isomorphism, for disjoint `j` and `k`.

The geometric input `AlgebraicGeometry.isEmpty_pullback_of_disjoint_range` lives in
`WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion`, and the sheaf-theoretic inputs
`CategoryTheory.Sheaf.isTerminalOfIsTerminalObj`, `CategoryTheory.Sheaf.isZero_of_isZero_obj`
and `CategoryTheory.Sheaf.isInitialOfIsZeroObj` in
`WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf`. Both are shared with the étale
counterpart.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

/-! ### The sections of `k^* j_*` and of `j^* k_*` -/

section Disjoint

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U W X : Scheme.{u}} (j : U ⟶ X) (k : W ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]

open ProEtale

set_option backward.isDefEq.respectTransparency false in
omit [IsOpenImmersion j] in
/-- For `T` weakly étale over `W`, the fibre product `T ×_X U` is empty when the ranges of `j`
and `k` are disjoint: `T` maps into the range of `k`, which misses the range of `j`. Here `j`
is arbitrary. -/
lemma Scheme.ProEt.isEmpty_left_pullback_map
    (hjk : Set.range j.base ∩ Set.range k.base = ∅) (T : W.ProEt) :
    IsEmpty ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ k)).obj T)).left := by
  refine ⟨fun z ↦ ?_⟩
  have hz : (Limits.pullback.fst (T.hom ≫ k) j ≫ T.hom ≫ k).base z ∈
      Set.range j.base ∩ Set.range k.base := by
    refine ⟨?_, ⟨T.hom.base (Limits.pullback.fst (T.hom ≫ k) j z), ?_⟩⟩
    · rw [Limits.pullback.condition]
      exact ⟨_, rfl⟩
    · rfl
  rw [hjk] at hz
  exact hz

set_option backward.isDefEq.respectTransparency false in
omit [IsOpenImmersion j] in
/-- The sections of `k^* j_* F` over `T : W.ProEt` are `F(T ×_X U) = F(∅)`, hence terminal.
Here `j` is arbitrary. -/
noncomputable def ProEtale.isTerminalSections_openImmersionRestriction_lowerStar
    (hjk : Set.range j.base ∩ Set.range k.base = ∅)
    (F : Sheaf (Scheme.ProEt.topology U) A) (T : W.ProEt) :
    IsTerminal ((((ProEtale.openImmersionRestriction A k).obj
      ((j)_*[A].obj F))).obj.obj (op T)) :=
  letI := Scheme.ProEt.isEmpty_left_pullback_map j k hjk T
  Scheme.ProEt.isTerminalSectionsOfIsEmpty F
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ k)).obj T))

set_option backward.isDefEq.respectTransparency false in
omit [IsGrothendieckAbelian.{u + 1} A] [IsOpenImmersion j] in
/-- **`k^* j_* F` vanishes.** All its sections are terminal, hence zero. Here `j` is
arbitrary. -/
lemma ProEtale.isZero_openImmersionRestriction_lowerStar
    (hjk : Set.range j.base ∩ Set.range k.base = ∅) (F : Sheaf (Scheme.ProEt.topology U) A) :
    IsZero ((ProEtale.openImmersionRestriction A k).obj ((j)_*[A].obj F)) := by
  refine Sheaf.isZero_of_isZero_obj _ ?_
  rintro ⟨T⟩
  exact IsZero.of_iso (isZero_zero A)
    ((ProEtale.isTerminalSections_openImmersionRestriction_lowerStar A j k hjk F T).uniqueUpToIso
      HasZeroObject.zeroIsTerminal)

set_option backward.isDefEq.respectTransparency false in
/-- **`k^* j_! F` is initial**, proved through Hom-sets rather than through sections: the two
adjunctions turn `Hom(k^* j_! F, H)` into `Hom(F, j^* k_* H)`, and `j^* k_* H` vanishes by
`AlgebraicGeometry.ProEtale.isZero_openImmersionRestriction_lowerStar` with the roles of `j`
and `k` exchanged. -/
noncomputable def ProEtale.isInitial_openImmersionRestriction_openImmersionLowerShriek
    (hjk : Set.range j.base ∩ Set.range k.base = ∅) (F : Sheaf (Scheme.ProEt.topology U) A) :
    IsInitial ((ProEtale.openImmersionRestriction A k).obj ((j)_!open[A].obj F)) := by
  refine IsInitial.ofUnique (h := fun H => ?_)
  haveI : Unique (F ⟶ (ProEtale.openImmersionRestriction A j).obj ((k)_*[A].obj H)) := by
    have hz := ProEtale.isZero_openImmersionRestriction_lowerStar A k j
      (by rw [Set.inter_comm]; exact hjk) H
    exact ⟨⟨hz.isTerminal.from F⟩, fun a => hz.isTerminal.hom_ext _ _⟩
  exact Equiv.unique
    (((ProEtale.openImmersionRestrictionLowerStarAdjunction A k).homEquiv _ H).trans
      ((ProEtale.openImmersionLowerShriekAdjunction A j).homEquiv F _))

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison `j_! ⟶ j_*` restricted to a disjoint open is an isomorphism.** Both sides
are initial, and a morphism out of an initial object is unique, so it agrees with the canonical
isomorphism between the two. -/
lemma ProEtale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar
    (hjk : Set.range j.base ∩ Set.range k.base = ∅) (F : Sheaf (Scheme.ProEt.topology U) A) :
    IsIso ((ProEtale.openImmersionRestriction A k).map
      ((ProEtale.openImmersionLowerShriekToLowerStar A j).app F)) := by
  have hS := ProEtale.isInitial_openImmersionRestriction_openImmersionLowerShriek A j k hjk F
  have hT := (ProEtale.isZero_openImmersionRestriction_lowerStar A j k hjk F).isInitial
  have key : (ProEtale.openImmersionRestriction A k).map
      ((ProEtale.openImmersionLowerShriekToLowerStar A j).app F) = (hS.uniqueUpToIso hT).hom :=
    hS.hom_ext _ _
  rw [key]
  infer_instance

end Disjoint

section DisjointPullback

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U W X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ X)

open ProEtale

/-- **The pullback of `j_! F` along a morphism `g` missing the range of `j` is initial.** The
adjunctions `g^* ⊣ g_*` and `j_! ⊣ j^*` turn `Hom(g^* j_! F, H)` into `Hom(F, j^* g_* H)`,
and `j^* g_* H` vanishes by `AlgebraicGeometry.ProEtale.isZero_openImmersionRestriction_lowerStar`.
-/
noncomputable def ProEtale.isInitial_upperStar_openImmersionLowerShriek
    (hjg : Set.range j.base ∩ Set.range g.base = ∅) (F : Sheaf (Scheme.ProEt.topology U) A) :
    IsInitial ((g)^*[A].obj ((j)_!open[A].obj F)) := by
  refine IsInitial.ofUnique (h := fun H => ?_)
  haveI : Unique (F ⟶ (ProEtale.openImmersionRestriction A j).obj ((g)_*[A].obj H)) := by
    have hz := ProEtale.isZero_openImmersionRestriction_lowerStar A g j
      (by rw [Set.inter_comm]; exact hjg) H
    exact ⟨⟨hz.isTerminal.from F⟩, fun a => hz.isTerminal.hom_ext _ _⟩
  exact Equiv.unique
    (((ProEtale.upperStarLowerStarAdjunction A g).homEquiv _ H).trans
      ((ProEtale.openImmersionLowerShriekAdjunction A j).homEquiv F _))

/-- **The pullback of `j_! F` along a morphism `g` missing the range of `j` vanishes.** -/
lemma ProEtale.isZero_upperStar_openImmersionLowerShriek
    (hjg : Set.range j.base ∩ Set.range g.base = ∅) (F : Sheaf (Scheme.ProEt.topology U) A) :
    IsZero ((g)^*[A].obj ((j)_!open[A].obj F)) :=
  (isZero_zero _).of_iso
    ((ProEtale.isInitial_upperStar_openImmersionLowerShriek A j g hjg F).uniqueUpToIso
      HasZeroObject.zeroIsInitial)

end DisjointPullback

end AlgebraicGeometry
