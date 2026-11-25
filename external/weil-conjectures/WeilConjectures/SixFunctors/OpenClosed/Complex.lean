/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.OpenClosed.Vanishing

/-!
# The open–closed short complex, and its restriction to the open part

Let `j : U ⟶ X` be an open immersion and let `i : Z ⟶ X` be an arbitrary morphism whose range
is disjoint from the range of `j`. For a sheaf `F` on the small étale site of `X` this file
builds the short complex

`j_! j^* F ⟶ F ⟶ i_* i^* F`,

whose first map is the counit of `j_! ⊣ j^*` and whose second map is the unit of `i^* ⊣ i_*`.
Both maps are the components of natural transformations, so the complex is built once and for
all as a complex of endofunctors `j_! j^* ⟶ 𝟭 ⟶ i_* i^*` of the category of sheaves on `X`,
and the complex at `F` is its evaluation at `F`; this is what "naturally in `F`" means.

That it *is* a complex needs no computation: the vanishing `j^* i_* = 0` of
`WeilConjectures.SixFunctors.OpenClosed.Vanishing` makes the whole Hom-set
`Hom(j_! j^* F, i_* i^* F) ≃ Hom(j^* F, j^* i_* i^* F)` a singleton, so the composite and `0`
agree for want of anything else to be.

In the intended application `i` is a closed immersion complementary to `j`, and this short
complex is short exact. That is proved by applying the two exact functors `j^*` and `i^*`, which
jointly reflect isomorphisms, and checking short exactness of the two images. This file proves
the `j^*` half, which is the half that needs no new geometric input: the image complex is

`j^* j_! j^* F ⟶ j^* F ⟶ j^* i_* i^* F`,

whose third term vanishes and whose first map is an isomorphism, the latter because the unit of
`j_! ⊣ j^*` is an isomorphism. The `i^*` half — which does need `i^* i_* ≅ 𝟙` — and the
conclusion are in `WeilConjectures.SixFunctors.OpenClosed.Exact`.

## Main definitions

- `AlgebraicGeometry.Etale.openClosedShortComplex`: the short complex
  `j_! j^* F ⟶ F ⟶ i_* i^* F`.
- `AlgebraicGeometry.Etale.openClosedShortComplexFunctor`: the same as a short complex of
  *endofunctors* `j_! j^* ⟶ 𝟭 ⟶ i_* i^*`, which is the naturality of the construction in `F`;
  the previous one is its evaluation at `F`.

## Main results

- `AlgebraicGeometry.Etale.shortExact_map_upperStar_openClosedShortComplex_open`: the image of
  the short complex under `j^*` is short exact.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

section OpenClosed

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]

open Etale

/-- The unit of `j_! ⊣ j^*` is an isomorphism, in the form of the adjunction
`Etale.openImmersionLowerShriekUpperStarAdjunction` to `Etale.upperStar` rather than to
`Etale.openImmersionRestriction`. -/
instance Etale.isIso_openImmersionLowerShriekUpperStarAdjunction_unit :
    IsIso (Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit := by
  have h : (Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit =
      ((Etale.openImmersionLowerShriekAdjunction A j).ofNatIsoRight
        (Etale.upperStarIsoOpenImmersionRestriction A j).symm).unit := rfl
  rw [h, Adjunction.ofNatIsoRight_unit]
  infer_instance

/-- `j^*` of the counit of `j_! ⊣ j^*` is an isomorphism at every sheaf `G` on `X`. This is
`Etale.isIso_openImmersionRestriction_map_lowerShriekAdjunction_counit` for `Etale.upperStar`
in place of `Etale.openImmersionRestriction`, proved the same way from the triangle identity
`η_{j^* G} ≫ j^*(ε_G) = 𝟙` and the invertibility of the unit `η`. -/
instance Etale.isIso_upperStar_map_openImmersionLowerShriekUpperStarAdjunction_counit
    (G : Sheaf X.smallEtaleTopology A) :
    IsIso ((j)^*[A].map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).counit.app G)) := by
  have h := (Etale.openImmersionLowerShriekUpperStarAdjunction A j).right_triangle_components
    (Y := G)
  rw [← IsIso.inv_eq_of_hom_inv_id h]
  infer_instance

variable (hji : Disjoint (Set.range j.base) (Set.range i.base))

variable (F : Sheaf X.smallEtaleTopology A)

/-- **The open–closed short complex** `j_! j^* F ⟶ F ⟶ i_* i^* F` attached to an open
immersion `j` and a morphism `i` whose range is disjoint from the range of `j`.

The first map is the counit of `j_! ⊣ j^*` at `F` and the second is the unit of `i^* ⊣ i_*` at
`F`. Their composite is zero because `Hom(j_! j^* F, i_* i^* F) ≃ Hom(j^* F, j^* i_* i^* F)` is
a singleton, `j^* i_* i^* F` being zero by
`Etale.isZero_upperStar_lowerStar_of_disjoint_range`.

Both maps are components of natural transformations, so the whole complex is natural in `F`;
that is `Etale.openClosedShortComplexFunctor` below. -/
@[simps]
noncomputable def Etale.openClosedShortComplex :
    ShortComplex (Sheaf X.smallEtaleTopology A) where
  X₁ := (j)_!open[A].obj ((j)^*[A].obj F)
  X₂ := F
  X₃ := (i)_*[A].obj ((i)^*[A].obj F)
  f := (Etale.openImmersionLowerShriekUpperStarAdjunction A j).counit.app F
  g := (Etale.upperStarLowerStarAdjunction A i).unit.app F
  zero := by
    have hz := Etale.isZero_upperStar_lowerStar_of_disjoint_range A j i hji ((i)^*[A].obj F)
    have : Subsingleton ((j)^*[A].obj F ⟶ (j)^*[A].obj ((i)_*[A].obj ((i)^*[A].obj F))) :=
      ⟨fun _ _ ↦ hz.eq_of_tgt _ _⟩
    have : Subsingleton
        ((j)_!open[A].obj ((j)^*[A].obj F) ⟶ (i)_*[A].obj ((i)^*[A].obj F)) :=
      Equiv.subsingleton
        ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).homEquiv _ _)
    exact Subsingleton.elim _ _

/-- **The open–closed short complex, as a complex of endofunctors** `j_! j^* ⟶ 𝟭 ⟶ i_* i^*`,
attached to an open immersion `j` and a morphism `i` whose range is disjoint from the range of
`j`.

The two maps are the counit of `j_! ⊣ j^*` and the unit of `i^* ⊣ i_*` as natural
transformations, so this is `Etale.openClosedShortComplex` made natural in `F`; that it is a
complex is the statement for a fixed `F`, read componentwise. -/
@[simps]
noncomputable def Etale.openClosedShortComplexFunctor :
    ShortComplex (Sheaf X.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A) where
  X₁ := (j)^*[A] ⋙ (j)_!open[A]
  X₂ := 𝟭 _
  X₃ := (i)^*[A] ⋙ (i)_*[A]
  f := (Etale.openImmersionLowerShriekUpperStarAdjunction A j).counit
  g := (Etale.upperStarLowerStarAdjunction A i).unit
  zero := NatTrans.ext (funext fun F ↦ (Etale.openClosedShortComplex A j i hji F).zero)

omit [HasSmallSiteSheafify A] in
/-- The open–closed short complex at `F` is the complex of endofunctors evaluated at `F`; this
is what "naturally in `F`" means. -/
lemma Etale.openClosedShortComplexFunctor_map_evaluation (F : Sheaf X.smallEtaleTopology A) :
    (Etale.openClosedShortComplexFunctor A j i hji).map ((evaluation _ _).obj F) =
      Etale.openClosedShortComplex A j i hji F :=
  rfl

omit [HasSmallSiteSheafify A] in
/-- **The `j^*`-image of the open–closed short complex is short exact**, i.e.

`0 ⟶ j^* j_! j^* F ⟶ j^* F ⟶ j^* i_* i^* F ⟶ 0`

is exact. Its third term is zero by `Etale.isZero_upperStar_lowerStar_of_disjoint_range`, and
its first map is an isomorphism by
`Etale.isIso_upperStar_map_openImmersionLowerShriekUpperStarAdjunction_counit`.

This is one of the two halves of the reflection argument proving that
`Etale.openClosedShortComplex` is itself short exact; it is the half that does not use that `i`
is a closed immersion. The other half is
`Etale.shortExact_map_upperStar_openClosedShortComplex_closed`. -/
lemma Etale.shortExact_map_upperStar_openClosedShortComplex_open :
    ((Etale.openClosedShortComplex A j i hji F).map (j)^*[A]).ShortExact := by
  have hz := Etale.isZero_upperStar_lowerStar_of_disjoint_range A j i hji ((i)^*[A].obj F)
  have : HasZeroObject (Sheaf U.smallEtaleTopology A) := ⟨_, hz⟩
  have hg : ((Etale.openClosedShortComplex A j i hji F).map (j)^*[A]).g = 0 :=
    hz.eq_of_tgt _ _
  have : IsIso ((Etale.openClosedShortComplex A j i hji F).map (j)^*[A]).f :=
    inferInstanceAs (IsIso ((j)^*[A].map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).counit.app F)))
  exact
    { exact := (ShortComplex.exact_iff_epi _ hg).2 inferInstance
      mono_f := inferInstance
      epi_g := ⟨fun _ _ _ ↦ hz.eq_of_src _ _⟩ }

end OpenClosed

end AlgebraicGeometry
