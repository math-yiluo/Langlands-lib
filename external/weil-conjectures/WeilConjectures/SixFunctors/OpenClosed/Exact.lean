/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!

# The open–closed exact sequence

Let `j : U ⟶ X` be an open immersion and `i : Z ⟶ X` a closed immersion whose range is the
complement of the range of `j`. This file shows that the short complex

`0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0`

of `WeilConjectures.SixFunctors.OpenClosed.Complex` is short exact, for every sheaf `F` on the
small étale site of `X`.

This is the excision sequence of étale cohomology; it is classical, see Milne, *Étale
Cohomology*, II.3, or SGA 4. The proof below is organised so that the one step which is not
formal — the stalks of `i_*` — is isolated in
`WeilConjectures.SixFunctors.OpenClosed.Stalk`.

## The argument

The two restrictions `j^*` and `i^*` are exact and jointly reflect isomorphisms
(`AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_upperStar`), so by
`CategoryTheory.JointlyReflectIsomorphisms.shortExact_iff` it suffices to check short exactness
of the two images. In both cases the image complex is a zero object next to an isomorphism:

- over `U` the third term `j^* i_* i^* F` vanishes and the first map is invertible because the
  unit of `j_! ⊣ j^*` is; this is
  `AlgebraicGeometry.Etale.shortExact_map_upperStar_openClosedShortComplex_open`, proved in
  `WeilConjectures.SixFunctors.OpenClosed.Complex`;
- over `Z` the first term `i^* j_! j^* F` vanishes by
  `AlgebraicGeometry.Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range` and the
  second map `i^*(η_F)` is invertible: the triangle identity exhibits it as a section of the
  counit `i^* i_* i^* F ⟶ i^* F`, which is an isomorphism by
  `AlgebraicGeometry.Etale.isIso_upperStarLowerStarAdjunction_counit_app`, that is, by the full
  faithfulness of `i_*`.

Besides the standing assumptions on the coefficient category `A`, the results below need `A` to
be concrete over `Type (u + 1)` in a way compatible with filtered colimits and sheafification.
That hypothesis comes from the two inputs which are proved by evaluating at geometric points,
namely `i^* i_* ≅ 𝟙` and the joint conservativity of `j^*` and `i^*`; it is asked for on the
small étale site of `Z` and on that of `X` respectively. This is not a defect: both hold for
`A = ModuleCat.{u + 1} Λ`, the case the ℓ-adic formalism needs.

## Main results

- `AlgebraicGeometry.Etale.shortExact_map_upperStar_openClosedShortComplex_closed`: the
  `i^*`-image of the open–closed short complex is short exact.
- `AlgebraicGeometry.Etale.shortExact_openClosedShortComplex`: **the open–closed short complex
  is short exact** (blueprint: `thm:openclosed-exact`).

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJZ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJZ in
/-- **`i^*` of the unit of `i^* ⊣ i_*` is an isomorphism** at every sheaf `G` on `X`, for a
closed immersion `i : Z ⟶ X`: the triangle identity `i^*(η_G) ≫ ε_{i^* G} = 𝟙` exhibits it as
the inverse of the counit `ε_{i^* G}`, which is an isomorphism by
`AlgebraicGeometry.Etale.isIso_upperStarLowerStarAdjunction_counit_app`. -/
instance Etale.isIso_upperStar_map_upperStarLowerStarAdjunction_unit
    (G : Sheaf X.smallEtaleTopology A) :
    IsIso ((i)^*[A].map ((Etale.upperStarLowerStarAdjunction A i).unit.app G)) := by
  rw [← IsIso.inv_eq_of_inv_hom_id
    ((Etale.upperStarLowerStarAdjunction A i).left_triangle_components G)]
  infer_instance

variable (hji : Disjoint (Set.range j.base) (Set.range i.base))
  (F : Sheaf X.smallEtaleTopology A)

include hJZ in
omit [HasSmallSiteSheafify A] in
/-- **The `i^*`-image of the open–closed short complex is short exact**, i.e.

`0 ⟶ i^* j_! j^* F ⟶ i^* F ⟶ i^* i_* i^* F ⟶ 0`

is exact. Its first term is zero by
`AlgebraicGeometry.Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range`, and its
second map `i^*(η_F)` is an isomorphism, being the inverse of the counit of `i^* ⊣ i_*` at
`i^* F` by `AlgebraicGeometry.Etale.isIso_upperStar_map_upperStarLowerStarAdjunction_unit`.

This is one of the two halves of the reflection argument proving that
`AlgebraicGeometry.Etale.openClosedShortComplex` is itself short exact; the other half is
`AlgebraicGeometry.Etale.shortExact_map_upperStar_openClosedShortComplex_open`. -/
lemma Etale.shortExact_map_upperStar_openClosedShortComplex_closed :
    ((Etale.openClosedShortComplex A j i hji F).map (i)^*[A]).ShortExact := by
  have hz := Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A j i hji
    ((j)^*[A].obj F)
  have : HasZeroObject (Sheaf Z.smallEtaleTopology A) := ⟨_, hz⟩
  have hf : ((Etale.openClosedShortComplex A j i hji F).map (i)^*[A]).f = 0 :=
    hz.eq_of_src _ _
  have : IsIso ((Etale.openClosedShortComplex A j i hji F).map (i)^*[A]).g :=
    inferInstanceAs (IsIso ((i)^*[A].map
      ((Etale.upperStarLowerStarAdjunction A i).unit.app F)))
  exact
    { exact := (ShortComplex.exact_iff_mono _ hf).2 inferInstance
      mono_f := ⟨fun _ _ _ ↦ hz.eq_of_tgt _ _⟩
      epi_g := inferInstance }

variable [hJX : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJX hJZ in
omit [HasSmallSiteSheafify A] in
/-- **The open–closed short complex is short exact**: for an open immersion `j : U ⟶ X`, a
closed immersion `i : Z ⟶ X` whose range is the complement of the range of `j`, and a sheaf
`F` on the small étale site of `X`, the sequence

`0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0`

is exact. Both restrictions `j^*` and `i^*` are exact and they jointly reflect isomorphisms, so
this follows from
`AlgebraicGeometry.Etale.shortExact_map_upperStar_openClosedShortComplex_open` and
`AlgebraicGeometry.Etale.shortExact_map_upperStar_openClosedShortComplex_closed`.
(blueprint: `thm:openclosed-exact`) -/
theorem Etale.shortExact_openClosedShortComplex
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (Etale.openClosedShortComplex A j i
      (disjoint_range_of_range_eq_compl j i hij) F).ShortExact := by
  rw [(Etale.jointlyReflectIsomorphisms_upperStar A j i hij).shortExact_iff]
  rintro (_ | _)
  · exact Etale.shortExact_map_upperStar_openClosedShortComplex_closed A j i _ F
  · exact Etale.shortExact_map_upperStar_openClosedShortComplex_open A j i _ F

end AlgebraicGeometry
