/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import WeilConjectures.SixFunctors.OpenClosed.Points
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!

# The restrictions to an open and to its closed complement jointly reflect isomorphisms

Let `j : U ⟶ X` be an open immersion and `i : Z ⟶ X` a closed immersion whose range is the
complement of the range of `j`. This file shows that the two restrictions `j^*` and `i^*` of
`A`-valued sheaves on the small étale sites see everything: a morphism of sheaves on `X`
which becomes an isomorphism both on `U` and on `Z` is an isomorphism.

The proof evaluates at geometric points. By
`AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map` it suffices to check that the fibre
of the morphism at every geometric point `s : Spec Ω ⟶ X` is invertible. By
`AlgebraicGeometry.existsUnique_fac_or_fac_of_range_eq_compl` such an `s` factors as `t ≫ j`
or as `t ≫ i`, and by `AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso` the fibre at
`t ≫ j` of a morphism is the fibre at `t` of its restriction along `j`, which is invertible
by assumption; likewise for `i`.

## Main results

- `AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_upperStar`: the pair `(j^*, i^*)`
  jointly reflects isomorphisms, as a `CategoryTheory.JointlyReflectIsomorphisms` for the
  two-element family `CategoryTheory.pairFunctor` indexed by `Bool`, with `j^*` at `true`
  and `i^*` at `false` (blueprint: `prop:openclosed-conservative`).
- `AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map`: the same statement in the
  two-hypothesis form, for a human caller.
- `AlgebraicGeometry.Etale.isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map`: the step
  both cases of the proof use, for an arbitrary morphism `f : W ⟶ X`.

## Implementation notes

The two restrictions land in the *different* categories `Sheaf U.smallEtaleTopology A` and
`Sheaf Z.smallEtaleTopology A`, so the family they form is genuinely dependent and cannot be
written with `Matrix.cons`. It is spelled `CategoryTheory.pairFunctor ((j)^*[A]) ((i)^*[A])`,
a family indexed by `Bool` whose target category is `cond b _ _`; see
`WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly`.

Besides the standing assumptions on the coefficient category `A`, the results below need `A`
to be concrete over `Type (u + 1)` in a way compatible with filtered colimits and
sheafification, since that is what
`AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map` asks for. This is not a defect: it
holds for `A = ModuleCat.{u + 1} Λ`, the case the ℓ-adic formalism needs.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)

omit [HasSmallSiteSheafify A] in
/-- The fibre at a geometric point of the form `t ≫ f` of a morphism of étale sheaves whose
restriction along `f` is invertible is invertible: by
`AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso` that fibre is the fibre at `t` of
the restriction `f^* φ`. -/
lemma Etale.isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map {W : Scheme.{u}} (f : W ⟶ X)
    {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G) (hf : IsIso ((f)^*[A].map φ))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ W) :
    IsIso (((pointSmallEtale (t ≫ f)).ulift.{u + 1}).sheafFiber.map φ) := by
  have := hf
  refine (NatIso.isIso_map_iff (Etale.upperStarCompUliftSheafFiberIso A f t) φ).1 ?_
  rw [Functor.comp_map]
  infer_instance

include hij in
omit [HasSmallSiteSheafify A] in
/-- The fibre at a geometric point `s : Spec Ω ⟶ X` of a morphism of étale sheaves whose
restrictions along `j` and along `i` are invertible is invertible: `s` factors through `j` or
through `i` by `AlgebraicGeometry.existsUnique_fac_or_fac_of_range_eq_compl`, and either case
is `AlgebraicGeometry.Etale.isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map`. -/
lemma Etale.isIso_uliftSheafFiber_map_of_isIso_upperStar_map
    {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G)
    (hj : IsIso ((j)^*[A].map φ)) (hi : IsIso ((i)^*[A].map φ))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsIso (((pointSmallEtale s).ulift.{u + 1}).sheafFiber.map φ) := by
  obtain ⟨t, ht, -⟩ | ⟨t, ht, -⟩ := existsUnique_fac_or_fac_of_range_eq_compl j i hij s
  · subst ht
    exact Etale.isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map A j φ hj t
  · subst ht
    exact Etale.isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map A i φ hi t

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hij hJ in
omit [HasSmallSiteSheafify A] in
/-- **The restrictions to an open and to its closed complement jointly reflect
isomorphisms.** For an open immersion `j : U ⟶ X` and a closed immersion `i : Z ⟶ X` whose
range is the complement of the range of `j`, a morphism of `A`-valued sheaves on the small
étale site of `X` which is invertible after restricting to `U` and after restricting to `Z`
is invertible.

The pair `(j^*, i^*)` is spelled as the two-element family
`CategoryTheory.pairFunctor ((j)^*[A]) ((i)^*[A])` indexed by `Bool`, with `j^*` at `true`
and `i^*` at `false`; the two restrictions land in different categories, so the family has to
be dependent. In this bundled form the criteria of
`Mathlib/CategoryTheory/Functor/ReflectsIso/Exact.lean` apply, in particular
`CategoryTheory.JointlyReflectIsomorphisms.shortExact_iff`.
(blueprint: `prop:openclosed-conservative`) -/
theorem Etale.jointlyReflectIsomorphisms_upperStar :
    JointlyReflectIsomorphisms (pairFunctor ((j)^*[A]) ((i)^*[A])) := by
  refine jointlyReflectIsomorphisms_pairFunctor _ _ ?_
  intro F G φ hj hi
  refine Scheme.isIso_of_isIso_sheafFiber_map φ fun x ↦ ?_
  exact Etale.isIso_uliftSheafFiber_map_of_isIso_upperStar_map A j i hij φ hj hi _

include hij hJ in
omit [HasSmallSiteSheafify A] in
/-- A morphism of `A`-valued sheaves on the small étale site of `X` which is invertible after
restricting along the open immersion `j` and after restricting along the complementary closed
immersion `i` is invertible. This is the two-hypothesis form of
`AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_upperStar`.
(blueprint: `prop:openclosed-conservative`) -/
theorem Etale.isIso_of_isIso_upperStar_map {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G)
    (hj : IsIso ((j)^*[A].map φ)) (hi : IsIso ((i)^*[A].map φ)) : IsIso φ :=
  (Etale.jointlyReflectIsomorphisms_upperStar A j i hij).isIso_of_pairFunctor φ hj hi

include hJ in
omit [HasSmallSiteSheafify A] in
/-- **Restrictions along a jointly surjective family reflect isomorphisms.** If `a_i : U_i ⟶ X`
is a family of morphisms whose images cover `X`, a morphism of `A`-valued sheaves on the small
étale site of `X` whose restrictions along all the `a_i` are invertible is invertible: every
point of `X` is the image of a geometric point of some `U_i`, and the fibre of the morphism at
that geometric point is the fibre of its restriction to `U_i`. -/
theorem Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective
    {ι : Type u} {U : ι → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G) (hφ : ∀ i, IsIso ((a i)^*[A].map φ)) :
    IsIso φ := by
  refine (((isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ X
    (Ω := fun j : Σ i, U i ↦ AlgebraicClosure ((U j.1).residueField j.2))
    (fun j ↦ (U j.1).algClosurePoint j.2 ≫ a j.1) ?_).jointlyReflectIsomorphisms A).isIso_iff
      φ).2 ?_
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, y, rfl⟩ := ha x
    exact Set.mem_iUnion.2 ⟨⟨i, y⟩, default, by simp⟩
  rintro ⟨-, ⟨j⟩⟩
  exact Etale.isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map A (a j.1) φ (hφ j.1) _


include hJ in
omit [HasSmallSiteSheafify A] in
/-- **An étale covering detects isomorphisms of sheaves.** Let `a_i : U_i ⟶ X` be a jointly
surjective family of morphisms, for instance an étale covering. A morphism `φ` of `A`-valued
sheaves on the small étale site of `X` is an isomorphism if and only if all its restrictions
`a_i^* φ` are: restriction is a functor, and conversely
`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective` checks `φ` on the
geometric stalks, each of which is a geometric stalk of some `a_i^* φ`.
(blueprint: `lem-weil-pbc-etale-cover-detects-iso`) -/
theorem Etale.isIso_iff_forall_isIso_upperStar_map_of_jointlySurjective
    {ι : Type u} {U : ι → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ i, IsIso ((a i)^*[A].map φ) :=
  ⟨fun _ _ ↦ inferInstance, Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective A a ha φ⟩

end AlgebraicGeometry
