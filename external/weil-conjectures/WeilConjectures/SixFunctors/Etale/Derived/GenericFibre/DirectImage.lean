/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Open direct images commute with generic base change

Let `S` be an integral scheme of finite type over a field `k`, let `Λ` be a finite ring whose
exponent is invertible on `S`, and let `t : T ⟶ S` be a morphism from a noetherian scheme `T`
lying over the generic point of `S` — for instance a geometric generic point
`Spec (k(S)^{alg}) ⟶ S`, the case of blueprint `lemma-restriction-geometric-generic-fibre` with
`S = B` a curve. For an open immersion `j : X ⟶ Y` of finite-type `S`-schemes and its base change
`j_T : X_T ⟶ Y_T` along `g : Y_T ⟶ Y`, the derived base change map

`Ex_* : g^* Rj_* L ⟶ Rj_{T,*} g'^* L`

(`AlgebraicGeometry.Etale.derivedBaseChangeMap`) is an isomorphism for every bounded
constructible `L` on `X`.

This is the first comparison of blueprint `lemma-restriction-geometric-generic-fibre`,
`g_X^* Rh_* L ≅ Rh_{η̄,*} g_T^* L`, for `h` an open immersion; it is the case used by the closed
support comparison (`WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport`).

## Implementation notes

The blueprint proves the comparison by writing the separable closure of `k(B)` as a limit of
étale neighbourhoods, applying smooth base change at each stage and passing to the limit. Here it
is instead read off from Deligne's generic base change theorem
(`AlgebraicGeometry.Etale.exists_hasConstructibleDirectImageBaseChangeOn`,
`theorem-generic-constructibility-base-change-rj`): for each constructible sheaf `F` the formation
of `Rj_* F` commutes with every noetherian base change landing in some nonempty open `U ⊆ S`, and
the generic point lies in every such `U`. A dévissage over the cohomology sheaves
(`AlgebraicGeometry.Etale.prop_of_boundedConstructible`) passes from sheaves to bounded
constructible complexes, the locus where `Ex_*` is invertible being a triangulated subcategory
(`CategoryTheory.NatTrans.isoLocus`). In particular no algebraic closedness of the residue field
of `T` is needed.

## Main statements

- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The generic point of an integral scheme lies in every nonempty open subset. -/
lemma genericPoint_mem_of_nonempty {S : Scheme.{u}} [IsIntegral S] (U : S.Opens)
    (hU : (U : Set S).Nonempty) : genericPoint S ∈ U :=
  ((genericPoint_spec S).mem_open_set_iff U.isOpen).2 (by simpa using hU)

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lemma-restriction-geometric-generic-fibre`, first comparison, for an open immersion.

Let `S` be integral and of finite type over a field `k`, let `Λ` be a finite ring whose exponent
is invertible on `S`, and let `t : T ⟶ S` be a morphism from a noetherian scheme lying over the
generic point of `S` (e.g. a geometric generic point). For an open immersion `j : X ⟶ Y` of
finite-type `S`-schemes, with base changes `g : Y_T ⟶ Y`, `g' : X_T ⟶ X` and `j_T : X_T ⟶ Y_T`,
the derived base change map `Ex_* : g^* Rj_* L ⟶ Rj_{T,*} g'^* L` is an isomorphism for every
bounded constructible complex `L` on `X`. This is Deligne's generic base change
(`AlgebraicGeometry.Etale.exists_hasConstructibleDirectImageBaseChangeOn`), followed by a
dévissage over the cohomology sheaves of `L`. -/
theorem isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic {k : Type u} [Field k]
    {S : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] {T : Scheme.{u}} [IsNoetherian T] (t : T ⟶ S)
    (ht : ∀ x, t.base x = genericPoint S) {X Y XT YT : Scheme.{u}} (fY : Y ⟶ S)
    [LocallyOfFiniteType fY] [QuasiCompact fY] (j : X ⟶ Y) [IsOpenImmersion j] {g : YT ⟶ Y}
    {fT : YT ⟶ T} (hY : IsPullback g fT fY t) {g' : XT ⟶ X} {jT : XT ⟶ YT}
    (sq : IsPullback g' jT j g)
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X L) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) := by
  refine prop_of_boundedConstructible
    (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).isoLocus (fun F hF ↦ ?_) hL
  obtain ⟨U, hU, h⟩ := exists_hasConstructibleDirectImageBaseChangeOn Λ aS fY j F
  have hr : Set.range t.base ⊆ (U : Set S) := by
    rintro _ ⟨x, rfl⟩
    rw [ht x]
    exact genericPoint_mem_of_nonempty U hU
  exact (h T t hr YT XT g fT g' jT hY sq).2

end Etale

end AlgebraicGeometry
