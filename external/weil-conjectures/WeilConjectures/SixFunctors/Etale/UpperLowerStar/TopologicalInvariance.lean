/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Topological invariance of the small étale topos and of étale cohomology

Let `f : X ⟶ Y` be a universal homeomorphism of schemes. Base change along `f` is an
equivalence of the small étale sites, matching the topologies
(`AlgebraicGeometry.Scheme.Hom.isDenseSubsite_etale`), so it induces an equivalence of the
small étale topoi, and hence an isomorphism on étale cohomology in every degree. This is
[Stacks 03SI].

For arbitrary coefficients the equivalence of topoi is
`AlgebraicGeometry.Etale.sheafEquivalence`, obtained from
`CategoryTheory.Equivalence.sheafCongr`; its functor is the pushforward
`AlgebraicGeometry.Etale.lowerStar`, which is restriction along base change. For
Grothendieck abelian coefficients, where the pullback `AlgebraicGeometry.Etale.upperStar` is
available, the pullback is the quasi-inverse.

Étale cohomology `CategoryTheory.Sheaf.H` is the `Ext`-groups out of the constant sheaf `ℤ`
on the small étale site, so any morphism of schemes `f : X ⟶ Y` induces a comparison map on
étale cohomology (`AlgebraicGeometry.Etale.cohomologyMap`) by pushing an `Ext`-class forward
along the exact functor `f^*` and using the comparison `ℤ_X ≅ f^* ℤ_Y` of constant sheaves
(`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`). For a universal homeomorphism `f^*`
is an equivalence, and the comparison map is an isomorphism.

## Main definitions

- `AlgebraicGeometry.Etale.sheafEquivalence`: the equivalence
  `Sheaf X.smallEtaleTopology A ≌ Sheaf Y.smallEtaleTopology A` for arbitrary coefficients
  `A`; its functor is the pushforward `(f)_*[A]`.
- `AlgebraicGeometry.Etale.upperStarIsoInverse`: the pullback `(f)^*[A]` is the quasi-inverse
  of the pushforward, by uniqueness of left adjoints.
- `AlgebraicGeometry.Etale.cohomologyMap`: the comparison map on étale cohomology
  `H^n(Y_ét, F) →+ H^n(X_ét, f^* F)` along an arbitrary morphism `f`.
- `AlgebraicGeometry.Etale.cohomologyEquiv`: for a universal homeomorphism, the comparison
  map as an additive equivalence `H^n(Y_ét, F) ≃+ H^n(X_ét, f^* F)`.

## Main statements

- `AlgebraicGeometry.Etale.isEquivalence_lowerStar` and
  `AlgebraicGeometry.Etale.isEquivalence_upperStar`: the pushforward and the pullback along a
  universal homeomorphism are equivalences of categories of étale sheaves;
  `AlgebraicGeometry.Etale.isEquivalence_upperStar_of_thickening` is the case of a thickening.
- `AlgebraicGeometry.Etale.cohomologyMap_bijective`: **topological invariance of étale
  cohomology**, [Stacks 03SI]: for a universal homeomorphism the comparison map on étale
  cohomology is bijective.

## Implementation notes

The general-coefficient statement comes first because it needs nothing on `A`: the
pushforward is objectwise restriction along base change, hence literally the functor of
`CategoryTheory.Equivalence.sheafCongr` for the equivalence of sites. The `upperStar`
statements then follow formally, the pullback being a left adjoint of an equivalence.

The comparison map on cohomology is `CategoryTheory.Sheaf.H.mapFunctor` applied to `f^*`
and the constant-sheaf comparison; nothing about universal homeomorphisms enters its
construction. Bijectivity is `CategoryTheory.Sheaf.H.mapFunctor_bijective`. It applies
because `f^*` is an equivalence, hence fully faithful and exact and preserving injective
objects, and because the category of étale sheaves on `Y` has enough injective objects,
being Grothendieck abelian.

`Etale.sheafEquivalence` and `Etale.isEquivalence_lowerStar` depend only on
`AlgebraicGeometry.Scheme.Hom.isEquivalence_etale`, which is why they are stated first, for
arbitrary coefficients. The `upperStar` and cohomology statements additionally need the
instances `CategoryTheory.GrothendieckTopology.hasSheafify_smallEtaleTopology` and
`CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_smallEtaleTopology`, which
are what make `AlgebraicGeometry.Etale.upperStar` and `CategoryTheory.Sheaf.H` available on
the small étale site at all; these come from the hypothesis
`CategoryTheory.HasSmallSiteSheafify A` on the coefficient category and are found by
instance search.

## References

* [Stacks 03SI], Étale Cohomology, Proposition 59.45.4.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian

namespace AlgebraicGeometry.Etale

open Scheme

section General

variable (A : Type u') [Category.{u + 1} A] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [IsUniversalHomeomorphism f]

/-- **Topological invariance of the small étale topos**, [Stacks 03SI]: for a universal
homeomorphism `f : X ⟶ Y`, restriction along base change is an equivalence between the
category of `A`-valued sheaves on the small étale site of `X` and that of `Y`.

This is the sheaf-level form of the equivalence of sites
`AlgebraicGeometry.Scheme.Hom.isDenseSubsite_etale`.
(blueprint: `prop-weil-pbc-universal-homeomorphism-topos`) -/
@[stacks 03SI]
noncomputable def sheafEquivalence :
    Sheaf X.smallEtaleTopology A ≌ Sheaf Y.smallEtaleTopology A :=
  -- instance search does not see through `f.etaleEquivalence.symm.inverse` to `f.Etale`
  have : (f.etaleEquivalence.symm.inverse).IsDenseSubsite
      Y.smallEtaleTopology X.smallEtaleTopology := Scheme.Hom.isDenseSubsite_etale f
  f.etaleEquivalence.symm.sheafCongr X.smallEtaleTopology Y.smallEtaleTopology A

/-- The pushforward along a universal homeomorphism is the functor of
`AlgebraicGeometry.Etale.sheafEquivalence`: both are restriction along the base change
functor `AlgebraicGeometry.Scheme.Hom.Etale`. -/
lemma lowerStar_eq_sheafEquivalence_functor : (f)_*[A] = (sheafEquivalence A f).functor :=
  rfl

/-- **Topological invariance of the small étale topos**, [Stacks 03SI]: the pushforward along
a universal homeomorphism is an equivalence of categories of étale sheaves.
(blueprint: `prop-weil-pbc-universal-homeomorphism-topos`) -/
@[stacks 03SI]
theorem isEquivalence_lowerStar : ((f)_*[A]).IsEquivalence :=
  inferInstanceAs ((sheafEquivalence A f).functor.IsEquivalence)

end General

section GrothendieckAbelian

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

/-- The pullback along a universal homeomorphism is the quasi-inverse of the pushforward, by
uniqueness of left adjoints: `(f)^*[A] ⊣ (f)_*[A]` by
`AlgebraicGeometry.Etale.upperStarLowerStarAdjunction`, and the inverse of an equivalence is
left adjoint to it. -/
noncomputable def upperStarIsoInverse : (f)^*[A] ≅ (sheafEquivalence A f).inverse :=
  (upperStarLowerStarAdjunction A f).leftAdjointUniq (sheafEquivalence A f).symm.toAdjunction

omit [HasSmallSiteSheafify A] in
/-- **Topological invariance of the small étale topos**, [Stacks 03SI]: the pullback along a
universal homeomorphism `f : X ⟶ Y` is an equivalence between the category of `A`-valued
sheaves on the small étale site of `Y` and that of `X`.
(blueprint: `prop-weil-pbc-universal-homeomorphism-topos`) -/
@[stacks 03SI]
theorem isEquivalence_upperStar : ((f)^*[A]).IsEquivalence :=
  Functor.isEquivalence_of_iso (upperStarIsoInverse A f).symm

omit [HasSmallSiteSheafify A] in
/-- Blueprint `lemma-reduction-field`: The etale site of a thickening.

If `i : T₁ ⟶ T₂` is a thickening, that is, a closed immersion which is surjective on points,
then pullback along `i` is an equivalence between the categories of `A`-valued étale sheaves
on `T₂` and on `T₁`. In particular it identifies the étale cohomology of `T₂` and of `T₁`, see
`AlgebraicGeometry.Etale.cohomologyMap_bijective`. -/
@[stacks 03SI]
theorem isEquivalence_upperStar_of_thickening {T₁ T₂ : Scheme.{u}} (i : T₁ ⟶ T₂)
    [IsClosedImmersion i] (hi : Function.Surjective i.base) : ((i)^*[A]).IsEquivalence :=
  have : Surjective i := ⟨hi⟩
  isEquivalence_upperStar A i

end GrothendieckAbelian

section Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)

/-- The comparison map on étale cohomology induced by a morphism of schemes `f : X ⟶ Y`: an
`Ext`-class out of the constant sheaf `ℤ` on the small étale site of `Y` is pushed forward
along the exact functor `f^*` and then precomposed with the comparison `ℤ_X ≅ f^* ℤ_Y` of
constant sheaves of `AlgebraicGeometry.Scheme.upperStarConstantSheafIso`.
(blueprint: `def-weil-pbc-cohomology-pullback`) -/
noncomputable def cohomologyMap :
    Sheaf.H F n →+ Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj F) n :=
  Sheaf.H.mapFunctor _
    ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
      (AddCommGrpCat.of (ULift ℤ))) F n

lemma cohomologyMap_apply (x : Sheaf.H F n) :
    cohomologyMap f F n x =
      (Ext.mk₀ ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
          (AddCommGrpCat.of (ULift ℤ))).hom).comp
        (x.mapExactFunctor ((f)^*[AddCommGrpCat.{u + 1}])) (zero_add n) :=
  rfl

variable {F} in
/-- The comparison map on étale cohomology is natural in the sheaf: the square

```
   H^n(Y_ét, F) ──cohomologyMap f F n──→ H^n(X_ét, f^* F)
        │                                     │
        │ Sheaf.H.map φ n                     │ Sheaf.H.map (f^* φ) n
        ↓                                     ↓
   H^n(Y_ét, G) ──cohomologyMap f G n──→ H^n(X_ét, f^* G)
```

commutes. (blueprint: `proposition-cohomology-p-1-over-henselian--1`, naturality) -/
lemma cohomologyMap_map {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (x : Sheaf.H F n) :
    cohomologyMap f G n (Sheaf.H.map φ n x) =
      Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map φ) n (cohomologyMap f F n x) :=
  Sheaf.H.mapFunctor_map _ _ _ φ x

variable [IsUniversalHomeomorphism f]

attribute [local instance] isEquivalence_upperStar

/-- **Topological invariance of étale cohomology**, [Stacks 03SI]: for a universal
homeomorphism `f : X ⟶ Y` the comparison map `AlgebraicGeometry.Etale.cohomologyMap` on
étale cohomology is bijective in every degree.
(blueprint: `prop-weil-pbc-universal-homeomorphism-topos`) -/
@[stacks 03SI]
theorem cohomologyMap_bijective : Function.Bijective (cohomologyMap f F n) :=
  Sheaf.H.mapFunctor_bijective _ _ F n

/-- **Topological invariance of étale cohomology**, [Stacks 03SI]: for a universal
homeomorphism `f : X ⟶ Y` the pullback induces an isomorphism
`H^n(Y_ét, F) ≃+ H^n(X_ét, f^* F)` in every degree. This is
`AlgebraicGeometry.Etale.cohomologyMap`, which is bijective by
`AlgebraicGeometry.Etale.cohomologyMap_bijective`.
(blueprint: `prop-weil-pbc-universal-homeomorphism-topos`) -/
@[stacks 03SI]
noncomputable def cohomologyEquiv :
    Sheaf.H F n ≃+ Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj F) n :=
  AddEquiv.ofBijective _ (cohomologyMap_bijective f F n)

@[simp]
lemma cohomologyEquiv_apply (x : Sheaf.H F n) :
    cohomologyEquiv f F n x = cohomologyMap f F n x :=
  rfl

end Cohomology

end AlgebraicGeometry.Etale
