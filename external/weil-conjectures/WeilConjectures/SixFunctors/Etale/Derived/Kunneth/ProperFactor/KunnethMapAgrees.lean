/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-!
# The Künneth map with a proper factor

Let `W = X ×_S Y` with projections `q : W ⟶ X` and `r : W ⟶ Y`. The base change map
`M ⊗ᴸ La_X^* Ra_{Y*} F ⟶ Rq_*(Lq^* M ⊗ᴸ Lr^* F)` (`AlgebraicGeometry.Etale.tensorBaseChangeMap`)
is the composite of the derived base change map `La_X^* Ra_{Y*} F ⟶ Rq_* Lr^* F`, of the
symmetry of `⊗ᴸ` and of the projection map of `q`
(`AlgebraicGeometry.Etale.tensorBaseChangeMap_eq_projectionMap`). Hence the Künneth map
`κ_{E,K}` (`AlgebraicGeometry.Etale.kunnethMap`) is the composite of the canonical maps of the
blueprint: the tensor product with a constant complex
(`proposition-open-direct-image-preserves-finite`), proper base change
(`theorem-results-from-etale-theory--1`) and the projection formula for the proper projection
(`proposition-proper-direct-image-constructible-complexes--9`)
(`AlgebraicGeometry.Etale.kunnethMap_eq_of_isPullback`, blueprint
`corollary-open-direct-image-over-field--2`). In particular, over a separably closed field and with
torsion coefficients, `κ_{E,K}` is an isomorphism as soon as one factor is proper
(`corollary-open-direct-image-over-field--2`).

In the blueprint the proper factor is the first one. Here it is the second one, `Y`: with the
conventions of `AlgebraicGeometry.Etale.kunnethMap`, whose canonical factorisation
(`AlgebraicGeometry.Etale.kunnethMap_eq`) runs through the projection map of the first factor,
this avoids composing with the symmetry of `⊗ᴸ` on both sides of `κ_{E,K}`.

## Main statements

- `AlgebraicGeometry.Etale.tensorBaseChangeMap_eq_projectionMap`.
- `AlgebraicGeometry.Etale.kunnethMap_eq_of_isPullback`
(`corollary-open-direct-image-over-field--2`).
- `AlgebraicGeometry.Etale.isIso_kunnethMap_of_isProper_of_hasFiniteCohomologicalDimension`
  (`corollary-open-direct-image-over-field--2`).
- `AlgebraicGeometry.Etale.isIso_kunnethMap_of_isProper`
(`corollary-open-direct-image-over-field--2`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {S X Y W : Scheme.{u}}

/-- Naturality of the tensor comparison of `Lg^*` in the first variable. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_naturality_left {T R : Scheme.{u}} (g : T ⟶ R)
    {K K' : DerivedCategory (Sheaf R.smallEtaleTopology A)} (φ : K ⟶ K')
    (M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    L((g)^*[A]).map (((-⊗ᴸ-(R)[A]).map φ).app M) ≫
        ((leftDerivedUpperStarTensorComparison A g).app K').app M =
      ((leftDerivedUpperStarTensorComparison A g).app K).app M ≫
        ((-⊗ᴸ-(T)[A]).map (L((g)^*[A]).map φ)).app _ :=
  NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A g).naturality φ) M

/-- Naturality of the tensor comparison of `Lg^*` in the second variable. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_naturality_right {T R : Scheme.{u}} (g : T ⟶ R)
    (K : DerivedCategory (Sheaf R.smallEtaleTopology A))
    {M M' : DerivedCategory (Sheaf R.smallEtaleTopology A)} (ψ : M ⟶ M') :
    L((g)^*[A]).map (((-⊗ᴸ-(R)[A]).obj K).map ψ) ≫
        ((leftDerivedUpperStarTensorComparison A g).app K).app M' =
      ((leftDerivedUpperStarTensorComparison A g).app K).app M ≫
        ((-⊗ᴸ-(T)[A]).obj _).map (L((g)^*[A]).map ψ) :=
  ((leftDerivedUpperStarTensorComparison A g).app K).naturality ψ

/-- `AlgebraicGeometry.Etale.map_rightDerivedLowerStarProjectionMap_comp_counit`, with the object
of the counit written with the derived tensor product. -/
@[reassoc]
lemma map_rightDerivedLowerStarProjectionMap_comp_counit' {T R : Scheme.{u}} (g : T ⟶ R)
    (M : DerivedCategory (Sheaf T.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    L((g)^*[A]).map (((rightDerivedLowerStarProjectionMap A g).app M).app L) ≫
        (derivedUpperStarLowerStarAdjunction A g).counit.app
          (((-⊗ᴸ-(T)[A]).obj M).obj (L((g)^*[A]).obj L)) =
      ((leftDerivedUpperStarTensorComparison A g).app (R((g)_*[A]).obj M)).app L ≫
        ((-⊗ᴸ-(T)[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app M)).app
          (L((g)^*[A]).obj L) :=
  map_rightDerivedLowerStarProjectionMap_comp_counit A g M L

/-- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`, written with the derived
tensor product `AlgebraicGeometry.Etale.derivedTensor`. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_comp_derivedTensor {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
    (K M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    ((leftDerivedUpperStarTensorComparison A g₁₂).app K).app M ≫
        ((-⊗ᴸ-(T)[A]).map ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app K)).app _ ≫
        ((-⊗ᴸ-(T)[A]).obj _).map ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app M) =
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (((-⊗ᴸ-(R)[A]).obj K).obj M) ≫
        L((g₁)^*[A]).map (((leftDerivedUpperStarTensorComparison A g₂).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A g₁).app _).app _ := by
  have := leftDerivedUpperStarTensorComparison_comp A g₁ g₂ g₁₂ hg K M
  rw [MonoidalCategory.tensorHom_def] at this
  exact this

omit [Etale.UpperStarPreservesFlat A] in
/-- The composite `L(a ≫ b)^* ≅ ... ≅ L(a' ≫ b')^*` of two composition isomorphisms through a
common composite `c = a ≫ b = a' ≫ b'` does not depend on the choice of the morphism `c`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_inv_app_comp_hom_app_congr {T S S' R : Scheme.{u}} (a : T ⟶ S)
    (b : S ⟶ R) (a' : T ⟶ S') (b' : S' ⟶ R) (c₁ c₂ : T ⟶ R) (h₁ : c₁ = a ≫ b)
    (h₁' : c₁ = a' ≫ b') (h₂ : c₂ = a ≫ b) (h₂' : c₂ = a' ≫ b')
    (K : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A a b c₁ h₁).inv.app K ≫
        (leftDerivedUpperStarComp A a' b' c₁ h₁').hom.app K =
      (leftDerivedUpperStarComp A a b c₂ h₂).inv.app K ≫
        (leftDerivedUpperStarComp A a' b' c₂ h₂').hom.app K := by
  obtain rfl : c₁ = c₂ := h₁.trans h₂.symm
  rfl

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- The tensor comparison of `Lg^*` commutes with the derived braidings:
`Lg^* β_{K, M} ≫ (Lg^* M ⊗ᴸ Lg^* K comparison) = comparison ≫ β_{Lg^* K, Lg^* M}`. -/
@[reassoc]
lemma leftDerivedUpperStar_map_braiding_hom_comp_tensorComparison {T R : Scheme.{u}}
    (g : T ⟶ R) (K M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    L((g)^*[A]).map (β_ K M).hom ≫ ((leftDerivedUpperStarTensorComparison A g).app M).app K =
      ((leftDerivedUpperStarTensorComparison A g).app K).app M ≫
        (β_ (L((g)^*[A]).obj K) (L((g)^*[A]).obj M)).hom :=
  leftDerivedUpperStar_map_braiding_hom_δ A g K M

/-- The base change map for a pushforward tensored with a complex
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`) of a commutative square `q ≫ a_X = r ≫ a_Y` is
the composite

`M ⊗ᴸ La_X^* Ra_{Y*} F ⟶ M ⊗ᴸ Rq_* Lr^* F ≅ Rq_* Lr^* F ⊗ᴸ M ⟶ Rq_*(Lr^* F ⊗ᴸ Lq^* M)
  ≅ Rq_*(Lq^* M ⊗ᴸ Lr^* F)`

of the derived base change map (`AlgebraicGeometry.Etale.derivedBaseChangeMap`), the symmetry
of `⊗ᴸ`, the projection map of `q` (`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`)
and the symmetry again. -/
lemma tensorBaseChangeMap_eq_projectionMap (q : W ⟶ X) (r : W ⟶ Y) (aX : X ⟶ S)
    (aY : Y ⟶ S) (w : q ≫ aX = r ≫ aY) (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (F : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    tensorBaseChangeMap A q r aX aY w M F =
      ((-⊗ᴸ-(X)[A]).obj M).map ((derivedBaseChangeMap A (CommSq.mk w.symm)).app F) ≫
        (β_ M ((R((q)_*[A])).obj ((L((r)^*[A])).obj F))).hom ≫
        ((rightDerivedLowerStarProjectionMap A q).app _).app M ≫
        R((q)_*[A]).map (β_ ((L((q)^*[A])).obj M) ((L((r)^*[A])).obj F)).inv := by
  apply ((derivedUpperStarLowerStarAdjunction A q).homEquiv _ _).symm.injective
  rw [tensorBaseChangeMap, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Functor.id_obj]
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality,
    map_rightDerivedLowerStarProjectionMap_comp_counit'_assoc,
    leftDerivedUpperStar_map_braiding_hom_comp_tensorComparison_assoc,
    leftDerivedUpperStarTensorComparison_naturality_right_assoc]
  congr 1
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map]
  rw [← BraidedCategory.braiding_naturality_right_assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [← MonoidalCategory.whiskerLeft_comp]
  congr 1
  rw [derivedUpperStar_map_derivedBaseChangeMap_app_counit, derivedSquareUpperStarIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    leftDerivedUpperStarComp_inv_app_comp_hom_app_congr_assoc A q aX r aY (q ≫ aX) (r ≫ aY)
      rfl w w.symm rfl]

/-- Blueprint `corollary-open-direct-image-over-field--2`: the Künneth map is the composite of the
canonical maps.

For a commutative square `q ≫ a_X = r ≫ a_Y = c` (with `q : W ⟶ X`, `r : W ⟶ Y`), the Künneth map
`κ_{E,K} : Ra_{X*} E ⊗ᴸ Ra_{Y*} K ⟶ Rc_*(Lq^* E ⊗ᴸ Lr^* K)` is the composite of

* the projection map `Ra_{X*} E ⊗ᴸ Ra_{Y*} K ⟶ Ra_{X*}(E ⊗ᴸ La_X^* Ra_{Y*} K)` (the tensor product
  with a constant complex, `proposition-open-direct-image-preserves-finite`, over a separably closed
  field);
* `Ra_{X*}` of `E ⊗ᴸ` the derived base change map `La_X^* Ra_{Y*} K ⟶ Rq_* Lr^* K` (proper base
  change, `theorem-results-from-etale-theory--1`, if `a_Y` is proper);
* `Ra_{X*}` of the projection map `E ⊗ᴸ Rq_* Lr^* K ⟶ Rq_*(Lq^* E ⊗ᴸ Lr^* K)` of `q`, up to the
  symmetry of `⊗ᴸ` (the projection formula
  `proposition-proper-direct-image-constructible-complexes--9`, if `q` is proper);
* the composition isomorphism `Ra_{X*} Rq_* ≅ Rc_*` (the Leray isomorphism).

This is the statement `θ ∘ κ_{E,K} = id` of the blueprint, written as `κ_{E,K} = θ⁻¹`, with the
roles of the two factors exchanged (the proper factor is `Y`). -/
lemma kunnethMap_eq_of_isPullback (q : W ⟶ X) (r : W ⟶ Y) (aX : X ⟶ S) (aY : Y ⟶ S)
    (c : W ⟶ S) (hq : q ≫ aX = c) (hr : r ≫ aY = c)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    kunnethMap A q r aX aY c hq hr E K =
      ((rightDerivedLowerStarProjectionMap A aX).app E).app (R((aY)_*[A]).obj K) ≫
        R((aX)_*[A]).map
          (((-⊗ᴸ-(X)[A]).obj E).map
              ((derivedBaseChangeMap A (CommSq.mk (hr.trans hq.symm))).app K) ≫
            (β_ E ((R((q)_*[A])).obj ((L((r)^*[A])).obj K))).hom ≫
            ((rightDerivedLowerStarProjectionMap A q).app _).app E ≫
            R((q)_*[A]).map (β_ ((L((q)^*[A])).obj E) ((L((r)^*[A])).obj K)).inv) ≫
        (rightDerivedLowerStarCompIsoOfComp A q aX c hq).hom.app _ := by
  rw [kunnethMap_eq, tensorBaseChangeMap_eq_projectionMap]
  rfl

/-- The Künneth map is an isomorphism as soon as the projection map of `a_X`, the derived base
change map of the square and the projection map of `q` are isomorphisms
(`AlgebraicGeometry.Etale.kunnethMap_eq_of_isPullback`). -/
lemma isIso_kunnethMap_of_isIso (q : W ⟶ X) (r : W ⟶ Y) (aX : X ⟶ S) (aY : Y ⟶ S)
    (c : W ⟶ S) (hq : q ≫ aX = c) (hr : r ≫ aY = c)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h₁ : IsIso (((rightDerivedLowerStarProjectionMap A aX).app E).app (R((aY)_*[A]).obj K)))
    (h₂ : IsIso ((derivedBaseChangeMap A (CommSq.mk (hr.trans hq.symm))).app K))
    (h₃ : IsIso (((rightDerivedLowerStarProjectionMap A q).app
      ((L((r)^*[A])).obj K)).app E)) :
    IsIso (kunnethMap A q r aX aY c hq hr E K) := by
  rw [kunnethMap_eq_of_isPullback]
  infer_instance

end General

section Point

variable (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

/-- Blueprint `corollary-open-direct-image-over-field--2`: the Künneth formula with one proper
factor, for torsion coefficients.

Let `k` be a separably closed field, `Λ` a ring which is torsion as an additive group, `Y` a
proper `k`-scheme and `X` a quasi-compact quasi-separated `k`-scheme of finite cohomological
dimension. For the cartesian square `W = X ×_k Y` with projections `q`, `r`, and all
`E ∈ D(X_ét, Λ)`, `K ∈ D(Y_ét, Λ)` (unbounded), the Künneth map

`κ_{E,K} : Ra_{X*} E ⊗ᴸ Ra_{Y*} K ⟶ Rc_*(Lq^* E ⊗ᴸ Lr^* K)`

of `AlgebraicGeometry.Etale.kunnethMap` is an isomorphism in `D((Spec k)_ét, Λ)` (which is
`D(Λ)` through `RΓ(Spec k, -)`).

The blueprint works with `ℤ`-coefficients, `E ∈ D⁺(X_ét)` with torsion cohomology and
`K ∈ D⁺(Y_ét)`, where the tensor product with a constant complex
(`corollary-open-direct-image-over-field--2`) and the projection formula
(`corollary-open-direct-image-over-field--2`) hold for bounded below complexes. Here the coefficient
category is `ModuleCat Λ` for a torsion ring `Λ`; the inputs are then available on the unbounded
derived categories (`proposition-open-direct-image-preserves-finite`,
`theorem-results-from-etale-theory--1`,
`proposition-proper-direct-image-constructible-complexes--9`), at the price of the finite
cohomological dimension of `X`. As explained in the module docstring, the proper factor is the
second one. -/
theorem isIso_kunnethMap_of_isProper_of_hasFiniteCohomologicalDimension
    (hΛ : IsAddTorsion Λ) {X Y W : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : HasFiniteCohomologicalDimension Λ X)
    [IsProper aY] (q : W ⟶ X) (r : W ⟶ Y) (sq : IsPullback q r aX aY)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (kunnethMap (ModuleCat.{u + 1} Λ) q r aX aY (q ≫ aX) rfl sq.w.symm E K) := by
  have : IsProper q := MorphismProperty.of_isPullback (P := @IsProper) sq.flip inferInstance
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ hΛ sq.flip
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper Λ hΛ q
  exact isIso_kunnethMap_of_isIso _ q r aX aY _ rfl sq.w.symm E K
    (isIso_rightDerivedLowerStarProjectionMap_of_isSepClosed Λ aX hX E _) inferInstance
    inferInstance

/-- Blueprint `corollary-open-direct-image-over-field--2` (isomorphism statement): over a separably
closed field `k`, with torsion coefficients `Λ`, the Künneth map of `X ×_k Y` for `X` of finite type
and `Y` proper over `k` is an isomorphism, for all `E ∈ D(X_ét, Λ)`, `K ∈ D(Y_ét, Λ)` (unbounded).
It is the composite of the canonical isomorphisms of
`AlgebraicGeometry.Etale.kunnethMap_eq_of_isPullback`. -/
theorem isIso_kunnethMap_of_isProper (hΛ : IsAddTorsion Λ) {X Y W : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsProper aY] (q : W ⟶ X) (r : W ⟶ Y) (sq : IsPullback q r aX aY)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (kunnethMap (ModuleCat.{u + 1} Λ) q r aX aY (q ≫ aX) rfl sq.w.symm E K) :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  isIso_kunnethMap_of_isProper_of_hasFiniteCohomologicalDimension Λ hΛ aX aY
    (hasFiniteCohomologicalDimension_of_isSepClosed Λ hΛ aX) q r sq E K

end Point

end Etale

end AlgebraicGeometry
