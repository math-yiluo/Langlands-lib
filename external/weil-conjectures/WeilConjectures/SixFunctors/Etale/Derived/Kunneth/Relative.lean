/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap

/-!

# The relative product theorem on the étale site

The ordinary Künneth formula with an identity factor, the relative product theorem for `Rf_!`
and its variants for complexes supported on closed subschemes, for the external product
`AlgebraicGeometry.Etale.externalProduct`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`
  (`lemma-kunneth-one-identity-factor--1`): `Rf_* M ⊠ Q ≅ R(f × id_Z)_* (M ⊠ Q)`
  over a field, for a finite coefficient ring of invertible exponent.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`
  (`lemma-kunneth-formula-compact-supports`): `R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M`.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_externalProduct`:
  `L(i ×_B j)^* (K ⊠ L) ≅ Li^* K ⊠ Lj^* L`.
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_closedImmersion`:
  `(i ×_B j)_* (i ×_B j)^* (K ⊠ L) ≅ i_* i^* K ⊠ j_* j^* L` for closed immersions `i`, `j`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion`
  (`lemma-kunneth-formula-compact-supports`): the relative product theorem for complexes supported
  on closed subschemes.
- `AlgebraicGeometry.Etale.nonempty_iso_compactlySupported_externalProduct_closedImmersion`
  (`lemma-kunneth-formula-compact-supports`): the Künneth formula for `RΓ_c(Z × W, -)` over a field.

See `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` for the implementation notes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {B X Y : Scheme.{u}}

/-- The square
```
  X ×_B Z --f × 𝟙--> Y ×_B Z
     |                  |
    pr                 pr
     v                  v
     X -------f-------> Y
```
is cartesian. -/
lemma isPullback_mapOverBaseRight_fst {Z : Scheme.{u}} (b : Y ⟶ B) (c : Z ⟶ B) (f : X ⟶ Y) :
    IsPullback (pullback.mapOverBaseRight f b c) (pullback.fst (f ≫ b) c) (pullback.fst b c)
      f :=
  .of_right (h₁₂ := pullback.snd b c) (h₂₂ := b) (v₁₃ := c)
    (by simpa using (IsPullback.of_hasPullback (f ≫ b) c).flip)
    (pullback.mapOverBaseRight_fst f b c) (IsPullback.of_hasPullback b c).flip

/-- The comparison map `Rf_* M ⊠ Q ⟶ R(f × 𝟙_Z)_* (M ⊠ Q)` of the ordinary Künneth formula
with an identity factor (`lemma-kunneth-one-identity-factor--1`), for
`f : X ⟶ Y`, `b : Y ⟶ B`, `c : Z ⟶ B`, `M ∈ D(X_ét)` and `Q ∈ D(Z_ét)`.

Writing `p_Y, p'_Z` for the projections of `Y ×_B Z` and `p_X, p_Z` for those of `X ×_B Z`,
it is the composite

`p_Y^* Rf_* M ⊗ᴸ p'_Z^* Q ≅ p'_Z^* Q ⊗ᴸ p_Y^* Rf_* M
  ⟶ R(f × 𝟙)_* ((f × 𝟙)^* p'_Z^* Q ⊗ᴸ p_X^* M) ≅ R(f × 𝟙)_* (p_X^* M ⊗ᴸ p_Z^* Q)`

of the braiding of `⊗ᴸ` (`AlgebraicGeometry.Etale.derivedTensorBraiding`),
the base change map `AlgebraicGeometry.Etale.tensorBaseChangeMap` of
`lemma-kunneth-field-coefficients--1` for the cartesian square
`AlgebraicGeometry.Etale.isPullback_mapOverBaseRight_fst`, and the composition isomorphism
`(f × 𝟙)^* p'_Z^* ≅ p_Z^*` followed by the braiding again. -/
noncomputable def externalProductRightDerivedLowerStarMap [UpperStarPreservesFlat A]
    {Z : Scheme.{u}} (b : Y ⟶ B) (c : Z ⟶ B) (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    externalProduct A b c ((R((f)_*[A])).obj M) Q ⟶
      (R((pullback.mapOverBaseRight f b c)_*[A])).obj (externalProduct A (f ≫ b) c M Q) :=
  ((derivedTensorBraiding A (pullback b c)).hom.app _).app _ ≫
    tensorBaseChangeMap A (pullback.mapOverBaseRight f b c) (pullback.fst (f ≫ b) c)
      (pullback.fst b c) f (isPullback_mapOverBaseRight_fst b c f).w
      ((L((pullback.snd b c)^*[A])).obj Q) M ≫
    (R((pullback.mapOverBaseRight f b c)_*[A])).map
      (((derivedTensor A (pullback (f ≫ b) c)).map
          ((leftDerivedUpperStarComp A (pullback.mapOverBaseRight f b c) (pullback.snd b c)
            (pullback.snd (f ≫ b) c) (by simp)).inv.app Q)).app _ ≫
        ((derivedTensorBraiding A (pullback (f ≫ b) c)).hom.app _).app _)

/-- The comparison map `Rf_* M ⊠ Q ⟶ R(f × 𝟙_Z)_* (M ⊠ Q)` is an isomorphism as soon as the
base change map of `lemma-kunneth-field-coefficients--1` it is built from is one. -/
lemma isIso_externalProductRightDerivedLowerStarMap [UpperStarPreservesFlat A]
    {Z : Scheme.{u}} (b : Y ⟶ B) (c : Z ⟶ B) (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    [IsIso (tensorBaseChangeMap A (pullback.mapOverBaseRight f b c) (pullback.fst (f ≫ b) c)
      (pullback.fst b c) f (isPullback_mapOverBaseRight_fst b c f).w
      ((L((pullback.snd b c)^*[A])).obj Q) M)] :
    IsIso (externalProductRightDerivedLowerStarMap A b c f M Q) := by
  rw [externalProductRightDerivedLowerStarMap]
  infer_instance

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- Blueprint `lemma-kunneth-one-identity-factor--1` (detailed node
`lemma-kunneth-one-identity-factor--1`): Ordinary Künneth with an identity factor.

Let `k` be a field, `Λ` a finite coefficient ring whose exponent is invertible in `k` (for
instance the finite stage `A_{E,n}`), and let `f : X ⟶ Y` be a morphism of separated
finite-type `k`-schemes, where `Y` has structure morphism `b` and `X` is viewed over `k`
through `f ≫ b`. Let `c : Z ⟶ Spec k` be a further separated finite-type `k`-scheme, so that
`f` induces `f × 𝟙_Z` across the square

```
  X ×_k Z --f × 𝟙--> Y ×_k Z --pr--> Y
     |                  |            |
     |                  |            f
     v                  v            v
     Z ------c------> Spec k <--b--- Y
```

For `M` in `Dctf(X, Λ)` and `Q` in `Dctf(Z, Λ)` the canonical comparison

`Rf_* M ⊠ Q ⟶ R(f × id_Z)_* (M ⊠ Q)`

is an isomorphism. Here both external products are taken over `Spec k`. The hypotheses that `M`
and `Q` lie in `Dctf` are those of the blueprint; the proof (through
`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`) does not use them.

The base has to be a field and the exponent of `Λ` invertible: over the base `𝔸¹_k`, with
`Z` the origin and `f` the inclusion of `𝔾_m`, the right-hand side vanishes while the
left-hand side is the stalk of `Rf_* Λ` at the origin; and for `Λ = 𝔽_p` in characteristic
`p` the Artin–Schreier cohomology of the affine line already defeats the formula. -/
theorem nonempty_iso_externalProduct_rightDerivedLowerStar (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {Z : Scheme.{u}}
    (b : Y ⟶ Spec (.of k)) (c : Z ⟶ Spec (.of k)) (f : X ⟶ Y)
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (_hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M)
    (_hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z Q) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) b c
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj M) Q ≅
      (R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ])).obj
        (externalProduct (ModuleCat.{u + 1} Λ) (f ≫ b) c M Q)) := by
  have := isIso_tensorBaseChangeMap Λ c b (f ≫ b) (pullback.snd b c) (pullback.fst b c)
    (pullback.mapOverBaseRight f b c) (pullback.fst (f ≫ b) c) f rfl
    (IsPullback.of_hasPullback b c).flip (isPullback_mapOverBaseRight_fst b c f) Q M
  have := isIso_externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} Λ) b c f M Q
  exact ⟨asIso (externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} Λ) b c f M Q)⟩

/-- Blueprint `lemma-kunneth-one-identity-factor--1`: Ordinary Kunneth for a general morphism.

The detailed form of `lemma-kunneth-one-identity-factor--1`, at a finite coefficient ring `A` whose
exponent is invertible in `k` (such as `A_{E,n}`): for a morphism `f : X ⟶ Y` of separated
finite-type `k`-schemes, an auxiliary separated finite-type `k`-scheme `Z`, `L ∈ Dctf(X, A)` and
`Q ∈ Dctf(Z, A)`, the canonical comparison `Rf_* L ⊠ Q ⟶ R(f × id_Z)_* (L ⊠ Q)`
(`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarMap`) is an isomorphism. It is the
composite of the base-change map along `Y ×_k Z ⟶ Y`, an isomorphism by
`lemma-kunneth-field-coefficients--1` (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`), and of
the projection map of `R(f × id_Z)_*`. -/
theorem isIso_externalProductRightDerivedLowerStarMap_of_finite (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {Z : Scheme.{u}}
    (b : Y ⟶ Spec (.of k)) (c : Z ⟶ Spec (.of k)) (f : X ⟶ Y)
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X L)
    (_hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z Q) :
    IsIso (externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} Λ) b c f L Q) := by
  have := isIso_tensorBaseChangeMap Λ c b (f ≫ b) (pullback.snd b c) (pullback.fst b c)
    (pullback.mapOverBaseRight f b c) (pullback.fst (f ≫ b) c) f rfl
    (IsPullback.of_hasPullback b c).flip (isPullback_mapOverBaseRight_fst b c f) Q L
  exact isIso_externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} Λ) b c f L Q

omit [HasSmallSiteSheafify A] in
/-- The assembly step of the ordinary Künneth formula with an identity factor for a morphism
`p : X ⟶ Y` with base change `p' = p × 𝟙_Z : X ×_S Z ⟶ Y ×_S Z`: base change along the
projection `Y ×_S Z ⟶ Y` and the projection formula for `p'` give
`Rp_* M ⊠ Q ≅ Rp'_* (M ⊠ Q)`. -/
theorem nonempty_iso_externalProduct_rightDerivedLowerStar_of_iso [UpperStarPreservesFlat A]
    {S Z : Scheme.{u}} (b : Y ⟶ S) (c : Z ⟶ S) (p : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (e : (L((pullback.fst b c)^*[A])).obj ((R((p)_*[A])).obj M) ≅
      (R((pullback.mapOverBaseRight p b c)_*[A])).obj
        ((L((pullback.fst (p ≫ b) c)^*[A])).obj M))
    (hpf : IsIso (((rightDerivedLowerStarProjectionMap A (pullback.mapOverBaseRight p b c)).app
      ((L((pullback.fst (p ≫ b) c)^*[A])).obj M)).app ((L((pullback.snd b c)^*[A])).obj Q))) :
    Nonempty (externalProduct A b c ((R((p)_*[A])).obj M) Q ≅
      (R((pullback.mapOverBaseRight p b c)_*[A])).obj (externalProduct A (p ≫ b) c M Q)) := by
  let e' : (L((pullback.mapOverBaseRight p b c)^*[A])).obj ((L((pullback.snd b c)^*[A])).obj Q) ≅
      (L((pullback.snd (p ≫ b) c)^*[A])).obj Q :=
    ((leftDerivedUpperStarComp A (pullback.mapOverBaseRight p b c) (pullback.snd b c)
      (pullback.snd (p ≫ b) c) (by simp)).app Q).symm
  exact ⟨((derivedTensor A _).mapIso e).app _ ≪≫ asIso (((rightDerivedLowerStarProjectionMap A
    (pullback.mapOverBaseRight p b c)).app ((L((pullback.fst (p ≫ b) c)^*[A])).obj M)).app
      ((L((pullback.snd b c)^*[A])).obj Q)) ≪≫
    (R((pullback.mapOverBaseRight p b c)_*[A])).mapIso (((derivedTensor A _).obj _).mapIso e')⟩

/-- The ordinary Künneth formula with an identity factor `lemma-kunneth-one-identity-factor--1` for
a
*proper* morphism `p : X ⟶ Y` and a finite coefficient ring: `Rp_* M ⊠ Q ≅ R(p × 𝟙_Z)_* (M ⊠ Q)`
for all `M` and `Q`, by proper base change
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`) and the
projection formula for the proper morphism `p × 𝟙_Z`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`). For a
compactification `f = g ∘ j` of a general `f` this handles the proper factor `g`; the open
factor `j` is the non-formal part of
`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`. -/
theorem nonempty_iso_externalProduct_rightDerivedLowerStar_of_isProper (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {S Z : Scheme.{u}} (b : Y ⟶ S) (c : Z ⟶ S) (p : X ⟶ Y) [IsProper p]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) b c
        ((R((p)_*[ModuleCat.{u + 1} Λ])).obj M) Q ≅
      (R((pullback.mapOverBaseRight p b c)_*[ModuleCat.{u + 1} Λ])).obj
        (externalProduct (ModuleCat.{u + 1} Λ) (p ≫ b) c M Q)) := by
  have sq : IsPullback (pullback.fst (p ≫ b) c) (pullback.mapOverBaseRight p b c) p
      (pullback.fst b c) := isPullback_pullbackMapLeft b c p
  have : IsProper (pullback.mapOverBaseRight p b c) :=
    MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ (pullback.mapOverBaseRight p b c)
  exact nonempty_iso_externalProduct_rightDerivedLowerStar_of_iso (ModuleCat.{u + 1} Λ) b c p M Q
    ((asIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq)).app M) inferInstance

omit [HasSmallSiteSheafify A] in
/-- The assembly step of the relative product theorem `lemma-kunneth-formula-compact-supports`: with
`p`, `q` the projections of `X ×_B Y`, a composition isomorphism
`R(f ×_B g)_! ≅ Rq_! ⋙ Rg_!`, the projection formula for `q` at `(Lp^*K, M)`, compact-support
base change `Lg^* Rf_! K ≅ Rq_! Lp^* K` and the projection formula for `g` at `(M, Rf_! K)` give
`R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M`. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct_of_iso [UpperStarPreservesFlat A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f] [HasCompactification g]
    [HasCompactification (pullback.toBase f g)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (e₁ : R(pullback.toBase f g)_![A] ≅ R(pullback.snd f g)_![A] ⋙ R(g)_![A])
    (h₂ : HasProjectionFormula A (pullback.snd f g)
      ((L((pullback.fst f g)^*[A])).obj K) M)
    (e₃ : (L((g)^*[A])).obj ((R(f)_![A]).obj K) ≅
      (R(pullback.snd f g)_![A]).obj ((L((pullback.fst f g)^*[A])).obj K))
    (h₄ : HasProjectionFormula A g M ((R(f)_![A]).obj K)) :
    Nonempty ((R(pullback.toBase f g)_![A]).obj (externalProduct A f g K M) ≅
      ((-⊗ᴸ-(B)[A]).obj ((R(f)_![A]).obj K)).obj ((R(g)_![A]).obj M)) := by
  have : IsIso (((projectionMap A (pullback.snd f g)).app
    ((L((pullback.fst f g)^*[A])).obj K)).app M) := h₂
  have : IsIso (((projectionMap A g).app M).app ((R(f)_![A]).obj K)) := h₄
  obtain ⟨βY⟩ := nonempty_iso_derivedTensor_flip A Y
  obtain ⟨βB⟩ := nonempty_iso_derivedTensor_flip A B
  exact ⟨e₁.app _ ≪≫ (R(g)_![A]).mapIso
    ((asIso (((projectionMap A (pullback.snd f g)).app
      ((L((pullback.fst f g)^*[A])).obj K)).app M)).symm ≪≫
    ((-⊗ᴸ-(Y)[A]).mapIso e₃.symm).app M ≪≫ (βY.app _).app M) ≪≫
    (asIso (((projectionMap A g).app M).app ((R(f)_![A]).obj K))).symm ≪≫ (βB.app _).app _⟩

/-- The relative product theorem `lemma-kunneth-formula-compact-supports` for a finite coefficient
ring: `R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M` for every `K` and `M`. This is the case of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` with
coefficients `ModuleCat Λ`, by the four steps of the blueprint proof: the composition law for
`f ×_B g = q ≫ g`, the projection formula for `q`, compact-support base change for the
cartesian square of `f` and `g`, and the projection formula for `g`. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct_of_finite (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f]
    [HasCompactification g] [QuasiCompact f] [QuasiCompact g]
    [HasCompactification (pullback.toBase f g)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(pullback.toBase f g)_![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) f g K M) ≅
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj M)) := by
  have sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have : QuasiCompact (pullback.snd f g) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have hcomp : ∀ (t : pullback f g ⟶ B) [HasCompactification t], pullback.snd f g ≫ g = t →
      Nonempty (R(t)_![ModuleCat.{u + 1} Λ] ≅
        R(pullback.snd f g)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ]) := by
    rintro t _ rfl
    exact nonempty_iso_rightDerivedLowerShriek_comp Λ (pullback.snd f g) g
  obtain ⟨e₁⟩ := hcomp (pullback.toBase f g) (by simp)
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  exact nonempty_iso_rightDerivedLowerShriek_externalProduct_of_iso (ModuleCat.{u + 1} Λ) f g K M e₁
    (hasProjectionFormula_of_finite Λ _ _ _)
    ((asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).app K)
    (hasProjectionFormula_of_finite Λ _ _ _)

/-- Blueprint `lemma-kunneth-formula-compact-supports`: Relative product theorem.

Let `Λ` be a finite coefficient ring (for instance the finite stage `A_{E,n}`), let
`f : X ⟶ B` and `g : Y ⟶ B` be separated of finite type over a base scheme `B`, and let `K` be
in `Dctf(X, Λ)` and `M` in `Dctf(Y, Λ)`. Writing `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M` for the external
product over `B` and `f ×_B g : X ×_B Y ⟶ B` for the structure morphism
`CategoryTheory.Limits.pullback.toBase` of the fibre product, there is an isomorphism

`R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M`

in `D(B_ét)`. The canonical isomorphism, an explicit composite of the composition law, the
projection formula, compact-support base change and the symmetry of `⊗ᴸ`, is
`AlgebraicGeometry.Etale.relativeKunnethIso`. The coefficients are torsion: with coefficients
`ℤ` the statement fails, proper base change failing for a regular proper curve over a strictly
henselian discrete valuation ring with nodal special fibre. The `Dctf` hypotheses are those of
the blueprint; for a finite coefficient ring the isomorphism exists for all `K` and `M`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct_of_finite`). -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] (f : X ⟶ B) (g : Y ⟶ B)
    [HasCompactification f] [HasCompactification g] [QuasiCompact f] [QuasiCompact g]
    [HasCompactification (pullback.toBase f g)]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (_hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (_hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y M) :
    Nonempty ((R(pullback.toBase f g)_![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) f g K M) ≅
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj M)) :=
  ⟨relativeKunnethIso Λ f g K M⟩

omit [HasSmallSiteSheafify A] in
/-- The external product is compatible with pullback: for morphisms `i : Z ⟶ X`, `j : W ⟶ Y`
over `B`, with product `i ×_B j : Z ×_B W ⟶ X ×_B Y`,

`L(i ×_B j)^* (K ⊠ L) ≅ Li^* K ⊠ Lj^* L`,

the external product on the right being taken along `i ≫ f` and `j ≫ g`. The pullbacks are
assumed to preserve flat sheaves (`AlgebraicGeometry.Etale.UpperStarPreservesFlat`, true for
`ModuleCat Λ`), which is what makes the derived pullback monoidal
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso`). -/
theorem nonempty_iso_leftDerivedUpperStar_externalProduct [UpperStarPreservesFlat A]
    (f : X ⟶ B) (g : Y ⟶ B) {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Nonempty ((L((pullback.mapOverBase i j f g)^*[A])).obj (externalProduct A f g K L) ≅
      externalProduct A (i ≫ f) (j ≫ g) ((L((i)^*[A])).obj K) ((L((j)^*[A])).obj L)) := by
  -- `K ⊠ L = Lp^* K ⊗ᴸ Lq^* L`; the derived pullback is monoidal, and
  -- `p ∘ (i ×_B j) = i ∘ p'`, `q ∘ (i ×_B j) = j ∘ q'` for the projections `p'`, `q'` of
  -- `Z ×_B W`.
  let e : pullback (i ≫ f) (j ≫ g) ⟶ pullback f g := pullback.mapOverBase i j f g
  let pb₁ : (L((e)^*[A])).obj ((L((pullback.fst f g)^*[A])).obj K) ≅
      (L((pullback.fst (i ≫ f) (j ≫ g))^*[A])).obj ((L((i)^*[A])).obj K) :=
    ((leftDerivedUpperStarComp A e (pullback.fst _ _)).app K).symm ≪≫
      (leftDerivedUpperStarComp A _ _ (e ≫ pullback.fst _ _) (by simp [e])).app K
  let pb₂ : (L((e)^*[A])).obj ((L((pullback.snd f g)^*[A])).obj L) ≅
      (L((pullback.snd (i ≫ f) (j ≫ g))^*[A])).obj ((L((j)^*[A])).obj L) :=
    ((leftDerivedUpperStarComp A e (pullback.snd _ _)).app L).symm ≪≫
      (leftDerivedUpperStarComp A _ _ (e ≫ pullback.snd _ _) (by simp [e])).app L
  exact ⟨leftDerivedUpperStarTensorIso A e _ _ ≪≫ ((derivedTensor A _).mapIso pb₁).app _ ≪≫
    ((derivedTensor A _).obj _).mapIso pb₂⟩

omit [HasSmallSiteSheafify A] in
/-- The external product is compatible with restriction to closed subschemes: for closed
immersions `i : Z ⟶ X`, `j : W ⟶ Y` over `B`, with product `i ×_B j : Z ×_B W ⟶ X ×_B Y`,

`(i ×_B j)_* (i ×_B j)^* (K ⊠ L) ≅ i_* i^* K ⊠ j_* j^* L`.

The pullbacks are assumed to preserve flat sheaves
(`AlgebraicGeometry.Etale.UpperStarPreservesFlat`, true for `ModuleCat Λ`), which makes the
derived pullback monoidal. This is
`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_closedImmersion_of_flat`: both sides are
supported on `Z ×_B W` and agree there. -/
theorem nonempty_iso_externalProduct_closedImmersion [UpperStarPreservesFlat A]
    (f : X ⟶ B) (g : Y ⟶ B)
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Nonempty ((R((pullback.mapOverBase i j f g)_*[A])).obj
        ((L((pullback.mapOverBase i j f g)^*[A])).obj (externalProduct A f g K L)) ≅
      externalProduct A f g ((R((i)_*[A])).obj ((L((i)^*[A])).obj K))
        ((R((j)_*[A])).obj ((L((j)^*[A])).obj L))) :=
  nonempty_iso_externalProduct_closedImmersion_of_flat A f g i j K L
/-- Blueprint `lemma-kunneth-formula-compact-supports`: Supported product over a relative base.

Let `f : X ⟶ B` and `g : Y ⟶ B` be separated of finite type, `h = f ×_B g`, and let
`i : Z ⟶ X`, `j : W ⟶ Y` be closed immersions, with product
`i ×_B j : Z ×_B W ⟶ X ×_B Y`. For `K` and `L` on `X` and `Y` such that `i_* i^* K` and `j_* j^* L`
lie in `Dctf`,

`Rf_!(i_* i^* K) ⊗ᴸ Rg_!(j_* j^* L) ≅ Rh_!((i ×_B j)_* (i ×_B j)^* (K ⊠ L))`.

This is the relative product theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the
complexes `i_* i^* K` and `j_* j^* L`, rewritten with
`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_closedImmersion`. Over `B = Spec k` it
is the Künneth formula for the compactly supported cohomology of `Z ×_k W`.

The hypotheses are on `i_* i^* K` and `j_* j^* L` rather than on `K` and `L`: that `Ri_*` preserves
`Dctf` is a finiteness theorem for torsion coefficients of exponent invertible on the base
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar`), which in the blueprint's
setting turns `K, L ∈ Dctf` into these hypotheses. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f] [HasCompactification g]
    [QuasiCompact f] [QuasiCompact g] [HasCompactification (pullback.toBase f g)]
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)))
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L))) :
    Nonempty (((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj
          ((R((i)_*[ModuleCat.{u + 1} Λ])).obj ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)))).obj
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj
          ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L))) ≅
      (R(pullback.toBase f g)_![ModuleCat.{u + 1} Λ]).obj
        ((R((pullback.mapOverBase i j f g)_*[ModuleCat.{u + 1} Λ])).obj
          ((L((pullback.mapOverBase i j f g)^*[ModuleCat.{u + 1} Λ])).obj
            (externalProduct (ModuleCat.{u + 1} Λ) f g K L)))) := by
  obtain ⟨e⟩ := nonempty_iso_externalProduct_closedImmersion (ModuleCat.{u + 1} Λ) f g i j K L
  obtain ⟨k⟩ := nonempty_iso_rightDerivedLowerShriek_externalProduct Λ f g hK hL
  exact ⟨k.symm ≪≫ (R(pullback.toBase f g)_![ModuleCat.{u + 1} Λ]).mapIso e.symm⟩

/-- Blueprint `lemma-kunneth-formula-compact-supports`: Supported product over a relative base.

The Künneth formula with closed supports over a field: for `X`, `Y` separated of finite type
over a field `k` and closed subschemes `i : Z ⟶ X`, `j : W ⟶ Y`,

`RΓ_c(Z, i^* K) ⊗ᴸ RΓ_c(W, j^* L) ≅ RΓ_c(Z × W, (K ⊠ L)|_{Z × W})`,

written one step earlier, in `D((Spec k)_ét)`, with the structure morphisms `i ≫ f`,
`j ≫ g` of `Z`, `W` and `Z × W ⟶ Spec k`.

It is the relative product theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for `i ≫ f`,
`j ≫ g` and the complexes `i^* K`, `j^* L`, rewritten with
`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_externalProduct`. Comparing it with
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion`
over `B = Spec k` would also need `R(i ≫ f)_! ≅ Rf_! Ri_*`, the composition of compactly
supported direct images. -/
theorem nonempty_iso_compactlySupported_externalProduct_closedImmersion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [HasCompactification f] [HasCompactification g] [QuasiCompact f] [QuasiCompact g]
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [HasCompactification (i ≫ f)] [HasCompactification (j ≫ g)]
    [HasCompactification (pullback.toBase (i ≫ f) (j ≫ g))]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    Nonempty (((-⊗ᴸ-(Spec (.of k))[ModuleCat.{u + 1} Λ]).obj
          ((R(i ≫ f)_![ModuleCat.{u + 1} Λ]).obj ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
        ((R(j ≫ g)_![ModuleCat.{u + 1} Λ]).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L)) ≅
      (R(pullback.toBase (i ≫ f) (j ≫ g))_![ModuleCat.{u + 1} Λ]).obj
        ((L((pullback.mapOverBase i j f g)^*[ModuleCat.{u + 1} Λ])).obj
          (externalProduct (ModuleCat.{u + 1} Λ) f g K L))) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_externalProduct (ModuleCat.{u + 1} Λ) f g i j
    K L
  have : QuasiCompact (i ≫ f) := inferInstance
  have : QuasiCompact (j ≫ g) := inferInstance
  obtain ⟨k⟩ := nonempty_iso_rightDerivedLowerShriek_externalProduct Λ (i ≫ f) (j ≫ g)
    (constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) i hK)
    (constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) j hL)
  exact ⟨k.symm ≪≫ (R(pullback.toBase (i ≫ f) (j ≫ g))_![ModuleCat.{u + 1} Λ]).mapIso e.symm⟩

end Etale

end AlgebraicGeometry
