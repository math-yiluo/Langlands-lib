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
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative

/-!

# The `!`-Künneth isomorphism on the étale site

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct`
  (`lemma-external-duality-trace-morphism` (i)): the `!`-Künneth isomorphism
  `Ku_! : R(f₁ × f₂)_! (M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂` for a finite coefficient ring.

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

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

section KunnethShriek

/-! ### The `!`-Künneth isomorphism

Item (i) of `lemma-external-duality-trace-morphism`: for `fᵢ : Xᵢ ⟶ Yᵢ` over `S`, the `!`-Künneth
isomorphism `Ku_! : R(f₁ × f₂)_! (M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂` is the relative product theorem
over `B = Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_{Y₁} B) ×_B (X₂ ×_{Y₂} B)`
(`CategoryTheory.Limits.pullback.mapOverBaseIso`) and compact-support base change. -/

/-- For an isomorphism `e : Y ≅ Y'` of schemes, the derived pushforward `R(e_*)` is the
derived pullback `L((e⁻¹)^*)`: both are computed by the exact functor `e_* ≅ (e⁻¹)^*`. -/
noncomputable def rightDerivedLowerStarIsoLeftDerivedUpperStarInv {Y Y' : Scheme.{u}}
    (e : Y ≅ Y') : R((e.hom)_*[A]) ≅ L((e.inv)^*[A]) :=
  have : PreservesFiniteColimits (e.hom)_*[A] :=
    preservesFiniteColimits_of_natIso (upperStarInvIsoLowerStarHom A e)
  Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarInvIsoLowerStarHom A e).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory A e.inv).symm

variable {S X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁)
  (f₂ : X₂ ⟶ Y₂)

omit [HasSmallSiteSheafify A] in
/-- Transport of `R(f₁ × f₂)_!` along `pullback.mapOverBaseIso`: for `Z` in
`D((X₁ ×_S X₂)_ét)`, writing `e : X₁ ×_S X₂ ≅ (X₁ ×_{Y₁} B) ×_B (X₂ ×_{Y₂} B)` with
`B = Y₁ ×_S Y₂` and `h` for the structure morphism of the fibre product over `B`,

`R(f₁ × f₂)_! Z ≅ Rh_! (L(e⁻¹)^* Z)`, given the composition isomorphism
`R(f₁ × f₂)_! ≅ Re_! ⋙ Rh_!` (`hcomp`), which holds for torsion coefficients
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`). -/
theorem nonempty_iso_rightDerivedLowerShriek_mapOverBase
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    [HasCompactification (pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
      (pullback.snd f₂ (pullback.snd b₁ b₂)))]
    [HasCompactification (pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom]
    (hcomp : Nonempty (R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A] ≅
      R((pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom)_![A] ⋙
        R(pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
          (pullback.snd f₂ (pullback.snd b₁ b₂)))_![A]))
    (Z : _root_.DerivedCategory (Sheaf (pullback (f₁ ≫ b₁) (f₂ ≫ b₂)).smallEtaleTopology A)) :
    Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A]).obj Z ≅
      (R(pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
        (pullback.snd f₂ (pullback.snd b₁ b₂)))_![A]).obj
        ((L(((pullback.mapOverBaseIso f₁ f₂ b₁ b₂).inv)^*[A])).obj Z)) := by
  set e := pullback.mapOverBaseIso f₁ f₂ b₁ b₂
  set h := pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
      (pullback.snd f₂ (pullback.snd b₁ b₂))
  obtain ⟨c₁⟩ := hcomp
  obtain ⟨c₂⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar A e.hom
  exact ⟨c₁.app Z ≪≫ (R(h)_![A]).mapIso
    (c₂.app Z ≪≫ (rightDerivedLowerStarIsoLeftDerivedUpperStarInv A e).app Z)⟩

omit [HasSmallSiteSheafify A] in
/-- The external product is compatible with `pullback.mapOverBaseIso`: writing
`e : X₁ ×_S X₂ ≅ (X₁ ×_{Y₁} B) ×_B (X₂ ×_{Y₂} B)` with `B = Y₁ ×_S Y₂` and `hᵢ` for the
projections `Xᵢ ×_{Yᵢ} B ⟶ Xᵢ`,

`L(e⁻¹)^* (M₁ ⊠_S M₂) ≅ Lh₁^* M₁ ⊠_B Lh₂^* M₂`. -/
theorem nonempty_iso_leftDerivedUpperStar_mapOverBaseIso_externalProduct
    [UpperStarPreservesFlat A]
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)) :
    Nonempty ((L(((pullback.mapOverBaseIso f₁ f₂ b₁ b₂).inv)^*[A])).obj
        (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
      externalProduct A (pullback.snd f₁ (pullback.fst b₁ b₂))
        (pullback.snd f₂ (pullback.snd b₁ b₂))
        ((L((pullback.fst f₁ (pullback.fst b₁ b₂))^*[A])).obj M₁)
        ((L((pullback.fst f₂ (pullback.snd b₁ b₂))^*[A])).obj M₂)) := by
  -- The schemes in the type of `pullback.mapOverBaseIso` carry other `HasPullback` instances
  -- than the ones found here. Spelling out the source and target of `e`, writing the two
  -- isomorphisms `pb₁`, `pb₂` with explicit types and tensoring them with `derivedTensor` keeps
  -- every comparison syntactic; otherwise the kernel unfolds the derived tensor product down
  -- to complexes, which takes minutes.
  let e : pullback (pullback.snd f₁ (pullback.fst b₁ b₂)) (pullback.snd f₂ (pullback.snd b₁ b₂)) ⟶
      pullback (f₁ ≫ b₁) (f₂ ≫ b₂) := (pullback.mapOverBaseIso f₁ f₂ b₁ b₂).inv
  let pb₁ : (L((e)^*[A])).obj ((L((pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂))^*[A])).obj M₁) ≅
      (L((pullback.fst (pullback.snd f₁ (pullback.fst b₁ b₂))
        (pullback.snd f₂ (pullback.snd b₁ b₂)))^*[A])).obj
        ((L((pullback.fst f₁ (pullback.fst b₁ b₂))^*[A])).obj M₁) :=
    ((leftDerivedUpperStarComp A e (pullback.fst _ _)).app M₁).symm ≪≫
      (leftDerivedUpperStarComp A _ _ (e ≫ pullback.fst _ _) (by simp [e])).app M₁
  let pb₂ : (L((e)^*[A])).obj ((L((pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂))^*[A])).obj M₂) ≅
      (L((pullback.snd (pullback.snd f₁ (pullback.fst b₁ b₂))
        (pullback.snd f₂ (pullback.snd b₁ b₂)))^*[A])).obj
        ((L((pullback.fst f₂ (pullback.snd b₁ b₂))^*[A])).obj M₂) :=
    ((leftDerivedUpperStarComp A e (pullback.snd _ _)).app M₂).symm ≪≫
      (leftDerivedUpperStarComp A _ _ (e ≫ pullback.snd _ _) (by simp [e])).app M₂
  exact ⟨leftDerivedUpperStarTensorIso A e _ _ ≪≫ ((derivedTensor A _).mapIso pb₁).app _ ≪≫
    ((derivedTensor A _).obj _).mapIso pb₂⟩

omit [HasSmallSiteSheafify A] in
/-- The `!`-Künneth isomorphism `Ku_! : R(f₁ × f₂)_! (M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂`, given
the composition isomorphism `R(f₁ × f₂)_! ≅ Re_! ⋙ Rh_!`, compact-support base change of
`Rfᵢ_! Mᵢ` along the projections `Y₁ ×_S Y₂ ⟶ Yᵢ`, and the relative product theorem over
`B = Y₁ ×_S Y₂` for the pulled back complexes. -/
theorem nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct_of_kunneth
    [UpperStarPreservesFlat A]
    [HasCompactification f₁] [HasCompactification f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A))
    [HasCompactification (pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom]
    [HasCompactification (pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
      (pullback.snd f₂ (pullback.snd b₁ b₂)))]
    (hcomp : Nonempty (R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A] ≅
      R((pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom)_![A] ⋙
        R(pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
          (pullback.snd f₂ (pullback.snd b₁ b₂)))_![A]))
    (hbc₁ : Nonempty ((L((pullback.fst b₁ b₂)^*[A])).obj ((R(f₁)_![A]).obj M₁) ≅
      (R(pullback.snd f₁ (pullback.fst b₁ b₂))_![A]).obj
        ((L((pullback.fst f₁ (pullback.fst b₁ b₂))^*[A])).obj M₁)))
    (hbc₂ : Nonempty ((L((pullback.snd b₁ b₂)^*[A])).obj ((R(f₂)_![A]).obj M₂) ≅
      (R(pullback.snd f₂ (pullback.snd b₁ b₂))_![A]).obj
        ((L((pullback.fst f₂ (pullback.snd b₁ b₂))^*[A])).obj M₂)))
    (hku : Nonempty ((R(pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
        (pullback.snd f₂ (pullback.snd b₁ b₂)))_![A]).obj
        (externalProduct A (pullback.snd f₁ (pullback.fst b₁ b₂))
          (pullback.snd f₂ (pullback.snd b₁ b₂))
          ((L((pullback.fst f₁ (pullback.fst b₁ b₂))^*[A])).obj M₁)
          ((L((pullback.fst f₂ (pullback.snd b₁ b₂))^*[A])).obj M₂)) ≅
      ((-⊗ᴸ-(pullback b₁ b₂)[A]).obj ((R(pullback.snd f₁ (pullback.fst b₁ b₂))_![A]).obj
          ((L((pullback.fst f₁ (pullback.fst b₁ b₂))^*[A])).obj M₁))).obj
        ((R(pullback.snd f₂ (pullback.snd b₁ b₂))_![A]).obj
          ((L((pullback.fst f₂ (pullback.snd b₁ b₂))^*[A])).obj M₂)))) :
    Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A]).obj
        (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
      externalProduct A b₁ b₂ ((R(f₁)_![A]).obj M₁) ((R(f₂)_![A]).obj M₂)) := by
  obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerShriek_mapOverBase A b₁ b₂ f₁ f₂ hcomp
    (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂)
  obtain ⟨p⟩ := nonempty_iso_leftDerivedUpperStar_mapOverBaseIso_externalProduct A b₁ b₂ f₁ f₂
    M₁ M₂
  obtain ⟨ku⟩ := hku
  obtain ⟨e₁⟩ := hbc₁
  obtain ⟨e₂⟩ := hbc₂
  exact ⟨t ≪≫ (R(_)_![A]).mapIso p ≪≫ ku ≪≫
    ((-⊗ᴸ-(pullback b₁ b₂)[A]).mapIso e₁.symm).app _ ≪≫
    ((-⊗ᴸ-(pullback b₁ b₂)[A]).obj _).mapIso e₂.symm⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- The `!`-Künneth isomorphism `Ku_! : R(f₁ × f₂)_! (M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂` for a
finite coefficient ring, given compact-support base change of `Rfᵢ_! Mᵢ` along the projections
`Y₁ ×_S Y₂ ⟶ Yᵢ` and the composition isomorphism `R(f₁ × f₂)_! ≅ Re_! ⋙ Rh_!` of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_mapOverBase`; both hold for torsion
coefficients. It is the relative product theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` over
`B = Y₁ ×_S Y₂`, transported along `pullback.mapOverBaseIso`. -/
theorem nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct_of_baseChange
    [HasCompactification f₁] [HasCompactification f₂] [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    {M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM₁ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₁ M₁)
    (hM₂ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₂ M₂)
    [HasCompactification (pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom]
    [HasCompactification (pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
      (pullback.snd f₂ (pullback.snd b₁ b₂)))]
    (hcomp : Nonempty (R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![ModuleCat.{u + 1} Λ] ≅
      R((pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom)_![ModuleCat.{u + 1} Λ] ⋙
        R(pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
          (pullback.snd f₂ (pullback.snd b₁ b₂)))_![ModuleCat.{u + 1} Λ]))
    (hbc₁ : Nonempty ((L((pullback.fst b₁ b₂)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(f₁)_![ModuleCat.{u + 1} Λ]).obj M₁) ≅
      (R(pullback.snd f₁ (pullback.fst b₁ b₂))_![ModuleCat.{u + 1} Λ]).obj
        ((L((pullback.fst f₁ (pullback.fst b₁ b₂))^*[ModuleCat.{u + 1} Λ])).obj M₁)))
    (hbc₂ : Nonempty ((L((pullback.snd b₁ b₂)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(f₂)_![ModuleCat.{u + 1} Λ]).obj M₂) ≅
      (R(pullback.snd f₂ (pullback.snd b₁ b₂))_![ModuleCat.{u + 1} Λ]).obj
        ((L((pullback.fst f₂ (pullback.snd b₁ b₂))^*[ModuleCat.{u + 1} Λ])).obj M₂))) :
    Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
      externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ ((R(f₁)_![ModuleCat.{u + 1} Λ]).obj M₁)
        ((R(f₂)_![ModuleCat.{u + 1} Λ]).obj M₂)) := by
  obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerShriek_mapOverBase (ModuleCat.{u + 1} Λ) b₁ b₂ f₁
    f₂ hcomp (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂)
  obtain ⟨p⟩ := nonempty_iso_leftDerivedUpperStar_mapOverBaseIso_externalProduct
    (ModuleCat.{u + 1} Λ) b₁ b₂ f₁ f₂ M₁ M₂
  have : QuasiCompact (pullback.snd f₁ (pullback.fst b₁ b₂)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback f₁ (pullback.fst b₁ b₂)) inferInstance
  have : QuasiCompact (pullback.snd f₂ (pullback.snd b₁ b₂)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback f₂ (pullback.snd b₁ b₂)) inferInstance
  obtain ⟨ku⟩ := nonempty_iso_rightDerivedLowerShriek_externalProduct Λ
    (pullback.snd f₁ (pullback.fst b₁ b₂)) (pullback.snd f₂ (pullback.snd b₁ b₂))
    (constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) (pullback.fst f₁ _) hM₁)
    (constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) (pullback.fst f₂ _) hM₂)
  obtain ⟨e₁⟩ := hbc₁
  obtain ⟨e₂⟩ := hbc₂
  exact ⟨t ≪≫ (R(_)_![ModuleCat.{u + 1} Λ]).mapIso p ≪≫ ku ≪≫
    ((-⊗ᴸ-(pullback b₁ b₂)[ModuleCat.{u + 1} Λ]).mapIso e₁.symm).app _ ≪≫
    ((-⊗ᴸ-(pullback b₁ b₂)[ModuleCat.{u + 1} Λ]).obj _).mapIso e₂.symm⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `lemma-external-duality-trace-morphism` (i), `lemma-external-duality-trace-morphism`
(i): the `!`-Künneth isomorphism.

Let `fᵢ : Xᵢ ⟶ Yᵢ` be separated of finite type between schemes over `S`, let `Λ` be a finite
coefficient ring and `Mᵢ` in `Dctf(Xᵢ, Λ)`. Writing `f = f₁ × f₂ : X₁ ×_S X₂ ⟶ Y₁ ×_S Y₂`,

`Ku_! : Rf_!(M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂`.

This is the relative product theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the base
`B = Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_{Y₁} B) ×_B (X₂ ×_{Y₂} B)`, together with
compact-support base change `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`
along the projections `B ⟶ Yᵢ`. The finiteness of `Λ` is the hypothesis of that base change
theorem. -/
theorem nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct
    [HasCompactification f₁] [HasCompactification f₂] [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    {M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (_hM₁ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₁ M₁)
    (_hM₂ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₂ M₂) :
    Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
      externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂
        ((R(f₁)_![ModuleCat.{u + 1} Λ]).obj M₁) ((R(f₂)_![ModuleCat.{u + 1} Λ]).obj M₂)) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ
    (IsPullback.of_hasPullback f₁ (pullback.fst b₁ b₂))
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ
    (IsPullback.of_hasPullback f₂ (pullback.snd b₁ b₂))
  set e := pullback.mapOverBaseIso f₁ f₂ b₁ b₂
  set h := pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
      (pullback.snd f₂ (pullback.snd b₁ b₂))
  have he : e.hom ≫ h = pullback.mapOverBase f₁ f₂ b₁ b₂ :=
    pullback.mapOverBaseIso_hom_toBase ..
  have : HasCompactification h :=
    ((HasCompactification.compactification (pullback.mapOverBase f₁ f₂ b₁ b₂)).transport
      e (Iso.refl _) (by rw [Iso.refl_hom, Category.comp_id, he])).hasCompactification
  have : HasCompactification (e.hom ≫ h) := .of_eq he.symm
  have : QuasiCompact h := by
    rw [show h = _ from (pullback.fst_comp_eq_toBase _ _).symm]; infer_instance
  have hcongr : ∀ (ψ : _ ⟶ _) [HasCompactification ψ], ψ = pullback.mapOverBase f₁ f₂ b₁ b₂ →
      Nonempty (R(ψ)_![ModuleCat.{u + 1} Λ] ≅
        R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![ModuleCat.{u + 1} Λ]) := by
    rintro ψ _ rfl; exact ⟨Iso.refl _⟩
  obtain ⟨c₀⟩ := hcongr _ he
  obtain ⟨c₁⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ e.hom h
  have : QuasiCompact (pullback.snd f₁ (pullback.fst b₁ b₂)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback f₁ (pullback.fst b₁ b₂)) inferInstance
  have : QuasiCompact (pullback.snd f₂ (pullback.snd b₁ b₂)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback f₂ (pullback.snd b₁ b₂)) inferInstance
  exact nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct_of_kunneth _
    b₁ b₂ f₁ f₂ M₁ M₂ ⟨c₀.symm ≪≫ c₁⟩
    ⟨asIso ((rightDerivedLowerShriekBaseChangeMap _
      (IsPullback.of_hasPullback f₁ (pullback.fst b₁ b₂))).app M₁)⟩
    ⟨asIso ((rightDerivedLowerShriekBaseChangeMap _
      (IsPullback.of_hasPullback f₂ (pullback.snd b₁ b₂))).app M₂)⟩
    (nonempty_iso_rightDerivedLowerShriek_externalProduct_of_finite Λ _ _ _ _)

end KunnethShriek

end Etale

end AlgebraicGeometry
