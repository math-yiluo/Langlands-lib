/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.DualReduction
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Pullback

/-!

# Duality of external products of perfect complexes on smooth schemes

The remark `rem-sf-kv-formal` (`sk-rem-sf-kv-formal`) observes that the statement
`𝔻_{X × Y} (M ⊠ N) ≅ 𝔻_X M ⊠ 𝔻_Y N`, equivalent to the Künneth–Verdier isomorphism, is *formal*
for perfect `M`, `N` on smooth `X`, `Y`: under orientations the Verdier dual of a perfect complex
is its twisted shifted coefficient dual (`theorem-poincare-duality--2`), and the coefficient dual of
an external product of perfect complexes is the external product of the coefficient duals
(`theorem-poincare-duality--4`). This file records that formal case.

## Main statements

- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_externalProduct`
  (`sk-rem-sf-kv-formal`, `rem-sf-kv-formal`): `𝔻(P ⊠ Q) ≅ 𝔻P ⊠ 𝔻Q` for perfect `P`, `Q`, given
  orientations of `X`, `Y` and `X × Y`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section Generic

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The internal tensor–Hom adjunction `RHom(K, RHom(N, W)) ≅ RHom(N ⊗ᴸ K, W)`. -/
noncomputable def derivedHomDerivedHomIso {X : Scheme.{u}}
    (K N W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (RHom(X)[A].obj (op K)).obj ((RHom(X)[A].obj (op N)).obj W) ≅
      (RHom(X)[A].obj (op (((-⊗ᴸ-(X)[A]).obj N).obj K))).obj W :=
  ((((derivedTensorHomAdjunction A (N ⊗ K)).ofNatIsoLeft (tensorLeftTensor N K)).rightAdjointUniq
    ((derivedTensorHomAdjunction A K).comp (derivedTensorHomAdjunction A N))).app W).symm

/-- The coefficient dual of a tensor product with a dualizable complex:
`(K ⊗ᴸ M)^∨ ≅ K^∨ ⊗ᴸ M^∨` for `M` dualizable. -/
theorem nonempty_iso_coefficientDual_derivedTensor {X : Scheme.{u}}
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hM : IsDualizable M) :
    Nonempty ((coefficientDual A X).obj (op (((-⊗ᴸ-(X)[A]).obj K).obj M)) ≅
      ((-⊗ᴸ-(X)[A]).obj ((coefficientDual A X).obj (op K))).obj
        ((coefficientDual A X).obj (op M))) := by
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip A X
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor hM ((coefficientDual A X).obj (op K))
  exact ⟨(derivedHomDerivedHomIso M K (𝟙_ _)).symm ≪≫ e.symm ≪≫ (β.app _).app _⟩

variable [Etale.UpperStarPreservesFlat A]

/-- The derived pullback of a dualizable complex is dualizable. -/
theorem isDualizable_leftDerivedUpperStar {X Y : Scheme.{u}} (g : Y ⟶ X)
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hM : IsDualizable M) : IsDualizable ((L((g)^*[A])).obj M) := by
  obtain ⟨_⟩ := nonempty_monoidal_leftDerivedUpperStar A g
  exact hM.map _

/-- The derived pullback commutes with the coefficient dual of a dualizable complex:
`Lg^* (M^∨) ≅ (Lg^* M)^∨`. -/
theorem nonempty_iso_leftDerivedUpperStar_coefficientDual {X Y : Scheme.{u}} (g : Y ⟶ X)
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hM : IsDualizable M) :
    Nonempty ((L((g)^*[A])).obj ((coefficientDual A X).obj (op M)) ≅
      (coefficientDual A Y).obj (op ((L((g)^*[A])).obj M))) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_derivedHom g hM (𝟙_ _)
  exact ⟨e ≪≫ ((RHom(Y)[A]).obj _).mapIso (leftDerivedUpperStarUnitIso A g)⟩

end Generic

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

variable [HasTateTwist Λ]

/-- Blueprint `sk-rem-sf-kv-formal`, `rem-sf-kv-formal`: the formal case of duality of external
products.

Let `a : X ⟶ S` and `b : Y ⟶ S` carry orientations of relative dimensions `d` and `e`, and let
the structure morphism of `X ×_S Y` carry one of relative dimension `d + e` (by smooth purity,
`proposition-smooth-purity-finite-coefficients`, orientations exist for smooth `X`, `Y` over a
field, `AlgebraicGeometry.Etale.Orientation.nonempty`). Then for perfect (dualizable) `P` on `X` and
`Q` on `Y`,

`𝔻_{X ×_S Y} (P ⊠ Q) ≅ 𝔻_X P ⊠ 𝔻_Y Q`.

Indeed `𝔻 K ≅ K^∨ ⊗ᴸ Λ(c)[2c]` for perfect `K` (`theorem-poincare-duality--2`), the coefficient dual
of `P ⊠ Q = p^* P ⊗ᴸ q^* Q` is `P^∨ ⊠ Q^∨` (`theorem-poincare-duality--4`), and
`Λ(d)[2d] ⊠ Λ(e)[2e] ≅ Λ(d + e)[2(d + e)]`. This is the base of the induction, not a substitute
for it: for non-perfect complexes the statement needs the exceptional Künneth formula. -/
theorem Orientation.nonempty_iso_verdierDual_externalProduct {X Y S : Scheme.{u}} (a : X ⟶ S)
    (b : Y ⟶ S) [HasCompactification a] [HasCompactification b]
    [HasCompactification (pullback.fst a b ≫ a)] [HasInvertibleExponent Λ S] {d e : ℕ}
    (oX : Orientation Λ a d) (oY : Orientation Λ b e)
    (oXY : Orientation Λ (pullback.fst a b ≫ a) (d + e))
    {P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hP : IsDualizable P) (hQ : IsDualizable Q) :
    Nonempty ((verdierDual Λ (pullback.fst a b ≫ a)).obj
        (op (externalProduct (ModuleCat.{u + 1} Λ) a b P Q)) ≅
      externalProduct (ModuleCat.{u + 1} Λ) a b ((verdierDual Λ a).obj (op P))
        ((verdierDual Λ b).obj (op Q))) := by
  have : HasInvertibleExponent Λ X := .of_hom a
  have : HasInvertibleExponent Λ Y := .of_hom b
  have : HasInvertibleExponent Λ (pullback a b) := .of_hom (pullback.fst a b ≫ a)
  have hP':= isDualizable_leftDerivedUpperStar (pullback.fst a b) hP
  have hQ' := isDualizable_leftDerivedUpperStar (pullback.snd a b) hQ
  obtain ⟨e₁⟩ := oXY.nonempty_iso_verdierDual_coefficientDual
    (isDualizable_derivedTensor hP' hQ')
  obtain ⟨e₂⟩ := nonempty_iso_coefficientDual_derivedTensor
    (K := (L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).obj P) hQ'
  obtain ⟨c₁⟩ := nonempty_iso_leftDerivedUpperStar_coefficientDual (pullback.fst a b) hP
  obtain ⟨c₂⟩ := nonempty_iso_leftDerivedUpperStar_coefficientDual (pullback.snd a b) hQ
  obtain ⟨m⟩ := nonempty_iso_externalProduct_derivedTensor (ModuleCat.{u + 1} Λ) a b
    ((coefficientDual _ X).obj (op P)) ((tateObject Λ X d)⟦(2 * d : ℤ)⟧)
    ((coefficientDual _ Y).obj (op Q)) ((tateObject Λ Y e)⟦(2 * e : ℤ)⟧)
  obtain ⟨oP⟩ := oX.nonempty_iso_verdierDual_coefficientDual hP
  obtain ⟨oQ⟩ := oY.nonempty_iso_verdierDual_coefficientDual hQ
  -- the twists: `p^* Λ(d)[2d] ⊗ᴸ q^* Λ(e)[2e] ≅ Λ(d + e)[2(d + e)]`
  let t₁ : (L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ X d)⟦(2 * d : ℤ)⟧) ≅
      (tateObject Λ (pullback a b) d)⟦(2 * d : ℤ)⟧ :=
    ((L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * d : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 * d : ℤ)).mapIso (leftDerivedUpperStarTateObjectIso _ _)
  let t₂ : (L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ Y e)⟦(2 * e : ℤ)⟧) ≅
      (tateObject Λ (pullback a b) e)⟦(2 * e : ℤ)⟧ :=
    ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * e : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 * e : ℤ)).mapIso (leftDerivedUpperStarTateObjectIso _ _)
  let t : externalProduct (ModuleCat.{u + 1} Λ) a b ((tateObject Λ X d)⟦(2 * d : ℤ)⟧)
        ((tateObject Λ Y e)⟦(2 * e : ℤ)⟧) ≅
      (tateObject Λ (pullback a b) ((d + e : ℕ) : ℤ))⟦(2 * (d + e : ℕ) : ℤ)⟧ :=
    ((derivedTensor _ _).mapIso t₁).app _ ≪≫ ((derivedTensor _ _).obj _).mapIso t₂ ≪≫
      shiftTateObjectAddIso Λ (pullback a b) d e ≪≫ eqToIso (by push_cast; rfl)
  exact ⟨e₁ ≪≫ ((derivedTensor _ _).mapIso (e₂ ≪≫ ((derivedTensor _ _).mapIso c₁.symm).app _ ≪≫
      ((derivedTensor _ _).obj _).mapIso c₂.symm)).app _ ≪≫
    ((derivedTensor _ _).obj _).mapIso t.symm ≪≫ m.symm ≪≫
    externalProductMapIso _ a b oP.symm oQ.symm⟩

end Etale

end AlgebraicGeometry
