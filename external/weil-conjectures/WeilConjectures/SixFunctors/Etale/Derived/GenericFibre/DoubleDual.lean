/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom

/-!
# The double dual along a monoidal functor, up to an invertible twist

This file contains the formal part of blueprint `lemma-double-dual-geometric-generic-fibre--1`: a
comparison `g^* ω_X ≅ ω_{X'} ⊗ L` with `L` invertible identifies `g^* δ_K` with `δ_{g^* K}`,
as soon as the internal-hom comparisons of `g^*` at `(K, ω_X)` and at `(𝔻_X K, ω_X)` are
isomorphisms; the invertible twist cancels after dualising twice.

## Main statements

- `CategoryTheory.MonoidalClosed.isIso_toIhomIhom_tensor_right_iff`: for `L` invertible, the
  double-dual map of `X` relative to `W ⊗ L` is an isomorphism if and only if the one relative
  to `W` is.
- `CategoryTheory.MonoidalClosed.isIso_map_toIhomIhom_iff_of_iso_tensor`: for a lax braided
  functor `G` and `G W ≅ W' ⊗ L` with `L` invertible, `G δ_X` is an isomorphism if and only if
  `δ_{G X}` (relative to `W'`) is, provided the internal-hom comparisons of `G` at `(X, W)` and
  at `([X, W], W)` are isomorphisms.
- `AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff`: the
  same for the derived pullback `Lg^*` and the Verdier double-dual maps, for a general
  coefficient category.

## Implementation notes

The derived pullback `Lg^*` is not yet known to be braided for the derived braiding
`AlgebraicGeometry.Etale.derivedBraidedCategory`. The statements for `Lg^*` therefore take the
braided axiom for the monoidal structure `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`
as an explicit hypothesis (`hbr`), and this is the only missing input.

The derived statements are made for a general coefficient category `A`, with the twisted
object written using `AlgebraicGeometry.Etale.derivedTensor`, so that they can be specialised to
`A = ModuleCat Λ` without comparing monoidal instances (see the implementation notes of
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- Blueprint `lemma-double-dual-geometric-generic-fibre--1` (formal core): biduality is invariant
under twisting the dualizing object by an invertible object. For `L` invertible, the double-dual map
`X ⟶ [[X, W ⊗ L], W ⊗ L]` is an isomorphism if and only if `X ⟶ [[X, W], W]` is.

The canonical isomorphisms `[X, W] ⊗ L ≅ [X, W ⊗ L]`
(`CategoryTheory.MonoidalClosed.isIso_ihomTensorToIhom`) identify the self-adjunction of
`[-, W ⊗ L]` with that of `[-, W]` followed by the autoequivalence `- ⊗ L` of `Cᵒᵖ`, and the units
of the two adjunctions are isomorphisms at the same objects. -/
theorem isIso_toIhomIhom_tensor_right_iff (W X : C) {L : C} (hL : IsInvertible L) :
    IsIso (toIhomIhom (W ⊗ L) X) ↔ IsIso (toIhomIhom W X) := by
  obtain ⟨L', ⟨e⟩, ⟨e'⟩⟩ := hL
  have hL : IsInvertible L := ⟨L', ⟨e⟩, ⟨e'⟩⟩
  let E : Cᵒᵖ ≌ Cᵒᵖ := (tensorRightEquivalenceOfTensorIso e e').op
  have : ∀ Y : C, IsIso (ihomTensorToIhom Y W L) := fun Y ↦ isIso_ihomTensorToIhom Y W hL
  let iso : (internalHom.flip.obj (W ⊗ L)).rightOp ≅
      (internalHom.flip.obj W).rightOp ⋙ E.functor :=
    NatIso.ofComponents (fun Y ↦ (asIso (ihomTensorToIhom Y W L)).op) (fun {Y Y'} f ↦ by
      apply Quiver.Hom.unop_inj
      exact (pre_app_whiskerRight_comp_ihomTensorToIhom f W L).symm)
  have h := Adjunction.isIso_unit_app_iff_of_iso (ihomFlipSelfAdjunction (W ⊗ L))
    ((ihomFlipSelfAdjunction W).comp E.toAdjunction) iso X
  rw [Adjunction.comp_unit_app, ihomFlipSelfAdjunction_unit_app,
    ihomFlipSelfAdjunction_unit_app, Equivalence.toAdjunction_unit, isIso_comp_right_iff] at h
  exact h

variable {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D] [MonoidalClosed D]

/-- Blueprint `lemma-double-dual-geometric-generic-fibre--1` (formal core): let `G` be a lax braided
functor between braided monoidal closed categories, and let `G W ≅ W' ⊗ L` with `L` invertible.
If the internal-hom comparisons `G [X, W] ⟶ [G X, G W]` and `G [[X, W], W] ⟶ [G [X, W], G W]`
of `G` are isomorphisms, then `G δ_X` is an isomorphism if and only if the double-dual map
`δ_{G X} : G X ⟶ [[G X, W'], W']` is: the twist by `L` cancels after dualising twice
(`CategoryTheory.MonoidalClosed.isIso_toIhomIhom_tensor_right_iff`), and the comparison along
`G` is `CategoryTheory.MonoidalClosed.isIso_map_toIhomIhom_iff`. -/
theorem isIso_map_toIhomIhom_iff_of_iso_tensor (G : C ⥤ D) [G.LaxBraided] {W : C} {W' L : D}
    (hL : IsInvertible L) (e : G.obj W ≅ W' ⊗ L) (X : C)
    (h₁ : IsIso ((Functor.LaxMonoidal.ihomComparison G X).app W))
    (h₂ : IsIso ((Functor.LaxMonoidal.ihomComparison G ((ihom X).obj W)).app W)) :
    IsIso (G.map (toIhomIhom W X)) ↔ IsIso (toIhomIhom W' (G.obj X)) := by
  have : IsIso (dualComparison G e.hom X) := by
    rw [dualComparison]
    infer_instance
  have : IsIso (dualComparison G e.hom ((ihom X).obj W)) := by
    rw [dualComparison]
    infer_instance
  rw [isIso_map_toIhomIhom_iff G e.hom X]
  exact isIso_toIhomIhom_tensor_right_iff W' (G.obj X) hL

end CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- The braided axiom for the monoidal structure
`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal` of the derived pullback `Lg^*`, for the
derived braidings `CategoryTheory.DerivedCategory.braidedCategory'` (at `A = ModuleCat Λ`,
`AlgebraicGeometry.Etale.derivedBraidedCategory`):
`μ_{K, M} ≫ Lg^* β_{K, M} = β_{Lg^* K, Lg^* M} ≫ μ_{M, K}`. -/
def LeftDerivedUpperStarBraided {X Y : Scheme.{u}} (g : Y ⟶ X) : Prop :=
  letI := leftDerivedUpperStarMonoidal A g
  ∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
    Functor.LaxMonoidal.μ (L((g)^*[A])) K M ≫ (L((g)^*[A])).map (β_ K M).hom =
      (β_ ((L((g)^*[A])).obj K) ((L((g)^*[A])).obj M)).hom ≫
        Functor.LaxMonoidal.μ (L((g)^*[A])) M K

/-- The lax braided structure on `Lg^*` given by the monoidal structure
`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal` and the braided axiom. -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarLaxBraided {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hbr : LeftDerivedUpperStarBraided A g) : (L((g)^*[A])).LaxBraided :=
  letI := leftDerivedUpperStarMonoidal A g
  { braided := hbr }

/-- **The double dual along a derived pullback, up to an invertible twist**, for arbitrary
objects `ω_X`, `ω_{X'}` in place of the dualizing complexes: if `Lg^* ω_X ≅ ω_{X'} ⊗ᴸ L` with `L`
invertible and the internal-hom comparisons
`Lg^* RHom(K, ω_X) ⟶ RHom(Lg^* K, Lg^* ω_X)` and
`Lg^* RHom(RHom(K, ω_X), ω_X) ⟶ RHom(Lg^* RHom(K, ω_X), Lg^* ω_X)` are isomorphisms, then
`Lg^*` of the double-dual map `K ⟶ RHom(RHom(K, ω_X), ω_X)` is an isomorphism if and only if the
double-dual map of `Lg^* K` into `ω_{X'}` is. It is stated for a general coefficient category
`A`, where the kernel checks it without unfolding the derived categories of `ModuleCat Λ`; see
`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff`. -/
theorem isIso_leftDerivedUpperStar_map_derivedHomToIhomIhomNatTrans_app_iff
    {X X' : Scheme.{u}} (ωX : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (ωX' : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)) (g : X' ⟶ X)
    (hbr : LeftDerivedUpperStarBraided A g)
    {L : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)} (hL : IsInvertible L)
    (e : (L((g)^*[A])).obj ωX ≅ ((derivedTensor A X').obj ωX').obj L)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (h₁ : IsIso (derivedHomUpperStarComparison A g K ωX))
    (h₂ : IsIso (derivedHomUpperStarComparison A g (((RHom(X)[A]).flip.obj ωX).obj (op K)) ωX)) :
    IsIso ((L((g)^*[A])).map ((derivedHomToIhomIhomNatTrans A X ωX).app K)) ↔
      IsIso ((derivedHomToIhomIhomNatTrans A X' ωX').app ((L((g)^*[A])).obj K)) := by
  let := leftDerivedUpperStarLaxBraided A g hbr
  exact isIso_map_toIhomIhom_iff_of_iso_tensor L((g)^*[A]) hL e K h₁ h₂

/-- Blueprint `lemma-double-dual-geometric-generic-fibre--1`, formal part: **the double dual along a
derived pullback, up to an invertible twist.**

Let `g : X' ⟶ X`, let `a : X ⟶ S` and `a' : X' ⟶ S'` admit compactifications, with dualizing
complexes `ω_X`, `ω_{X'}` and Verdier double-dual maps `δ`, and let
`Lg^* ω_X ≅ ω_{X'} ⊗ᴸ L` with `L` invertible. If the internal-hom comparisons
`Lg^* RHom(K, ω_X) ⟶ RHom(Lg^* K, Lg^* ω_X)` and
`Lg^* RHom(𝔻_X K, ω_X) ⟶ RHom(Lg^* 𝔻_X K, Lg^* ω_X)`
(`AlgebraicGeometry.Etale.derivedHomUpperStarComparison`) are isomorphisms, then
`Lg^* δ_K` is an isomorphism if and only if `δ_{Lg^* K}` is
(`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_derivedHomToIhomIhomNatTrans_app_iff`).

The hypothesis `hbr` (the braided axiom for `Lg^*`) is not yet available in the repository. -/
theorem isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff {X X' S S' : Scheme.{u}}
    (a : X ⟶ S) (a' : X' ⟶ S') [HasCompactification a] [HasCompactification a'] (g : X' ⟶ X)
    (hbr : LeftDerivedUpperStarBraided (ModuleCat.{u + 1} Λ) g)
    {L : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : IsInvertible L)
    (e : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ a) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X').obj (dualizingComplex Λ a')).obj L)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h₁ : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) g K (dualizingComplex Λ a)))
    (h₂ : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) g
      ((verdierDual Λ a).obj (op K)) (dualizingComplex Λ a))) :
    IsIso ((L((g)^*[ModuleCat.{u + 1} Λ])).map ((verdierDualDoubleDual Λ a).app K)) ↔
      IsIso ((verdierDualDoubleDual Λ a').app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
  isIso_leftDerivedUpperStar_map_derivedHomToIhomIhomNatTrans_app_iff (ModuleCat.{u + 1} Λ)
    (dualizingComplex Λ a) (dualizingComplex Λ a') g hbr hL e K h₁ h₂

end Etale

end AlgebraicGeometry
