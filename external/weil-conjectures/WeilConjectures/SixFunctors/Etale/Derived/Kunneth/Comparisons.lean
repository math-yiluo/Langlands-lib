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
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!

# The Künneth–Verdier comparison maps on the étale site

## Main definitions

- `AlgebraicGeometry.Etale.HasKunnethComparisons` (`lemma-external-duality-trace-morphism`): the
  four product comparison assertions `Ku_!`, `α`, `β`, `κ`, one per field.

## Main statements

- `AlgebraicGeometry.Etale.hasKunnethComparisons` (`lemma-external-duality-trace-morphism`): the
four
  comparison maps are isomorphisms.

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
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

namespace Etale

variable {B X Y : Scheme.{u}}

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- Blueprint `lemma-external-duality-trace-morphism`: The product comparison maps.

The four product comparison maps of the six-functor formalism over a base scheme `S`, each
recorded as the assertion that it is an isomorphism. All external products are taken over
`S`.

* `kunnethShriek` is the `!`-Künneth map
  `Ku_! : Rf_! (M₁ ⊠ M₂) ⟶ Rf_{1!} M₁ ⊠ Rf_{2!} M₂` for `f = f₁ × f₂`, which is
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the base
  `Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_S Y₂) ×_{Y₁ ×_S Y₂} (Y₁ ×_S X₂)`; it is an
  isomorphism *by construction*, being built out of isomorphisms. For a finite coefficient
  ring this is proved, from the relative product theorem and compact-support base change, as
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct`;
* `exceptional` is the exceptional Künneth map
  `α : Rf₁^! N₁ ⊠ Rf₂^! N₂ ⟶ Rf^! (N₁ ⊠ N₂)`, the exceptional adjoint of `Ku_!` followed by
  the two counits of `Rf_{i!} ⊣ Rf_i^!`;
* `externalHom` is the external Hom map
  `β : RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ⟶ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`, the tensor–Hom transpose of
  the two evaluation maps;
* `kunnethVerdier` is the Künneth–Verdier map
  `κ : M ⊠ 𝔻_Y N ⟶ RHom(p_Y^* N, Rp_X^! M)` on `X ×_S Y`, the composite of `β` applied to the
  pairs `(Λ_X, M)` and `(N, ω_Y)` with `RHom(1, α)` for `id_X × a_Y`, using the unit
  identifications `RHom(Λ_X, M) = M` and `Λ_X ⊠ N = p_Y^* N`.

Only `Ku_!` is built from isomorphisms; that `α`, `β` and `κ` are invertible is the content of
`AlgebraicGeometry.Etale.hasKunnethComparisons`, i.e. of `lemma-external-duality-trace-morphism`,
which holds over a field for finite coefficients of invertible exponent. Over a more general base
the comparisons fail: over `S = 𝔸¹_k`, with `E₁ = E₂ = i_*Λ` the skyscraper at the origin and
`N₁ = N₂ = Λ_S`, the source of `β` is `i_*Λ(-2)[-4]` and its target `i_*Λ(-1)[-2]`. -/
structure HasKunnethComparisons (S : Scheme.{u}) : Prop where
  /-- The `!`-Künneth map `Ku_!` is an isomorphism. -/
  kunnethShriek : ∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
      [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
      [QuasiCompact f₁] [QuasiCompact f₂]
      [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
      {M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      {M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₁ M₁ →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₂ M₂ →
      Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![ModuleCat.{u + 1} Λ]).obj
          (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
        externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ ((R(f₁)_![ModuleCat.{u + 1} Λ]).obj M₁)
            ((R(f₂)_![ModuleCat.{u + 1} Λ]).obj M₂))
  /-- The exceptional Künneth map `α` is an isomorphism. -/
  exceptional : ∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
      [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
      [QuasiCompact f₁] [QuasiCompact f₂]
      [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
      {N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      {N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₁ N₁ →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₂ N₂ →
      Nonempty (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂)
          ((R(f₁)^![Λ]).obj N₁) ((R(f₂)^![Λ]).obj N₂) ≅
        (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![Λ]).obj (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂
            N₁ N₂))
  /-- The external Hom map `β` is an isomorphism. -/
  externalHom : ∀ {Z₁ Z₂ : Scheme.{u}} (c₁ : Z₁ ⟶ S) (c₂ : Z₂ ⟶ S)
      [IsSeparated c₁] [LocallyOfFiniteType c₁] [QuasiCompact c₁]
      [IsSeparated c₂] [LocallyOfFiniteType c₂] [QuasiCompact c₂]
      {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ E₁ →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ E₂ →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ N₁ →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ N₂ →
      Nonempty (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ ((RHom(Z₁)[ModuleCat.{u + 1} Λ].obj (op
          E₁)).obj N₁)
          ((RHom(Z₂)[ModuleCat.{u + 1} Λ].obj (op E₂)).obj N₂) ≅
        (RHom(pullback c₁ c₂)[ModuleCat.{u + 1} Λ].obj (op (externalProduct (ModuleCat.{u + 1} Λ) c₁
            c₂ E₁ E₂))).obj
          (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ N₁ N₂))
  /-- The Künneth–Verdier map `κ` is an isomorphism. -/
  kunnethVerdier : ∀ {X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
      [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
      [HasCompactification b] [QuasiCompact b] [HasCompactification (pullback.fst a b)]
      {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N →
      Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M ((verdierDual Λ b).obj (op N)) ≅
        (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1}
            Λ])).obj N))).obj
          ((R(pullback.fst a b)^![Λ]).obj M))

omit [HasSmallSiteSheafify A] in
/-- The external Hom map `β` of `AlgebraicGeometry.Etale.HasKunnethComparisons` is an isomorphism
for **dualizable** `E₁`, `E₂`:
`RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ≅ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`. The derived pullbacks are monoidal and
preserve duals, and internal homs out of dualizable objects are tensor products with the duals
(`CategoryTheory.nonempty_iso_tensorObj_map_ihom_obj`). Over a field, constructible complexes of
finite Tor amplitude are dualizable only where they are lisse, so this is the lisse case of the
`externalHom` clause. -/
theorem nonempty_iso_externalProduct_derivedHom_of_isDualizable [UpperStarPreservesFlat A]
    {S Z₁ Z₂ : Scheme.{u}} (c₁ : Z₁ ⟶ S) (c₂ : Z₂ ⟶ S)
    {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology A)}
    {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology A)}
    (h₁ : IsDualizable E₁) (h₂ : IsDualizable E₂) :
    Nonempty (externalProduct A c₁ c₂ ((RHom(Z₁)[A].obj (op E₁)).obj N₁)
        ((RHom(Z₂)[A].obj (op E₂)).obj N₂) ≅
      (RHom(pullback c₁ c₂)[A].obj (op (externalProduct A c₁ c₂ E₁ E₂))).obj
        (externalProduct A c₁ c₂ N₁ N₂)) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf Z₁.smallEtaleTopology A)
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf Z₂.smallEtaleTopology A)
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (pullback c₁ c₂).smallEtaleTopology A)
  let _ := leftDerivedUpperStarMonoidal A (pullback.fst c₁ c₂)
  let _ := leftDerivedUpperStarMonoidal A (pullback.snd c₁ c₂)
  exact nonempty_iso_tensorObj_map_ihom_obj (L((pullback.fst c₁ c₂)^*[A]))
    (L((pullback.snd c₁ c₂)^*[A])) h₁ h₂

/-- The product `f₁ ×_S f₂` of two open immersions over `S` is an open immersion: it is the
composite of the base changes `X₁ ×_S f₂` and `f₁ ×_S Y₂`. -/
lemma isOpenImmersion_mapOverBase {S X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [IsOpenImmersion f₁] [IsOpenImmersion f₂] :
    IsOpenImmersion (pullback.mapOverBase f₁ f₂ b₁ b₂) := by
  have h : pullbackMapRight (f₁ ≫ b₁) b₂ f₂ ≫ pullbackMapLeft b₁ b₂ f₁ =
      pullback.mapOverBase f₁ f₂ b₁ b₂ := by
    apply pullback.hom_ext <;> simp
  have : IsOpenImmersion (pullbackMapLeft b₁ b₂ f₁) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_pullbackMapLeft b₁ b₂ f₁) inferInstance
  have : IsOpenImmersion (pullbackMapRight (f₁ ≫ b₁) b₂ f₂) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_pullbackMapRight (f₁ ≫ b₁) b₂ f₂) inferInstance
  rw [← h]
  infer_instance

/-- The exceptional Künneth map `α` of `AlgebraicGeometry.Etale.HasKunnethComparisons` is an
isomorphism for **open immersions** `f₁`, `f₂` (quasi-compact, finite coefficients):
`Rf₁^! N₁ ⊠ Rf₂^! N₂ ≅ R(f₁ × f₂)^! (N₁ ⊠ N₂)`. For a quasi-compact open immersion the exceptional
inverse image is the restriction
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion`), and `f₁ × f₂` is again
an open immersion, so this is the compatibility of the external product with pullbacks
(`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_externalProduct_of_comp`).
This is the étale-local case through which the blueprint proof
(`proposition-exceptional-external-kunneth--1`) reduces lisse coefficients to constant ones. -/
theorem nonempty_iso_externalProduct_rightDerivedUpperShriek_of_isOpenImmersion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {S X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification f₁] [HasCompactification f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    [QuasiCompact (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    (N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂)
        ((R(f₁)^![Λ]).obj N₁) ((R(f₂)^![Λ]).obj N₂) ≅
      (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ N₁ N₂)) := by
  have := isOpenImmersion_mapOverBase b₁ b₂ f₁ f₂
  let ψ := pullback.mapOverBase f₁ f₂ b₁ b₂
  let e (Z W : Scheme.{u}) (j : Z ⟶ W) [IsOpenImmersion j] [QuasiCompact j]
      [HasCompactification j] :
      R(j)^![Λ] ≅ L((j)^*[ModuleCat.{u + 1} Λ]) :=
    rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory _ j).symm
  obtain ⟨p⟩ := nonempty_iso_leftDerivedUpperStar_externalProduct_of_comp
    (ModuleCat.{u + 1} Λ) b₁ b₂ (f₁ ≫ b₁) (f₂ ≫ b₂) f₁ f₂ ψ (by simp [ψ]) (by simp [ψ]) N₁ N₂
  exact ⟨((derivedTensor _ _).mapIso ((L((pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂))^*[_])).mapIso
      ((e _ _ f₁).app N₁))).app _ ≪≫
    ((derivedTensor _ _).obj _).mapIso ((L((pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂))^*[_])).mapIso
      ((e _ _ f₂).app N₂)) ≪≫ p.symm ≪≫ ((e _ _ ψ).app _).symm⟩

/-- The Künneth–Verdier map `κ` of `AlgebraicGeometry.Etale.HasKunnethComparisons` for a
**dualizable** `N` reduces to the case `N = Λ_Y`: given `M ⊠ ω_Y ≅ Rp_X^! M`,
`M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`. Indeed `𝔻_Y N = RHom(N, ω_Y) ≅ N^∨ ⊗ ω_Y` and
`RHom(p_Y^* N, -) ≅ p_Y^* N^∨ ⊗ -` (`CategoryTheory.nonempty_iso_tensorObj_map_ihom_obj_right`).
The remaining case `M ⊠ ω_Y ≅ Rp_X^! M` is the exceptional Künneth map for `𝟙_X × b`, which
is how the blueprint proof of `lemma-external-duality-trace-morphism--1` uses
`proposition-exceptional-external-kunneth--1`. -/
theorem nonempty_iso_externalProduct_verdierDual_of_isDualizable [UpperStarPreservesFlat
    (ModuleCat.{u + 1} Λ)]
    {S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) [HasCompactification b]
 [HasCompactification (pullback.fst a b)]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hN :
        IsDualizable N)
    (h : Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M (dualizingComplex Λ b) ≅
      (R(pullback.fst a b)^![Λ]).obj M)) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M ((verdierDual Λ b).obj (Opposite.op N)) ≅
      (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj (Opposite.op ((L((pullback.snd a
          b)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
        ((R(pullback.fst a b)^![Λ]).obj M)) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (pullback a b).smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let _ := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) (pullback.fst a b)
  let _ := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) (pullback.snd a b)
  obtain ⟨e⟩ := nonempty_iso_tensorObj_map_ihom_obj_right (L((pullback.fst a b)^*[ModuleCat.{u + 1}
      Λ]))
    (L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])) M (dualizingComplex Λ b) hN
  obtain ⟨h⟩ := h
  exact ⟨e ≪≫ (ihom ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N)).mapIso h⟩

end Etale

end AlgebraicGeometry
