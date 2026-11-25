/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs

/-!

# Künneth–Verdier comparisons from duality of external products

Over a field `k`, for a finite coefficient ring `Λ` of invertible exponent, and with Verdier
biduality (`sk-prop-sf-biduality-general`), the three non-formal product comparisons of
`lemma-external-duality-trace-morphism` — the exceptional Künneth map `α`, the external Hom map `β`
and the Künneth–Verdier map `κ` — reduce formally to the single statement that Verdier duality
commutes with external products,

`𝔻_{X ×_k Y} (P ⊠ Q) ≅ 𝔻_X P ⊠ 𝔻_Y Q`

for `P ∈ Dctf(X, Λ)`, `Q ∈ Dctf(Y, Λ)` on separated finite-type `k`-schemes
(`sk-rem-sf-kv-formal`, `rem-sf-kv-formal`). This file carries out that reduction at the level
of the existence of isomorphisms.

## Main definitions

- `AlgebraicGeometry.Etale.externalProductMapIso`: functoriality of `⊠` in isomorphisms.
- `AlgebraicGeometry.Etale.derivedHomVerdierDualIso`: `RHom(K, 𝔻N) ≅ 𝔻(N ⊗ᴸ K)`.
- `AlgebraicGeometry.Etale.VerdierDualExternalProduct`: the statement
  `𝔻(P ⊠ Q) ≅ 𝔻P ⊠ 𝔻Q` over `Spec k`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_mapOverBase_externalProduct`:
  `L(f₁ × f₂)^* (L₁ ⊠ L₂) ≅ Lf₁^* L₁ ⊠ Lf₂^* L₂`.
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_derivedTensor`:
  `(K₁ ⊗ᴸ K₂) ⊠ (M₁ ⊗ᴸ M₂) ≅ (K₁ ⊠ M₁) ⊗ᴸ (K₂ ⊠ M₂)`.
- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar_obj`:
  `𝔻_X (Lf^* K) ≅ Rf^! (𝔻_Y K)`.
- `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedUpperShriek_fst`:
  `RHom(p_Y^* N, Rp_X^! M) ≅ 𝔻(𝔻M ⊠ N)`.
- `AlgebraicGeometry.Etale.VerdierDualExternalProduct.nonempty_iso_kunnethVerdier`,
  `AlgebraicGeometry.Etale.VerdierDualExternalProduct.nonempty_iso_externalHom`,
  `AlgebraicGeometry.Etale.VerdierDualExternalProduct.nonempty_iso_exceptional`: the maps
  `κ`, `β`, `α` of `lemma-external-duality-trace-morphism` are invertible if duality commutes with
  external products.

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

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {B X Y : Scheme.{u}}

/-- The external product `K ⊠ M` is functorial in isomorphisms of both factors. -/
noncomputable def externalProductMapIso (f : X ⟶ B) (g : Y ⟶ B)
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {M M' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e₁ : K ≅ K') (e₂ : M ≅ M') :
    externalProduct A f g K M ≅ externalProduct A f g K' M' :=
  ((derivedTensor A _).mapIso ((L((pullback.fst f g)^*[A])).mapIso e₁)).app _ ≪≫
    ((derivedTensor A _).obj _).mapIso ((L((pullback.snd f g)^*[A])).mapIso e₂)

/-- The internal tensor–Hom adjunction against a Verdier dual:
`RHom(K, 𝔻N) ≅ 𝔻(N ⊗ᴸ K)`, from `RHom(N ⊗ᴸ K, ω) ≅ RHom(K, RHom(N, ω))`. -/
noncomputable def derivedHomVerdierDualIso {S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]
 (K N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((verdierDual Λ a).obj (op N)) ≅
      (verdierDual Λ a).obj (op (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj N).obj K)) :=
  ((((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) (N ⊗ K)).ofNatIsoLeft (tensorLeftTensor N
      K)).rightAdjointUniq
    ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K).comp (derivedTensorHomAdjunction
        (ModuleCat.{u + 1} Λ) N))).app
      (dualizingComplex Λ a)).symm

variable [UpperStarPreservesFlat A]

/-- The external product is compatible with pullback along a product of morphisms: for
`fᵢ : Xᵢ ⟶ Yᵢ` over `S`,

`L(f₁ × f₂)^* (L₁ ⊠ L₂) ≅ Lf₁^* L₁ ⊠ Lf₂^* L₂`,

the left external product being taken over `S` along `bᵢ`, the right one along `fᵢ ≫ bᵢ`. -/
theorem nonempty_iso_leftDerivedUpperStar_mapOverBase_externalProduct
    {S X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (L₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology A))
    (L₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology A)) :
    Nonempty ((L((pullback.mapOverBase f₁ f₂ b₁ b₂)^*[A])).obj (externalProduct A b₁ b₂ L₁ L₂) ≅
      externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) ((L((f₁)^*[A])).obj L₁)
        ((L((f₂)^*[A])).obj L₂)) := by
  let F := pullback.mapOverBase f₁ f₂ b₁ b₂
  let pb₁ : (L((F)^*[A])).obj ((L((pullback.fst b₁ b₂)^*[A])).obj L₁) ≅
      (L((pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂))^*[A])).obj ((L((f₁)^*[A])).obj L₁) :=
    ((leftDerivedUpperStarComp A F (pullback.fst _ _)).app L₁).symm ≪≫
      (leftDerivedUpperStarComp A _ _ (F ≫ pullback.fst _ _) (by simp [F])).app L₁
  let pb₂ : (L((F)^*[A])).obj ((L((pullback.snd b₁ b₂)^*[A])).obj L₂) ≅
      (L((pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂))^*[A])).obj ((L((f₂)^*[A])).obj L₂) :=
    ((leftDerivedUpperStarComp A F (pullback.snd _ _)).app L₂).symm ≪≫
      (leftDerivedUpperStarComp A _ _ (F ≫ pullback.snd _ _) (by simp [F])).app L₂
  exact ⟨leftDerivedUpperStarTensorIso A F _ _ ≪≫ ((derivedTensor A _).mapIso pb₁).app _ ≪≫
    ((derivedTensor A _).obj _).mapIso pb₂⟩

/-- The external product is compatible with the derived tensor product (the middle-four
interchange): `(K₁ ⊗ᴸ K₂) ⊠ (M₁ ⊗ᴸ M₂) ≅ (K₁ ⊠ M₁) ⊗ᴸ (K₂ ⊠ M₂)`. -/
theorem nonempty_iso_externalProduct_derivedTensor (f : X ⟶ B) (g : Y ⟶ B)
    (K₁ K₂ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M₁ M₂ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Nonempty (externalProduct A f g (((-⊗ᴸ-(X)[A]).obj K₁).obj K₂)
        (((-⊗ᴸ-(Y)[A]).obj M₁).obj M₂) ≅
      ((-⊗ᴸ-(pullback f g)[A]).obj (externalProduct A f g K₁ M₁)).obj
        (externalProduct A f g K₂ M₂)) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (pullback f g).smallEtaleTopology A)
  exact ⟨tensorIso (leftDerivedUpperStarTensorIso A (pullback.fst f g) K₁ K₂)
      (leftDerivedUpperStarTensorIso A (pullback.snd f g) M₁ M₂) ≪≫
    ⟨tensorμ _ _ _ _, tensorδ _ _ _ _, tensorμ_tensorδ _ _ _ _, tensorδ_tensorμ _ _ _ _⟩⟩

end Generic

section Field

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The Verdier dual of a pullback is the exceptional pullback of the Verdier dual:
for `f : X ⟶ Y` over `S`, with structure morphisms `a_Y` and `a_X = f ≫ a_Y`,

`𝔻_X (Lf^* K) ≅ Rf^! (𝔻_Y K)`.

It combines `Rf^! RHom(K, ω_Y) ≅ RHom(Lf^* K, Rf^! ω_Y)`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedHom`) with
`Rf^! ω_Y ≅ ω_X` (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex`).
-/
theorem nonempty_iso_verdierDual_leftDerivedUpperStar_obj {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (aY : Y ⟶ S) (aX : X ⟶ S) (h : f ≫ aY = aX) [HasCompactification f]
    [HasCompactification aY] [HasCompactification aX] [QuasiCompact aX]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((verdierDual Λ aX).obj
        (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (R(f)^![Λ]).obj ((verdierDual Λ aY).obj (op K))) := by
  subst h
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_derivedHom Λ f K (dualizingComplex _ aY)
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ f aY
  exact ⟨((RHom(X)[ModuleCat.{u + 1} Λ]).obj _).mapIso e₂.symm ≪≫ e₁.symm⟩

/-- The external product of two objects of `Dctf` lies in `Dctf`. -/
theorem constructibleFiniteTor_externalProduct {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y M) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) (pullback f g)
      (externalProduct (ModuleCat.{u + 1} Λ) f g K M) :=
  constructibleFiniteTor_tensor Λ _ (constructibleFiniteTor_leftDerivedUpperStar _ _ hK)
    (constructibleFiniteTor_leftDerivedUpperStar _ _ hM)

/-- Verdier duality commutes with external products over a field `k` (`sk-rem-sf-kv-formal`,
`rem-sf-kv-formal`): for separated finite-type `k`-schemes `X`, `Y` and `P ∈ Dctf(X, Λ)`,
`Q ∈ Dctf(Y, Λ)`,

`𝔻_{X ×_k Y} (P ⊠ Q) ≅ 𝔻_X P ⊠ 𝔻_Y Q`.

At `P = Λ_X`, `Q = Λ_Y` this is `ω_{X ×_k Y} ≅ ω_X ⊠ ω_Y`. The three product comparisons
`α`, `β`, `κ` of `lemma-external-duality-trace-morphism` follow from it formally, given biduality
(`AlgebraicGeometry.Etale.VerdierDualExternalProduct.nonempty_iso_kunnethVerdier`, ...). -/
structure VerdierDualExternalProduct (k : Type u) [Field k] : Prop where
  /-- `𝔻(P ⊠ Q) ≅ 𝔻P ⊠ 𝔻Q` for `P ∈ Dctf(X, Λ)`, `Q ∈ Dctf(Y, Λ)`. -/
  nonempty_iso : ∀ ⦃X Y : Scheme.{u}⦄ (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    ⦃P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))⦄
    ⦃Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))⦄,
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X P →
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y Q →
    Nonempty ((verdierDual Λ (pullback.fst a b ≫ a)).obj
        (op (externalProduct (ModuleCat.{u + 1} Λ) a b P Q)) ≅
      externalProduct (ModuleCat.{u + 1} Λ) a b ((verdierDual Λ a).obj (op P))
        ((verdierDual Λ b).obj (op Q)))

/-- Blueprint `sk-rem-sf-kv-formal`, `rem-sf-kv-formal`: the formal rewriting of the target of
`κ`. For separated finite-type `k`-schemes `X`, `Y`, `M ∈ Dctf(X, Λ)` and any `N` on `Y`,

`RHom(p_Y^* N, Rp_X^! M) ≅ 𝔻_{X ×_k Y}(𝔻_X M ⊠ N)`.

By biduality (`sk-prop-sf-biduality-general`) and duality against pullback
(`lemma-internal-adjunction-two-exchange-formulas--3`),
`Rp_X^! M ≅ Rp_X^! 𝔻_X 𝔻_X M ≅ 𝔻(p_X^* 𝔻_X M)`, and the internal adjunction
`RHom(A, 𝔻 C) ≅ 𝔻(C ⊗ᴸ A)` (`AlgebraicGeometry.Etale.derivedHomVerdierDualIso`) with `A = p_Y^* N`,
`C = p_X^* 𝔻_X M` concludes. -/
theorem nonempty_iso_derivedHom_rightDerivedUpperShriek_fst {k : Type u} [Field k]
    [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] [HasCompactification b] [QuasiCompact b]
    [HasCompactification (pullback.fst a b)]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj
          (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
        ((R(pullback.fst a b)^![Λ]).obj M) ≅
      (verdierDual Λ (pullback.fst a b ≫ a)).obj
        (op (externalProduct (ModuleCat.{u + 1} Λ) a b
          ((verdierDual Λ a).obj (op M)) N))) := by
  obtain ⟨e₁⟩ := nonempty_iso_verdierDual_verdierDual Λ a hM
  obtain ⟨e₂⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar_obj Λ (pullback.fst a b) a
    (pullback.fst a b ≫ a) rfl ((verdierDual Λ a).obj (op M))
  exact ⟨((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).obj _).mapIso
      ((R(pullback.fst a b)^![Λ]).mapIso e₁ ≪≫ e₂.symm) ≪≫
    derivedHomVerdierDualIso _ (pullback.fst a b ≫ a) _ _⟩

namespace VerdierDualExternalProduct

variable {Λ} {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  (hδ : VerdierDualExternalProduct Λ k)
include hδ

/-- The Künneth–Verdier comparison `κ` (`lemma-external-duality-trace-morphism` (iv)) is invertible
if Verdier duality commutes with external products: for `M ∈ Dctf(X, Λ)` and `N ∈ Dctf(Y, Λ)`,

`M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`.

Indeed `RHom(p_Y^* N, Rp_X^! M) ≅ 𝔻(𝔻M ⊠ N)`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedUpperShriek_fst`), and
`𝔻(𝔻M ⊠ N) ≅ 𝔻𝔻M ⊠ 𝔻N ≅ M ⊠ 𝔻N`. -/
theorem nonempty_iso_kunnethVerdier {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (b : Y ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification b] [QuasiCompact b] [HasCompactification (pullback.fst a b)]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M)
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M
        ((verdierDual Λ b).obj (op N)) ≅
      (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj
          (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
        ((R(pullback.fst a b)^![Λ]).obj M)) := by
  obtain ⟨e₁⟩ := nonempty_iso_verdierDual_verdierDual Λ a hM
  obtain ⟨e₂⟩ := nonempty_iso_derivedHom_rightDerivedUpperShriek_fst Λ a b hM N
  obtain ⟨e₃⟩ := hδ.nonempty_iso a b (constructibleFiniteTor_verdierDual Λ a hM) hN
  exact ⟨externalProductMapIso _ a b e₁ (Iso.refl _) ≪≫ e₃.symm ≪≫ e₂.symm⟩

/-- The external Hom comparison `β` (`lemma-external-duality-trace-morphism` (iii)) is invertible if
Verdier duality commutes with external products:

`RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ≅ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`.

Indeed `RHom(E, N) ≅ 𝔻(𝔻N ⊗ᴸ E)` by biduality, and
`(𝔻N₁ ⊗ᴸ E₁) ⊠ (𝔻N₂ ⊗ᴸ E₂) ≅ (𝔻N₁ ⊠ 𝔻N₂) ⊗ᴸ (E₁ ⊠ E₂) ≅ 𝔻(N₁ ⊠ N₂) ⊗ᴸ (E₁ ⊠ E₂)`. -/
theorem nonempty_iso_externalHom {Z₁ Z₂ : Scheme.{u}} (c₁ : Z₁ ⟶ Spec (.of k))
    (c₂ : Z₂ ⟶ Spec (.of k))
    [IsSeparated c₁] [LocallyOfFiniteType c₁] [QuasiCompact c₁]
    [IsSeparated c₂] [LocallyOfFiniteType c₂] [QuasiCompact c₂]
    {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ E₁)
    (hE₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ E₂)
    (hN₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ N₁)
    (hN₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ N₂) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂
        ((RHom(Z₁)[ModuleCat.{u + 1} Λ].obj (op E₁)).obj N₁)
        ((RHom(Z₂)[ModuleCat.{u + 1} Λ].obj (op E₂)).obj N₂) ≅
      (RHom(pullback c₁ c₂)[ModuleCat.{u + 1} Λ].obj
          (op (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ E₁ E₂))).obj
        (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ N₁ N₂)) := by
  obtain ⟨b₁⟩ := nonempty_iso_verdierDual_verdierDual Λ c₁ hN₁
  obtain ⟨b₂⟩ := nonempty_iso_verdierDual_verdierDual Λ c₂ hN₂
  have hDN₁ := constructibleFiniteTor_verdierDual Λ c₁ hN₁
  have hDN₂ := constructibleFiniteTor_verdierDual Λ c₂ hN₂
  have hT₁ := constructibleFiniteTor_tensor Λ _ hDN₁ hE₁
  have hT₂ := constructibleFiniteTor_tensor Λ _ hDN₂ hE₂
  have hNN := constructibleFiniteTor_externalProduct Λ c₁ c₂ hN₁ hN₂
  obtain ⟨b₃⟩ := nonempty_iso_verdierDual_verdierDual Λ (pullback.fst c₁ c₂ ≫ c₁) hNN
  obtain ⟨e₃⟩ := hδ.nonempty_iso c₁ c₂ hT₁ hT₂
  obtain ⟨e₄⟩ := nonempty_iso_externalProduct_derivedTensor (ModuleCat.{u + 1} Λ) c₁ c₂
    ((verdierDual Λ c₁).obj (op N₁)) E₁
    ((verdierDual Λ c₂).obj (op N₂)) E₂
  obtain ⟨e₅⟩ := hδ.nonempty_iso c₁ c₂ hN₁ hN₂
  exact ⟨externalProductMapIso _ c₁ c₂
      (((RHom(Z₁)[ModuleCat.{u + 1} Λ]).obj _).mapIso b₁ ≪≫ derivedHomVerdierDualIso _ c₁ _ _)
      (((RHom(Z₂)[ModuleCat.{u + 1} Λ]).obj _).mapIso b₂ ≪≫ derivedHomVerdierDualIso _ c₂ _ _) ≪≫
    e₃.symm ≪≫ (verdierDual Λ (pullback.fst c₁ c₂ ≫ c₁)).mapIso e₄.symm.op ≪≫
    (verdierDual Λ (pullback.fst c₁ c₂ ≫ c₁)).mapIso
      (((-⊗ᴸ-(pullback c₁ c₂)[ModuleCat.{u + 1} Λ]).mapIso e₅).app _).op ≪≫
    (derivedHomVerdierDualIso _ (pullback.fst c₁ c₂ ≫ c₁) _ _).symm ≪≫
    ((RHom(pullback c₁ c₂)[ModuleCat.{u + 1} Λ]).obj _).mapIso b₃.symm⟩

/-- The exceptional Künneth comparison `α` (`lemma-external-duality-trace-morphism` (ii)) is
invertible if Verdier duality commutes with external products: for `fᵢ : Xᵢ ⟶ Yᵢ` between separated
finite-type `k`-schemes and `Nᵢ ∈ Dctf(Yᵢ, Λ)`,

`Rf₁^! N₁ ⊠ Rf₂^! N₂ ≅ R(f₁ × f₂)^! (N₁ ⊠ N₂)`.

Indeed `Rfᵢ^! Nᵢ ≅ 𝔻(Lfᵢ^* 𝔻Nᵢ)` by biduality, and
`L(f₁ × f₂)^* (𝔻N₁ ⊠ 𝔻N₂) ≅ Lf₁^* 𝔻N₁ ⊠ Lf₂^* 𝔻N₂`. -/
theorem nonempty_iso_exceptional {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ Spec (.of k))
    (b₂ : Y₂ ⟶ Spec (.of k)) [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    [IsSeparated b₂] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
    [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    {N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₁ N₁)
    (hN₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₂ N₂) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂)
        ((R(f₁)^![Λ]).obj N₁) ((R(f₂)^![Λ]).obj N₂) ≅
      (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ N₁ N₂)) := by
  obtain ⟨b₁'⟩ := nonempty_iso_verdierDual_verdierDual Λ b₁ hN₁
  obtain ⟨b₂'⟩ := nonempty_iso_verdierDual_verdierDual Λ b₂ hN₂
  have hDN₁ := constructibleFiniteTor_verdierDual Λ b₁ hN₁
  have hDN₂ := constructibleFiniteTor_verdierDual Λ b₂ hN₂
  obtain ⟨p₁⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar_obj Λ f₁ b₁ (f₁ ≫ b₁) rfl
    ((verdierDual Λ b₁).obj (op N₁))
  obtain ⟨p₂⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar_obj Λ f₂ b₂ (f₂ ≫ b₂) rfl
    ((verdierDual Λ b₂).obj (op N₂))
  have hP₁ := constructibleFiniteTor_leftDerivedUpperStar _ f₁ hDN₁
  have hP₂ := constructibleFiniteTor_leftDerivedUpperStar _ f₂ hDN₂
  obtain ⟨e₃⟩ := hδ.nonempty_iso (f₁ ≫ b₁) (f₂ ≫ b₂) hP₁ hP₂
  obtain ⟨e₄⟩ := nonempty_iso_leftDerivedUpperStar_mapOverBase_externalProduct
    (ModuleCat.{u + 1} Λ) b₁ b₂ f₁ f₂ ((verdierDual Λ b₁).obj (op N₁))
    ((verdierDual Λ b₂).obj (op N₂))
  obtain ⟨e₅⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar_obj Λ
    (pullback.mapOverBase f₁ f₂ b₁ b₂) (pullback.fst b₁ b₂ ≫ b₁)
    (pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂) ≫ f₁ ≫ b₁)
    (by simp [-pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase])
    (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂
      ((verdierDual Λ b₁).obj (op N₁))
      ((verdierDual Λ b₂).obj (op N₂)))
  obtain ⟨e₆⟩ := hδ.nonempty_iso b₁ b₂ hDN₁ hDN₂
  exact ⟨externalProductMapIso _ (f₁ ≫ b₁) (f₂ ≫ b₂)
      ((R(f₁)^![Λ]).mapIso b₁' ≪≫ p₁.symm)
      ((R(f₂)^![Λ]).mapIso b₂' ≪≫ p₂.symm) ≪≫ e₃.symm ≪≫
    (verdierDual Λ (pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂) ≫ f₁ ≫ b₁)).mapIso
      e₄.op ≪≫ e₅ ≪≫
    (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![Λ]).mapIso
      (e₆ ≪≫ externalProductMapIso _ b₁ b₂ b₁'.symm b₂'.symm)⟩

end VerdierDualExternalProduct

/-- The Künneth–Verdier statement over a field `k` (`lemma-external-duality-trace-morphism--1`, the
`κ` of `lemma-external-duality-trace-morphism` (iv)): for separated finite-type `k`-schemes `X`,
`Y`, with projections `p_X`, `p_Y` of `X ×_k Y`, and `M ∈ Dctf(X, Λ)`, `N ∈ Dctf(Y, Λ)`,

`M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`. -/
structure KunnethVerdier (k : Type u) [Field k] : Prop where
  /-- `M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)` for `M ∈ Dctf(X, Λ)`, `N ∈ Dctf(Y, Λ)`. -/
  nonempty_iso : ∀ ⦃X Y : Scheme.{u}⦄ (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    ⦃M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))⦄
    ⦃N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))⦄,
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N →
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M
        ((verdierDual Λ b).obj (op N)) ≅
      (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj
          (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
        ((R(pullback.fst a b)^![Λ]).obj M))

variable {Λ} {k : Type u} [Field k]

/-- Blueprint `sk-rem-sf-kv-formal`, `rem-sf-kv-formal` (the converse direction): the
Künneth–Verdier isomorphism implies that Verdier duality commutes with external products.

For `P ∈ Dctf(X, Λ)` and `Q ∈ Dctf(Y, Λ)`, the internal adjunction and duality against
pullback (`lemma-internal-adjunction-two-exchange-formulas--3`) give
`𝔻(P ⊠ Q) ≅ RHom(p_Y^* Q, 𝔻(p_X^* P)) ≅ RHom(p_Y^* Q, Rp_X^! 𝔻P)`, and `κ` for the pair
`(𝔻P, Q)` identifies the latter with `𝔻P ⊠ 𝔻Q`. Biduality is not needed in this direction,
only that `𝔻_X` preserves `Dctf` (`sk-prop-sf-biduality-general`). -/
theorem KunnethVerdier.verdierDualExternalProduct [PerfectField k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    (h : KunnethVerdier Λ k) : VerdierDualExternalProduct Λ k := by
  refine ⟨fun X Y a b _ _ _ _ _ _ P Q hP hQ ↦ ?_⟩
  obtain ⟨e₁⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar_obj Λ (pullback.fst a b) a
    (pullback.fst a b ≫ a) rfl P
  obtain ⟨e₂⟩ := h.nonempty_iso a b (constructibleFiniteTor_verdierDual Λ a hP) hQ
  exact ⟨(derivedHomVerdierDualIso _ (pullback.fst a b ≫ a) _ _).symm ≪≫
    ((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).obj _).mapIso e₁ ≪≫ e₂.symm⟩

/-- Blueprint `sk-rem-sf-kv-formal`, `rem-sf-kv-formal`: Künneth–Verdier is formally duality of
external products.

Over a field `k`, for a finite coefficient ring `Λ` of invertible exponent, the Künneth–Verdier
isomorphism `M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)` (`lemma-external-duality-trace-morphism--1`) holds
for all `M ∈ Dctf(X, Λ)`, `N ∈ Dctf(Y, Λ)` if and only if Verdier duality commutes with external
products, `𝔻_{X ×_k Y} (P ⊠ Q) ≅ 𝔻_X P ⊠ 𝔻_Y Q`. The forward implication is
`AlgebraicGeometry.Etale.KunnethVerdier.verdierDualExternalProduct`; the backward one,
`AlgebraicGeometry.Etale.VerdierDualExternalProduct.nonempty_iso_kunnethVerdier`, uses
biduality (`sk-prop-sf-biduality-general`) to write `Rp_X^! M ≅ 𝔻(p_X^* 𝔻M)`. -/
theorem verdierDualExternalProduct_iff_kunnethVerdier [IsAlgClosed k]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    VerdierDualExternalProduct Λ k ↔ KunnethVerdier Λ k :=
  ⟨fun h ↦ ⟨fun _ _ a b _ _ _ _ _ _ _ _ hM hN ↦ h.nonempty_iso_kunnethVerdier a b hM hN⟩,
    KunnethVerdier.verdierDualExternalProduct⟩

end Field

end Etale

end AlgebraicGeometry
