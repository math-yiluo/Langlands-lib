/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.DualReduction
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek
public import WeilConjectures.SixFunctors.Etale.Derived.PointDualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual

/-!

# The Künneth–Verdier isomorphism

Over a field `k`, for a finite coefficient ring `Λ` whose exponent is invertible in `k`, and
for separated finite-type `k`-schemes `X`, `Y` with projections `p_X`, `p_Y` of `X ×_k Y`, the
Künneth–Verdier isomorphism (`lemma-external-duality-trace-morphism--1`) reads

`κ : M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`

for `M ∈ Dctf(X, Λ)`, `N ∈ Dctf(Y, Λ)`. As in the blueprint it is the external Hom isomorphism
`β` (`lemma-external-duality-trace-morphism--1`) for the pairs `(Λ_X, M)` and `(N, ω_Y)`, followed
by the exceptional Künneth isomorphism `α` (`proposition-exceptional-external-kunneth--1`) for
`𝟙_X × a_Y`, which reads `M ⊠ ω_Y ≅ Rp_X^! M`.

## Main statements

- `AlgebraicGeometry.Etale.verdierDual_obj`, `AlgebraicGeometry.Etale.dualizingComplex_eq`
  (`definition-verdier-dual-evaluation`): `𝔻_X = RHom(-, ω_X)` and `ω_X = Ra^! Λ_S`.
- `AlgebraicGeometry.Etale.nonempty_iso_externalHom` (`lemma-external-duality-trace-morphism--1`):
`β` as an
  isomorphism, from `AlgebraicGeometry.Etale.isIso_externalHomMap`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_pullbackFst`: `α` for
  `𝟙_X × a_Y`, `Rp_X^! M ≅ M ⊠ ω_Y`.
- `AlgebraicGeometry.Etale.nonempty_iso_kunnethVerdier`
(`lemma-external-duality-trace-morphism--1`): `κ`.
- `AlgebraicGeometry.Etale.kunnethVerdier`, `AlgebraicGeometry.Etale.verdierDualExternalProduct`
  (`rem-sf-kv-formal`): `κ` and its formal equivalent `𝔻(P ⊠ Q) ≅ 𝔻P ⊠ 𝔻Q`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `definition-verdier-dual-evaluation`: Dualizing complex and Verdier dual.

For `a : X ⟶ S`, the dualizing complex is `ω_X = Ra^! Λ_S`
(`AlgebraicGeometry.Etale.dualizingComplex`, see
`AlgebraicGeometry.Etale.dualizingComplex_eq`), the Verdier dual is `𝔻_X = RHom(-, ω_X)`
(`AlgebraicGeometry.Etale.verdierDual`), and the evaluation `ev_M : M ⊗ᴸ 𝔻_X M ⟶ ω_X` is the
counit of the tensor–internal-Hom adjunction (`AlgebraicGeometry.Etale.verdierDualEvaluation`).
(The blueprint writes the two factors in the other order, `𝔻_X M ⊗ᴸ M`; the internal Hom of the
library is right adjoint to tensoring on the left.) -/
theorem verdierDual_obj {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (verdierDual _ a).obj (op M) =
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op M)).obj (dualizingComplex _ a) :=
  rfl

/-- Blueprint `definition-verdier-dual-evaluation`: the dualizing complex of `a : X ⟶ S` is
`ω_X = Ra^! Λ_S`. -/
theorem dualizingComplex_eq {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a] :
    dualizingComplex Λ a = (R(a)^![Λ]).obj (𝟙_ _) :=
  rfl

/-- The internal hom out of the unit is the identity, `RHom(Λ_X, -) ≅ 𝟭`: both are right
adjoint to `Λ_X ⊗ᴸ - ≅ 𝟭`. -/
noncomputable def derivedHomUnitIso (X : Scheme.{u}) :
    (RHom(X)[ModuleCat.{u + 1} Λ]).obj (op (𝟙_ _)) ≅ 𝟭 _ :=
  (derivedTensorHomAdjunction _ (𝟙_ _)).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft (derivedTensorLeftUnitorNatIso _ X).symm)

/-- The external product with the unit in the first factor is the pullback of the second factor:
`Λ_X ⊠ N ≅ p_Y^* N`. -/
noncomputable def externalProductUnitLeftIso {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    externalProduct (ModuleCat.{u + 1} Λ) f g (𝟙_ _) N ≅
      (L((pullback.snd f g)^*[ModuleCat.{u + 1} Λ])).obj N :=
  ((derivedTensor _ _).mapIso (leftDerivedUpperStarUnitIso _ (pullback.fst f g))).app _ ≪≫
    derivedTensorLeftUnitor _ _ _

variable {k : Type u} [Field k]

/-- Blueprint `lemma-external-duality-trace-morphism--1`: External Hom; the `β` map, as an
isomorphism `RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ≅ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`
(`AlgebraicGeometry.Etale.isIso_externalHomMap`). -/
theorem nonempty_iso_externalHom [HasInvertibleExponent Λ (Spec (.of k))] {Z₁ Z₂ : Scheme.{u}}
    (c₁ : Z₁ ⟶ Spec (.of k)) (c₂ : Z₂ ⟶ Spec (.of k))
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
        (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ N₁ N₂)) :=
  have := isIso_externalHomMap Λ c₁ c₂ hE₁ hE₂ hN₁ hN₂
  ⟨asIso (externalHomMap (ModuleCat.{u + 1} Λ) c₁ c₂ E₁ N₁ E₂ N₂)⟩

/-- The exceptional Künneth isomorphism `α` for `𝟙_X × b`: for `a : X ⟶ Spec k` of finite type,
`b : Y ⟶ Spec k` and any `M`, with `p_X : X ×_k Y ⟶ X` the first projection,

`Rp_X^! M ≅ M ⊠ ω_Y`.

This is `α` (`proposition-exceptional-external-kunneth--1`) for `f₁ = 𝟙_X`, `f₂ = b` and the
coefficients `(M, Λ_k)`: the one-sided exceptional Künneth formula
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor`) for `b` and
`X = k ×_k X`, read through `La^* Λ_k ≅ Λ_X` and the unitors. -/
theorem nonempty_iso_rightDerivedUpperShriek_pullbackFst
    [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification b] [QuasiCompact b] [HasCompactification (pullback.fst a b)]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(pullback.fst a b)^![Λ]).obj M ≅
      externalProduct (ModuleCat.{u + 1} Λ) a b M (dualizingComplex _ b)) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_derivedTensor Λ (𝟙 (Spec (.of k))) a
    (IsPullback.id_vert a) b (IsPullback.of_hasPullback a b).flip (𝟙_ _) M
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) (pullback a b)
  exact ⟨(R(pullback.fst a b)^![Λ]).mapIso
      (((derivedTensor _ X).mapIso (leftDerivedUpperStarUnitIso _ a)).app _ ≪≫
        derivedTensorLeftUnitor _ _ _ ≪≫ (leftDerivedUpperStarId _ X).app M).symm ≪≫ e ≪≫
    ((derivedTensor _ _).obj _).mapIso (eqToIso (by rw [Category.comp_id])) ≪≫ (β.app _).app _⟩

/-- Blueprint `lemma-external-duality-trace-morphism--1`: Künneth–Verdier isomorphism; the `κ` map.

For `X`, `Y` separated of finite type over a field `k`, `Λ` finite of invertible exponent,
`M ∈ Dctf(X, Λ)` and `N ∈ Dctf(Y, Λ)`,

`κ : M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`.

As in the blueprint it is the external Hom isomorphism `β`
(`lemma-external-duality-trace-morphism--1`) for the pairs `(Λ_X, M)` and `(N, ω_Y)`, using the unit
identifications `RHom(Λ_X, M) ≅ M` and `Λ_X ⊠ N ≅ p_Y^* N`, followed by `RHom(1, α)` for the
identification `M ⊠ ω_Y ≅ Rp_X^! M` of `proposition-exceptional-external-kunneth--1`. -/
theorem nonempty_iso_kunnethVerdier [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] [HasCompactification b] [QuasiCompact b]
    [HasCompactification (pullback.fst a b)]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M)
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M
        ((verdierDual Λ b).obj (op N)) ≅
      (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj
          (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
        ((R(pullback.fst a b)^![Λ]).obj M)) := by
  have hω : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y (dualizingComplex _ b) :=
    constructibleFiniteTor_dualizingComplex Λ (𝟙 _) b (constructibleFiniteTor_unit Λ)
  obtain ⟨β⟩ := nonempty_iso_externalHom Λ a b (constructibleFiniteTor_unit Λ (X := X)) hN hM hω
  obtain ⟨α⟩ := nonempty_iso_rightDerivedUpperShriek_pullbackFst Λ a b M
  exact ⟨externalProductMapIso _ a b ((derivedHomUnitIso Λ X).app M).symm (Iso.refl _) ≪≫ β ≪≫
    ((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).mapIso
      (externalProductUnitLeftIso Λ a b N).symm.op).app _ ≪≫
    ((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).obj _).mapIso α.symm⟩

/-- The Künneth–Verdier isomorphism over `k` for all separated finite-type `k`-schemes
(`lemma-external-duality-trace-morphism--1`), in the form of
`AlgebraicGeometry.Etale.KunnethVerdier`. -/
theorem kunnethVerdier [HasInvertibleExponent Λ (Spec (.of k))] : KunnethVerdier Λ k :=
  ⟨fun _ _ a b _ _ _ _ _ _ _ _ hM hN ↦ nonempty_iso_kunnethVerdier Λ a b hM hN⟩

/-- Verdier duality commutes with external products over `k` (`rem-sf-kv-formal`):
`𝔻_{X ×_k Y} (P ⊠ Q) ≅ 𝔻_X P ⊠ 𝔻_Y Q`, from the Künneth–Verdier isomorphism by
`AlgebraicGeometry.Etale.verdierDualExternalProduct_iff_kunnethVerdier`. -/
theorem verdierDualExternalProduct [PerfectField k] [HasInvertibleExponent Λ (Spec (.of k))] :
    VerdierDualExternalProduct Λ k :=
  (kunnethVerdier Λ).verdierDualExternalProduct

variable (k) in
/-- Blueprint `lemma-external-duality-trace-morphism`: Künneth–Verdier isomorphism.

The four product comparison maps of `AlgebraicGeometry.Etale.HasKunnethComparisons` are
isomorphisms: besides the `!`-Künneth map `Ku_!`, which is an isomorphism by construction,
this asserts the invertibility of the exceptional Künneth map `α`, of the external Hom map
`β`, and of the Künneth–Verdier map `κ`.

It is stated over a field `k`, for a finite coefficient ring `Λ` whose exponent is invertible
in `k`, as in the blueprint. The headline case is `kunnethVerdier`: for `X` and `Y` separated of
finite type over `S = Spec k`,
with projections `p_X : X ×_S Y ⟶ X` and `p_Y : X ×_S Y ⟶ Y`, and for `M` in `Dctf(X, A)`
and `N` in `Dctf(Y, A)`,

`κ : M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`

on `X ×_S Y`, where `𝔻_Y = RHom(-, ω_Y)` is the Verdier dual relative to `b : Y ⟶ S`. -/
theorem hasKunnethComparisons [HasInvertibleExponent Λ (Spec (.of k))] :
    HasKunnethComparisons Λ (Spec (.of k)) where
  kunnethShriek := by
    intro _ _ _ _ b₁ b₂ _ _ _ _ f₁ f₂ _ _ _ _ _ _ _ hM₁ hM₂
    exact nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct (Λ := Λ) b₁ b₂ f₁ f₂
      hM₁ hM₂
  exceptional := by
    intro _ _ _ _ b₁ b₂ _ _ _ _ f₁ f₂ _ _ _ _ _ _ _ hN₁ hN₂
    exact nonempty_iso_externalProduct_rightDerivedUpperShriek Λ b₁ b₂ f₁ f₂ hN₁ hN₂
  externalHom := by
    intro _ _ c₁ c₂ _ _ _ _ _ _ _ _ _ _ hE₁ hE₂ hN₁ hN₂
    exact nonempty_iso_externalHom Λ c₁ c₂ hE₁ hE₂ hN₁ hN₂
  kunnethVerdier := by
    intro _ _ a b _ _ _ _ _ _ _ _ hM hN
    exact nonempty_iso_kunnethVerdier Λ a b hM hN

end Etale

end AlgebraicGeometry
