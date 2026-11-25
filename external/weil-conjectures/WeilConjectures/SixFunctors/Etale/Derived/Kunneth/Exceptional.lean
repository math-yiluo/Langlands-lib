/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional.Local
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The exceptional Künneth formula

Over a field `k`, for a finite coefficient ring `Λ` whose exponent is invertible in `k`, and for
compactifiable morphisms `fᵢ : Xᵢ ⟶ Yᵢ` with `Yᵢ` of finite type over `k`, the exceptional
Künneth isomorphism (`proposition-exceptional-external-kunneth--1`) reads

`α : Rf₁^! N₁ ⊠ Rf₂^! N₂ ≅ R(f₁ × f₂)^!(N₁ ⊠ N₂)`

(`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedUpperShriek`).

It is deduced from the one-sided formula
`R(g × 𝟙_W)^!(N ⊠ M) ≅ Rg^! N ⊠ M`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor`): the base change
map and the tensor map of `Rh^!` for `h = g × 𝟙_W` are isomorphisms
(`AlgebraicGeometry.Etale.isExceptionalKunneth`). Writing `f₁ × f₂ = (𝟙 × f₂) ≫ (f₁ × 𝟙)`, the
composition law for the exceptional inverse image reduces the two-sided formula to two
one-sided ones.

The formula holds for all objects `Nᵢ`, not only for `Nᵢ ∈ Dctf(Yᵢ, Λ)`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor`
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedUpperShriek_of_forall`
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedUpperShriek`
  (`proposition-exceptional-external-kunneth--1`)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- **The one-sided exceptional Künneth formula.** Let `g : T ⟶ S` be quasi-compact and
compactifiable, with `S` and `W` of finite type over `k`, let `P = S ×_k W` with projections
`q`, `r`, and let `h : Q ⟶ P` be the base change of `g` along `q`, with `q' : Q ⟶ T`. Then for
all `N ∈ D(S_ét, Λ)` and `M ∈ D(W_ét, Λ)`,

`Rh^!(Lq^* N ⊗ᴸ Lr^* M) ≅ Lq'^* Rg^! N ⊗ᴸ L(h ≫ r)^* M`,

that is `R(g × 𝟙_W)^!(N ⊠ M) ≅ Rg^! N ⊠ M`: through the inverses of the tensor map of `h` and
of the base change map (`AlgebraicGeometry.Etale.isExceptionalKunneth`). -/
theorem nonempty_iso_rightDerivedUpperShriek_derivedTensor {T S W P Q : Scheme.{u}}
    (b : S ⟶ Spec (.of k)) (c : W ⟶ Spec (.of k)) [LocallyOfFiniteType b] [QuasiCompact b]
    [LocallyOfFiniteType c] [QuasiCompact c] {q : P ⟶ S} {r : P ⟶ W} (sqP : IsPullback q r b c)
    (g : T ⟶ S) [HasCompactification g] [QuasiCompact g] {q' : Q ⟶ T} {h : Q ⟶ P}
    (sq : IsPullback q' h g q) [HasCompactification h] [QuasiCompact h]
    (N : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(h)^![Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) P).obj
        ((L((q)^*[ModuleCat.{u + 1} Λ])).obj N)).obj ((L((r)^*[ModuleCat.{u + 1} Λ])).obj M)) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Q).obj ((L((q')^*[ModuleCat.{u + 1} Λ])).obj
        ((R(g)^![Λ]).obj N))).obj
          ((L((h ≫ r)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
  obtain ⟨hBC, hτ⟩ := isExceptionalKunneth Λ k g b b c sqP sq
  have := (isIsoLowerShriekRightAdjointTensorMap_iff _ _ _).1 (hτ N M)
  have := (isIso_lowerShriekRightAdjointTensorMapOfDerivedTensor_iff
    (rightDerivedUpperShriekAdjunction Λ h)
    ((L((q)^*[ModuleCat.{u + 1} Λ])).obj N) ((L((r)^*[ModuleCat.{u + 1} Λ])).obj M)).2 this
  have := hBC N
  let e : (L((q')^*[ModuleCat.{u + 1} Λ])).obj ((R(g)^![Λ]).obj N) ≅
      (R(h)^![Λ]).obj ((L((q)^*[ModuleCat.{u + 1} Λ])).obj N) :=
    asIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app N)
  exact ⟨(asIso (lowerShriekRightAdjointTensorMapOfDerivedTensor
      (rightDerivedUpperShriekAdjunction Λ h) _ _)).symm ≪≫
    ((derivedTensor _ Q).mapIso e.symm).app _ ≪≫
    ((derivedTensor _ Q).obj _).mapIso ((leftDerivedUpperStarComp _ h r).app M).symm⟩

/-- The morphism `𝟙 × f₂ : X₁ ×_S X₂ ⟶ X₁ ×_S Y₂` over a base `S`. -/
noncomputable abbrev pullbackMapOverBaseLeft {S X₁ X₂ Y₂ : Scheme.{u}} (a₁ : X₁ ⟶ S)
    (f₂ : X₂ ⟶ Y₂) (b₂ : Y₂ ⟶ S) : pullback a₁ (f₂ ≫ b₂) ⟶ pullback a₁ b₂ :=
  pullback.map _ _ _ _ (𝟙 X₁) f₂ (𝟙 S) (by simp) (by simp)

/-- The square of `𝟙 × f₂` and `f₂` with the second projections is cartesian. -/
lemma isPullback_pullbackMapOverBaseLeft {S X₁ X₂ Y₂ : Scheme.{u}} (a₁ : X₁ ⟶ S)
    (f₂ : X₂ ⟶ Y₂) (b₂ : Y₂ ⟶ S) :
    IsPullback (pullback.snd a₁ (f₂ ≫ b₂)) (pullbackMapOverBaseLeft a₁ f₂ b₂) f₂
      (pullback.snd a₁ b₂) :=
  IsPullback.of_bot (by simpa using (IsPullback.of_hasPullback a₁ (f₂ ≫ b₂)).flip)
    (by simp) (IsPullback.of_hasPullback a₁ b₂).flip

/-- **The exceptional Künneth formula, for all coefficients.** For compactifiable quasi-compact
`fᵢ : Xᵢ ⟶ Yᵢ` with `Yᵢ` of finite type over `k`, and all `Nᵢ ∈ D(Yᵢ_ét, Λ)`,
`Rf₁^! N₁ ⊠ Rf₂^! N₂ ≅ R(f₁ × f₂)^!(N₁ ⊠ N₂)`. -/
theorem nonempty_iso_externalProduct_rightDerivedUpperShriek_of_forall
    {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ Spec (.of k)) (b₂ : Y₂ ⟶ Spec (.of k))
    [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
    [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    (N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂)
        ((R(f₁)^![Λ]).obj N₁) ((R(f₂)^![Λ]).obj N₂) ≅
      (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ N₁ N₂)) := by
  let φ₁ := pullback.mapOverBaseRight f₁ b₁ b₂
  let φ₂ := pullbackMapOverBaseLeft (f₁ ≫ b₁) f₂ b₂
  have sq₁ : IsPullback (pullback.fst (f₁ ≫ b₁) b₂) φ₁ f₁ (pullback.fst b₁ b₂) :=
    (isPullback_mapOverBaseRight_fst b₁ b₂ f₁).flip
  have sq₂ := isPullback_pullbackMapOverBaseLeft (f₁ ≫ b₁) f₂ b₂
  have : HasCompactification φ₁ := .of_isPullback sq₁
  have : HasCompactification φ₂ := .of_isPullback sq₂
  have : QuasiCompact φ₁ := MorphismProperty.of_isPullback sq₁ ‹_›
  have : QuasiCompact φ₂ := MorphismProperty.of_isPullback sq₂ ‹_›
  have hφ : φ₂ ≫ φ₁ = pullback.mapOverBase f₁ f₂ b₁ b₂ := by
    ext <;> simp [φ₁, φ₂]
  have hcomp : ∀ (m : pullback (f₁ ≫ b₁) (f₂ ≫ b₂) ⟶ pullback b₁ b₂) (_ : φ₂ ≫ φ₁ = m)
      [HasCompactification m] (K : _root_.DerivedCategory
        (Sheaf (pullback b₁ b₂).smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      Nonempty ((R(m)^![Λ]).obj K ≅
        (R(φ₂)^![Λ]).obj ((R(φ₁)^![Λ]).obj K)) := by
    intro m hm _ K
    subst hm
    obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ φ₂ φ₁
    exact ⟨e.app K⟩
  obtain ⟨e₀⟩ := hcomp _ hφ (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ N₁ N₂)
  -- the first factor: `R(f₁ × 𝟙)^!(N₁ ⊠ N₂) ≅ Rf₁^! N₁ ⊠ N₂`
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_derivedTensor Λ b₁ b₂
    (IsPullback.of_hasPullback b₁ b₂) f₁ sq₁ N₁ N₂
  have h₁ : φ₁ ≫ pullback.snd b₁ b₂ = pullback.snd (f₁ ≫ b₁) b₂ :=
    pullback.mapOverBaseRight_snd f₁ b₁ b₂
  -- the second factor: `R(𝟙 × f₂)^!(K ⊠ N₂) ≅ K ⊠ Rf₂^! N₂`
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_derivedTensor Λ b₂ (f₁ ≫ b₁)
    (IsPullback.of_hasPullback (f₁ ≫ b₁) b₂).flip f₂ sq₂ N₂ ((R(f₁)^![_]).obj N₁)
  have h₂ : φ₂ ≫ pullback.fst (f₁ ≫ b₁) b₂ = pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂) := by
    simp [φ₂]
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) (pullback (f₁ ≫ b₁) b₂)
  obtain ⟨β'⟩ :=
    nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) (pullback (f₁ ≫ b₁) (f₂ ≫ b₂))
  let e₁' : (R(φ₁)^![Λ]).obj (externalProduct _ b₁ b₂ N₁ N₂) ≅
      ((derivedTensor _ (pullback (f₁ ≫ b₁) b₂)).obj
        ((L((pullback.snd (f₁ ≫ b₁) b₂)^*[ModuleCat.{u + 1} Λ])).obj N₂)).obj
          ((L((pullback.fst (f₁ ≫ b₁) b₂)^*[ModuleCat.{u + 1} Λ])).obj
            ((R(f₁)^![Λ]).obj N₁)) :=
    e₁ ≪≫ ((derivedTensor _ _).obj _).mapIso (eqToIso (by rw [h₁])) ≪≫ (β.app _).app _
  let e₂' : (R(φ₂)^![Λ]).obj (((derivedTensor _ (pullback (f₁ ≫ b₁) b₂)).obj
        ((L((pullback.snd (f₁ ≫ b₁) b₂)^*[ModuleCat.{u + 1} Λ])).obj N₂)).obj
          ((L((pullback.fst (f₁ ≫ b₁) b₂)^*[ModuleCat.{u + 1} Λ])).obj
            ((R(f₁)^![Λ]).obj N₁))) ≅
      externalProduct _ (f₁ ≫ b₁) (f₂ ≫ b₂) ((R(f₁)^![Λ]).obj N₁)
        ((R(f₂)^![Λ]).obj N₂) :=
    e₂ ≪≫ ((derivedTensor _ _).obj _).mapIso (eqToIso (by rw [h₂])) ≪≫ (β'.app _).app _
  exact ⟨(e₀ ≪≫ (R(φ₂)^![Λ]).mapIso e₁' ≪≫ e₂').symm⟩

/-- Blueprint `proposition-exceptional-external-kunneth--1`: Exceptional Künneth; the `α` map.

Over a field `k`, for a finite coefficient ring `Λ` whose exponent is invertible in `k`, let
`fᵢ : Xᵢ ⟶ Yᵢ` (`i = 1, 2`) be quasi-compact morphisms admitting compactifications, with `Yᵢ`
of finite type over `k`, and let `Nᵢ ∈ Dctf(Yᵢ, Λ)`. Then, with the external products over
`Spec k`,

`Rf₁^! N₁ ⊠ Rf₂^! N₂ ≅ R(f₁ × f₂)^!(N₁ ⊠ N₂)`.

The statement is the `exceptional` field of `AlgebraicGeometry.Etale.HasKunnethComparisons`
over `S = Spec k`; it holds for all `Nᵢ`
(`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedUpperShriek_of_forall`). -/
theorem nonempty_iso_externalProduct_rightDerivedUpperShriek
    {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ Spec (.of k)) (b₂ : Y₂ ⟶ Spec (.of k))
    [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
    [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    {N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))} :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₁ N₁ →
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₂ N₂ →
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂)
        ((R(f₁)^![Λ]).obj N₁) ((R(f₂)^![Λ]).obj N₂) ≅
      (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ N₁ N₂)) := fun _ _ ↦
  nonempty_iso_externalProduct_rightDerivedUpperShriek_of_forall Λ b₁ b₂ f₁ f₂ N₁ N₂

end Etale

end AlgebraicGeometry
