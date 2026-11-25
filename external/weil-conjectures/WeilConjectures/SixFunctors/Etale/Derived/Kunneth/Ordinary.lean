/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle
import WeilConjectures.CategoryTheory.DerivedCategory.TelescopeFlat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# The Künneth formula in ordinary étale cohomology

This file proves the base change theorems for a pushforward tensored with a complex
(`lemma-kunneth-field-coefficients--1`, `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_isGE`,
and `lemma-kunneth-field-coefficients--1`, `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`) and
deduces the Künneth formula over a separably closed field
(`proposition-ordinary-external-kunneth--1`,
`AlgebraicGeometry.Etale.isIso_kunnethMap_of_isSepClosed`). The Künneth map and the inputs which do
not depend on these base change theorems are in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Inputs

/-- First step of the proof of blueprint `lemma-kunneth-field-coefficients--1`: reduction to single
sheaves.

Under the hypotheses of `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_isGE`, the base
change map `Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)` is an isomorphism provided it
is an isomorphism when `E` is a flat sheaf and `F` is a sheaf, both placed in degree `0`
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_single`). -/
theorem isIso_tensorBaseChangeMap_of_isGE_of_single [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K))
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (_sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m n : ℤ)
    (_hE : DerivedCategory.TStructure.t.IsGE E m)
    (hEt : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), q < n →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (((derivedTensor (ModuleCat.{u + 1} Λ)
        X).obj E).obj ((DerivedCategory.singleFunctor _ 0).obj M))))
    (hF : DerivedCategory.TStructure.t.IsGE F m)
    (hsingle : ∀ 𝓔 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), ObjectProperty.flat 𝓔 →
      ∀ 𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
        IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
          ((L((p)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓔))
          ((DerivedCategory.singleFunctor _ 0).obj 𝓕))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj E) F) :=
  have := hF
  isIso_tensorBaseChangeMap_of_single (ModuleCat.{u + 1} Λ) h e f' g sq₂.w p E F m n
    hEt hsingle

/-- Blueprint `lemma-kunneth-field-coefficients--1`: base change for a pushforward tensored with a
bounded below complex of finite Tor amplitude.

Let `K` be a field and `Λ` a finite ring whose exponent is invertible in `K`. For a diagram

```
  X <--p-- X' <--h-- Y
  |        |         |
  a        f'        e
  v        v         v
Spec K <-b- S' <--g-- T
```

with both squares cartesian, `X` of finite type over `K` and `g` quasi-compact and quasi-separated,
the base change map (`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)`

is an isomorphism for every bounded below `E ∈ D(X_ét, Λ)` of Tor amplitude in `[n, ∞)` and every
bounded below `F ∈ D(T_ét, Λ)`.

The blueprint statement does not require `X` to be of finite type over `K`, but its proof uses
it: it applies `lemma-kunneth-field-coefficients--1`, which is stated for schemes of finite type, to
the `Xᵢ`. -/
theorem isIso_tensorBaseChangeMap_of_isGE [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (_sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m n : ℤ)
    (_hE : DerivedCategory.TStructure.t.IsGE E m)
    (_hEt : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), q < n →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (((derivedTensor (ModuleCat.{u + 1} Λ)
        X).obj E).obj ((DerivedCategory.singleFunctor _ 0).obj M))))
    (_hF : DerivedCategory.TStructure.t.IsGE F m) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj E) F) :=
  isIso_tensorBaseChangeMap_of_isGE_of_single Λ a b p f' h e g _sq₁ sq₂ E F m n _hE _hEt _hF
    (fun 𝓔 h𝓔 𝓕 ↦
      isIso_tensorBaseChangeMap_singleFunctor_of_flat Λ a b p f' h e g _sq₁ sq₂ 𝓔 h𝓔 𝓕)

variable {Λ} in
/-- Blueprint `lemma-kunneth-field-coefficients--1`, for `E` a strictly bounded complex of flat
sheaves: the reduction of `F` to strictly bounded complexes, which are bounded below, and an
application of blueprint `lemma-kunneth-field-coefficients--1`
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_isGE`). -/
lemma isIso_tensorBaseChangeMap_Q_obj_of_flat [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] [QuasiCompact h] [QuasiSeparated h]
    (hg : HasFiniteCohomologicalDimensionMorphism Λ g)
    (hh : HasFiniteCohomologicalDimensionMorphism Λ h)
    (sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (m n : ℤ)
    [P.IsStrictlyGE m] [P.IsStrictlyLE n] (hP : ∀ i, ObjectProperty.flat (P.X i))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj (DerivedCategory.Q.obj P)) F) := by
  have := preservesColimitsOfShape_nat_rightDerivedLowerStar Λ g hg
  have := preservesColimitsOfShape_nat_rightDerivedLowerStar Λ h hh
  refine DerivedCategory.isIso_app_of_isIso_app_Q_obj_bounded
    (tensorBaseChangeMapRight (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj (DerivedCategory.Q.obj P))) (fun L m' _ _ _ ↦ ?_) F
  exact isIso_tensorBaseChangeMap_of_isGE Λ a b p f' h e g sq₁ sq₂ _ _ (min m m') m
    (DerivedCategory.TStructure.t.isGE_of_ge _ _ m (min_le_left _ _))
    (isZero_homology_derivedTensor_Q_obj_of_flat _ P m n hP)
    (DerivedCategory.TStructure.t.isGE_of_ge _ _ m' (min_le_right _ _))

/-- Blueprint `lemma-kunneth-field-coefficients--1`: base change for a pushforward tensored with an
arbitrary complex.

Let `K` be a field and `Λ` a finite ring whose exponent is invertible in `K`. For a diagram

```
  X <--p-- X' <--h-- Y
  |        |         |
  a        f'        e
  v        v         v
Spec K <-b- S' <--g-- T
```

of `K`-schemes of finite type with both squares cartesian, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)`

is an isomorphism for all `E ∈ D(X_ét, Λ)` and `F ∈ D(T_ét, Λ)`, unbounded. -/
theorem isIso_tensorBaseChangeMap [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) (t : T ⟶ Spec (.of K))
    [LocallyOfFiniteType a] [QuasiCompact a] [LocallyOfFiniteType b] [QuasiCompact b]
    [LocallyOfFiniteType t] [QuasiCompact t]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') (hg : g ≫ b = t)
    (sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj E) F) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  -- the schemes `X'`, `Y`, `T` and `S'` are of finite type over `K`, hence locally Noetherian
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sq₁ ‹LocallyOfFiniteType a›
  have : QuasiCompact f' := MorphismProperty.of_isPullback sq₁ ‹QuasiCompact a›
  have : LocallyOfFiniteType e := MorphismProperty.of_isPullback sq₂ ‹LocallyOfFiniteType f'›
  have : QuasiCompact e := MorphismProperty.of_isPullback sq₂ ‹QuasiCompact f'›
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian b
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f' ≫ b)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (e ≫ t)
  have hw : h ≫ f' ≫ b = e ≫ t := by rw [← Category.assoc, sq₂.w, Category.assoc, hg]
  -- hence `g` and `h` are quasi-compact and quasi-separated
  have : QuasiCompact g := by
    have : QuasiCompact (g ≫ b) := by rw [hg]; infer_instance
    exact QuasiCompact.of_comp g b
  have : QuasiCompact h := by
    have : QuasiCompact (h ≫ f' ≫ b) := by rw [hw]; infer_instance
    exact QuasiCompact.of_comp h (f' ≫ b)
  -- and of finite cohomological dimension, so that `Rg_*` and `Rh_*` commute with direct sums
  have hgd := hasFiniteCohomologicalDimensionMorphism Λ hΛ t b g hg
  have hhd := hasFiniteCohomologicalDimensionMorphism Λ hΛ (e ≫ t) (f' ≫ b) h hw
  have := preservesColimitsOfShape_nat_rightDerivedLowerStar Λ h hhd
  -- reduce `E` to strictly bounded complexes of flat sheaves
  exact DerivedCategory.isIso_app_of_isIso_app_Q_obj_flat
    (Functor.whiskerLeft L((p)^*[ModuleCat.{u + 1} Λ])
      (tensorBaseChangeMapLeft (ModuleCat.{u + 1} Λ) h e f' g sq₂.w F))
    (fun P m n _ _ hP ↦ isIso_tensorBaseChangeMap_Q_obj_of_flat a b p f' h e g hgd hhd sq₁ sq₂
      P m n hP F) E

end Inputs

section Kunneth

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- Blueprint `proposition-ordinary-external-kunneth--1`: the Künneth formula in étale cohomology.

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`, and
`X`, `Y` schemes of finite type over `k`. For a cartesian square

```
  W --p₂--> Y
  |         |
  p₁        a_Y
  v         v
  X --a_X-> Spec k
```

and all `E ∈ D(X_ét, Λ)`, `K ∈ D(Y_ét, Λ)`, unbounded, the Künneth map
(`AlgebraicGeometry.Etale.kunnethMap`)

`κ_{E,K} : Ra_{X*} E ⊗ᴸ Ra_{Y*} K ⟶ Rc_*(Lp₁^* E ⊗ᴸ Lp₂^* K)`, `c = p₁ ≫ a_X`,

is an isomorphism in `D((Spec k)_ét, Λ)`; through `RΓ(Spec k, -)` it is the map
`RΓ(X, E) ⊗ᴸ RΓ(Y, K) ⟶ RΓ(W, Lp₁^* E ⊗ᴸ Lp₂^* K)`
(`AlgebraicGeometry.Etale.nonempty_iso_kunneth_of_isSepClosed`).

Following the blueprint, `κ_{E,K}` is the composite (`proposition-ordinary-external-kunneth--1`,
`AlgebraicGeometry.Etale.kunnethMap_eq`) of the projection map of `a_X`, an isomorphism by
`proposition-open-direct-image-preserves-finite`, of `Ra_{X*}` applied to the base change map of
`lemma-kunneth-field-coefficients--1` for the diagram `X = X ⟵ W`, `Spec k = Spec k ⟵ Y`, and of the
composition isomorphism `Ra_{X*} Rp₁_* ≅ Rc_*`. -/
theorem isIso_kunnethMap_of_isSepClosed {W : Scheme.{u}} (p₁ : W ⟶ X) (p₂ : W ⟶ Y)
    (sq : IsPullback p₁ p₂ aX aY)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (kunnethMap (ModuleCat.{u + 1} Λ) p₁ p₂ aX aY (p₁ ≫ aX) rfl sq.w.symm E K) := by
  have h := isIso_tensorBaseChangeMap Λ aX (𝟙 _) aY (𝟙 X) aX p₁ p₂ aY (Category.comp_id _)
    (IsPullback.of_horiz_isIso (by simp)) sq E K
  let ι := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).app E
  have hn := tensorBaseChangeMap_naturality (ModuleCat.{u + 1} Λ) p₁ p₂ aX aY sq.w ι.hom
    (𝟙 K)
  have : IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) p₁ p₂ aX aY sq.w E K) :=
    have := IsIso.of_isIso_fac_left hn
    @IsIso.of_isIso_comp_left _ _ _ _ _ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ].obj E).map
      (L((aX)^*[ModuleCat.{u + 1} Λ]).map (R((aY)_*[ModuleCat.{u + 1} Λ]).map (𝟙 K)))) _ _ this
  rw [kunnethMap_eq]
  infer_instance

/-- Blueprint `proposition-ordinary-external-kunneth--1`, in `D(Λ)`: the Künneth formula
`RΓ(X, E) ⊗ᴸ RΓ(Y, K) ≅ RΓ(W, Lp₁^* E ⊗ᴸ Lp₂^* K)` for schemes `X`, `Y` of finite type over a
separably closed field `k`, `W = X ×_k Y`, and all `E ∈ D(X_ét, Λ)`, `K ∈ D(Y_ét, Λ)`. It is
`RΓ(Spec k, -)` applied to the Künneth map (`isIso_kunnethMap_of_isSepClosed`), together with
the Leray isomorphisms and the compatibility of `RΓ(Spec k, -)` with `⊗ᴸ`. -/
theorem nonempty_iso_kunneth_of_isSepClosed {W : Scheme.{u}} (p₁ : W ⟶ X) (p₂ : W ⟶ Y)
    (sq : IsPullback p₁ p₂ aX aY)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
            ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
          ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K))) := by
  have := isIso_kunnethMap_of_isSepClosed Λ aX aY p₁ p₂ sq E K
  obtain ⟨e⟩ := nonempty_iso_rightDerivedGlobalSections_derivedTensor_of_isSepClosed Λ
    ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj E) ((R((aY)_*[ModuleCat.{u + 1} Λ])).obj K)
  exact ⟨(((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aX).app E).symm ⊗ᵢ
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aY).app K).symm) ≪≫ e.symm ≪≫
    (rightDerivedGlobalSections _ (Spec (.of k))).mapIso
      (asIso (kunnethMap (ModuleCat.{u + 1} Λ) p₁ p₂ aX aY (p₁ ≫ aX) rfl sq.w.symm E K)) ≪≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ (p₁ ≫ aX)).app _⟩

end Kunneth

end Etale

end AlgebraicGeometry
