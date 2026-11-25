/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekInvertible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarInternalHom

/-!
# The canonical maps of `Rf^!` under composition, for finite coefficients

For a finite coefficient ring `Λ`, the composition law and the étale descent of the canonical
maps of the exceptional inverse image: the tensor map
`θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` (`AlgebraicGeometry.Etale.dualizingComplexTensorMap`) and the
base change map `Lg'^* Rf^! ⟶ Rf'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`). They are deduced from the
coherence of the composition law for `Rf_!` with the projection formula and with base change
(`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`) and of the projection formula
with the associativity of `⊗ᴸ` (`AlgebraicGeometry.Etale.projectionMapAssociativity`), through
the general statements of
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_comp`
- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_comp`
- `AlgebraicGeometry.Etale.isInvertible_of_isInvertible_leftDerivedUpperStar_of_etale`
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap_comp`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product: otherwise the monoidal structures found by instance
-- search differ from the ones in these definitions, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- Blueprint `lem-pur-co-smooth-composition`: Composition.

For `f : X ⟶ Y` and `g : Y ⟶ Z` admitting compactifications, if `ω_g` is invertible, `θ_g` is an
isomorphism at `K ∈ D^b_{ctf}(Z, Λ)` and `θ_f` is an isomorphism on `D^b_{ctf}(Y, Λ)`, then
`θ_{f ≫ g, K}` is an isomorphism. -/
theorem isIso_dualizingComplexTensorMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hf : ∀ P, DerivedCategory.boundedConstructibleFiniteTor Λ Y P →
      IsIso (dualizingComplexTensorMap Λ f P))
    (hω : DerivedCategory.isInvertible Λ Y (dualizingComplex Λ g))
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Z K)
    (hg : IsIso (dualizingComplexTensorMap Λ g K)) :
    IsIso (dualizingComplexTensorMap Λ (f ≫ g) K) := by
  obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
  exact isIso_lowerShriekRightAdjointUnitTensorMap_comp rfl (rightDerivedUpperShriekAdjunction Λ f)
    (rightDerivedUpperShriekAdjunction Λ g) (rightDerivedUpperShriekAdjunction Λ (f ≫ g))
    (E f g _ rfl) (hPF f g _ rfl) (projectionMapAssociativity Λ f) K
    (hf _ (constructibleFiniteTor_leftDerivedUpperStar _ g hK)) hg
    ((isInvertible_iff_exists_derivedTensor _).2 hω)

/-- If `θ_u` is an isomorphism at every object and `ω_u` is invertible, then `Ru^!` reflects
isomorphisms along a surjective étale `u`. -/
theorem isIso_of_isIso_rightDerivedUpperShriek_map {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    [Surjective u] [HasCompactification u] (hu : ∀ P, IsIso (dualizingComplexTensorMap Λ u P))
    (hω : DerivedCategory.isInvertible Λ U (dualizingComplex Λ u))
    {P Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : P ⟶ Q) (h : IsIso ((R(u)^![Λ]).map φ)) : IsIso φ :=
  isIso_of_isIso_leftDerivedUpperStar_map_of_surjective Λ u φ
    (isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map
      (rightDerivedUpperShriekAdjunction Λ u) hu
      ((isInvertible_iff_exists_derivedTensor _).2 hω) φ h)

/-- Blueprint `lem-pur-co-smooth-etale-locality`: Source-étale locality (step 3).

For a surjective étale `u : U ⟶ X` with `θ_u` an isomorphism at every object and `ω_u`
invertible, and `f : X ⟶ Y`: if `θ_{u ≫ f, K}` is an isomorphism, then so is `θ_{f, K}`. -/
theorem isIso_dualizingComplexTensorMap_of_comp {U X Y : Scheme.{u}} (u : U ⟶ X) [Etale u]
    [Surjective u] (f : X ⟶ Y) [HasCompactification u] [HasCompactification f]
    [HasCompactification (u ≫ f)] (hu : ∀ P, IsIso (dualizingComplexTensorMap Λ u P))
    (hω : DerivedCategory.isInvertible Λ U (dualizingComplex Λ u))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsIso (dualizingComplexTensorMap Λ (u ≫ f) K)) :
    IsIso (dualizingComplexTensorMap Λ f K) := by
  obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
  exact isIso_of_isIso_rightDerivedUpperShriek_map u hu hω _
    (isIso_map_lowerShriekRightAdjointUnitTensorMap_of_comp rfl
      (rightDerivedUpperShriekAdjunction Λ u) (rightDerivedUpperShriekAdjunction Λ f)
      (rightDerivedUpperShriekAdjunction Λ (u ≫ f)) (E u f _ rfl) (hPF u f _ rfl)
      (projectionMapAssociativity Λ u) hu K hK)

omit [Finite Λ] in
/-- If `W` and `W ⊗ᴸ P` are invertible, then so is `P`. -/
theorem DerivedCategory.isInvertible.of_derivedTensor_left {X : Scheme.{u}}
    {W P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hW : DerivedCategory.isInvertible Λ X W)
    (hWP : DerivedCategory.isInvertible Λ X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj W).obj P)) :
    DerivedCategory.isInvertible Λ X P := by
  obtain ⟨W', ⟨e₁⟩, ⟨e₂⟩⟩ := hW
  have hW' : DerivedCategory.isInvertible Λ X W' := ⟨W, ⟨e₂⟩, ⟨e₁⟩⟩
  refine DerivedCategory.isInvertible.of_iso ?_ (hW'.derivedTensor hWP)
  exact (derivedTensorAssociator _ X W' W P).symm ≪≫
    ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).mapIso e₂).app P ≪≫ derivedTensorLeftUnitor _ X P

omit [Finite Λ] in
/-- Blueprint `lem-pur-co-smooth-etale-locality`: Source-étale locality (step 2).

Invertibility descends along a surjective étale `u : U ⟶ X`: if `Lu^* L` is invertible, then so
is `L`. The evaluation `L ⊗ᴸ RHom(L, Λ) ⟶ Λ` pulls back to the evaluation of the invertible
`Lu^* L`, the derived pullback commuting with the derived internal hom
(`AlgebraicGeometry.Etale.isIso_ihomComparison_leftDerivedUpperStar_of_etale`), and
isomorphisms descend along `u`. -/
theorem isInvertible_of_isInvertible_leftDerivedUpperStar_of_etale {U X : Scheme.{u}}
    (u : U ⟶ X) [Etale u] [Surjective u]
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : DerivedCategory.isInvertible Λ U ((L((u)^*[ModuleCat.{u + 1} Λ])).obj L)) :
    DerivedCategory.isInvertible Λ X L := by
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) u
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have := isIso_ihomComparison_leftDerivedUpperStar_of_etale Λ u L
  exact (isInvertible_iff_exists_derivedTensor _).1
    (isInvertible_of_isIso_ihomComparison L((u)^*[ModuleCat.{u + 1} Λ])
      (fun φ hφ ↦ isIso_of_isIso_leftDerivedUpperStar_map_of_surjective Λ u φ hφ)
      ((isInvertible_iff_exists_derivedTensor _).2 h))

/-- Blueprint `lem-pur-co-smooth-etale-locality`: Source-étale locality (step 2).

For a surjective étale `u : U ⟶ X` with `θ_u` an isomorphism at every object and `ω_u`
invertible, and `f : X ⟶ Y`: if `ω_{u ≫ f}` is invertible, then so is `ω_f`. Indeed
`ω_{u ≫ f} ≅ Ru^! ω_f ≅ ω_u ⊗ᴸ Lu^* ω_f`. -/
theorem isInvertible_dualizingComplex_of_comp {U X Y : Scheme.{u}} (u : U ⟶ X) [Etale u]
    [Surjective u] (f : X ⟶ Y) [HasCompactification u] [HasCompactification f]
    [HasCompactification (u ≫ f)] [QuasiCompact (u ≫ f)]
    (hu : ∀ P, IsIso (dualizingComplexTensorMap Λ u P))
    (hω : DerivedCategory.isInvertible Λ U (dualizingComplex Λ u))
    (hωh : DerivedCategory.isInvertible Λ U (dualizingComplex Λ (u ≫ f))) :
    DerivedCategory.isInvertible Λ X (dualizingComplex Λ f) := by
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ u f
  refine isInvertible_of_isInvertible_leftDerivedUpperStar_of_etale u
    (DerivedCategory.isInvertible.of_derivedTensor_left hω ?_)
  have := hu (dualizingComplex Λ f)
  exact DerivedCategory.isInvertible.of_iso
    (asIso (dualizingComplexTensorMap Λ u _) ≪≫ (c.app (𝟙_ _)).symm).symm hωh

section BaseChange

variable {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {f' : X' ⟶ Y'}
  {g' : Y' ⟶ Z'} {h' : X' ⟶ Z'} {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
  (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) (sqh : IsPullback a h' h c)
  (w : f ≫ g = h) (w' : f' ≫ g' = h') [HasCompactification f] [HasCompactification g]
  [HasCompactification h] [HasCompactification f'] [HasCompactification g']
  [HasCompactification h'] [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact h']

include sqf sqg sqh w w' in
/-- **Base change maps of a composite.** For stacked cartesian squares, the base change map of
`R(f ≫ g)^!` is, up to the composition isomorphisms, the composite of those of `Rf^!` and `Rg^!`
(the blueprint's "exceptional composition identifies the base-change comparisons"). In
particular, `β_h` is an isomorphism at `K` as soon as `β_f` is one at `Rg^! K` and `β_g` at `K`,
and `Rf'^! β_g` is one at `K` as soon as `β_h` is one at `K` and `β_f` at `Rg^! K`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hf : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqf).app
      ((R(g)^![Λ]).obj K))) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqh).app K) ↔
      IsIso ((R(f')^![Λ]).map
        ((rightDerivedUpperShriekBaseChangeMap Λ sqg).app K)) := by
  obtain ⟨E, -, hEx⟩ := exists_rightDerivedLowerShriekCompIso Λ
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqf
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqg
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqh
  have key := Adjunction.mateEquiv_inv_comp_rightAdjointUniq
    (rightDerivedUpperShriekAdjunction _ f) (rightDerivedUpperShriekAdjunction _ g)
    (rightDerivedUpperShriekAdjunction _ h) (rightDerivedUpperShriekAdjunction _ f')
    (rightDerivedUpperShriekAdjunction _ g') (rightDerivedUpperShriekAdjunction _ h')
    (rightDerivedLowerShriekBaseChangeMap Λ sqf) (rightDerivedLowerShriekBaseChangeMap Λ sqg)
    (rightDerivedLowerShriekBaseChangeMap Λ sqh) (E f g h w) (E f' g' h' w')
    (hEx sqf sqg sqh w w') K
  change IsIso ((mateEquiv _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sqh))).app K) ↔
    IsIso ((R(f')^![Λ]).map
      ((mateEquiv _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sqg))).app K))
  change IsIso ((mateEquiv _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sqf))).app
    ((R(g)^![Λ]).obj K)) at hf
  rw [← isIso_comp_right_iff _ ((Adjunction.rightAdjointUniq
      ((rightDerivedUpperShriekAdjunction _ h').ofNatIsoLeft (E f' g' h' w'))
      ((rightDerivedUpperShriekAdjunction _ f').comp
        (rightDerivedUpperShriekAdjunction _ g'))).hom.app _), ← key,
    isIso_comp_left_iff, isIso_comp_left_iff]

end BaseChange

section InvertibleBaseChange

-- As in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`, whose
-- compatibility of the projection map with base change is used below: with the same instances,
-- its statement matches the one expected here syntactically.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

/-- **Base change at an invertible object.** For a cartesian square `g' ≫ f = f' ≫ g` with
quasi-compact `f'`, if the base change map `Lg'^* Rf^! ⟶ Rf'^! Lg^*` is an isomorphism at
`Λ_Y`, then it is one at every invertible `N`: through the tensor maps of `f` and `f'` it is the
base change map at `Λ_Y` tensored with `Lg'^* Lf^* N ≅ Lf'^* Lg^* N`, the projection formula
commuting with base change
(`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isInvertible {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (h₁ : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _)))
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : DerivedCategory.isInvertible Λ Y N) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app N) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  have : ∀ N, IsIso (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N) :=
    fun N ↦ by
      unfold derivedSquareUpperStarIsoInvApp
      infer_instance
  have hNi := (isInvertible_iff_exists_derivedTensor _).2 hN
  have hGN := isInvertible_leftDerivedUpperStar_obj g hNi
  exact Adjunction.isIso_mateEquiv_app_of_isInvertible
    (rightDerivedUpperShriekAdjunction Λ f)
    (rightDerivedUpperShriekAdjunction Λ f')
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f').app M).app N)
    (projectionMap_app_app_naturality_left f) (projectionMap_app_app_naturality_left f')
    (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g' M M').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g N N').hom)
    (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left g φ N'')
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N)
    (rightDerivedLowerShriekBaseChangeMap Λ sq) (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))
    (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib h₁ hNi
    (isInvertible_leftDerivedUpperStar_obj f hNi) hGN (isInvertible_leftDerivedUpperStar_obj f' hGN)

end InvertibleBaseChange

end Etale

end AlgebraicGeometry
