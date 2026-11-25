/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMapRightAdjointUniq
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Etale
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDualityBaseChange

/-!
# Smooth duality for étale morphisms

For an étale morphism `e : X ⟶ Y` admitting a compactification, `Re^! ≅ Le^*` and the canonical
tensor map `θ_{e,K} : ω_e ⊗ᴸ Le^* K ⟶ Re^! K` is an isomorphism for every `K`, with `ω_e ≅ Λ_X`
(`AlgebraicGeometry.Etale.etaleSmoothDuality`): the étale case of the proof of blueprint
`proposition-exceptional-inverse-image-smooth-morphism`, from
`lemma-affine-space-etale-localization--4`.

The compactly supported direct image `R(e)_!` is left adjoint to `Le^*`
(`AlgebraicGeometry.Etale.compactificationEtaleAdjunction`), so `ω_e ≅ Le^* Λ_Y ≅ Λ_X`. The
tensor maps are treated in three steps.

* For an open immersion `j`, the unit of `R(j)_! ⊣ Lj^*` is an isomorphism: it commutes with
  base change, and the base change of `j` along itself is the identity. Hence the tensor maps of
  `R(j)_! ⊣ Lj^*` are isomorphisms
  (`CategoryTheory.Adjunction.isIso_projectionTensorMap_of_isIso_unit`), and so are those of
  `R(j)_! ⊣ Rj^!`, the tensor maps of two right adjoints agreeing.
* For a quasi-compact étale `e`, base change `e` along itself: the diagonal `Δ` is a section of
  the second projection `e'`, hence an open immersion, and `Δ ≫ e' = 𝟙`; by the composition law
  `LΔ^* θ_{e'}` is an isomorphism, and since the base change map is an isomorphism
  (`AlgebraicGeometry.Etale.etaleBaseChange`), so is `LΔ^* Lg'^* θ_e ≅ θ_e`, for the first
  projection `g'`.
* In general, `θ_e` descends along a cover of `X` by affine opens mapping to affine opens of `Y`,
  over which `e` is quasi-compact.

## Main statements

- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_isOpenImmersion`
- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_etale`
- `AlgebraicGeometry.Etale.etaleSmoothDuality`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section Adjunction

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e] [HasCompactification e]

/-- The adjunction `R(e)_! ⊣ Le^*` of an étale morphism admitting a compactification. -/
noncomputable def rightDerivedLowerShriekEtaleAdjunction :
    R(e)_![ModuleCat.{u + 1} Λ] ⊣ L((e)^*[ModuleCat.{u + 1} Λ]) :=
  have := isIso_compactificationEtaleComparison Λ e (HasCompactification.compactification e)
  compactificationEtaleAdjunction Λ e (HasCompactification.compactification e)

/-- For an étale morphism `e`, the dualizing complex is trivial: `ω_e = Re^! Λ_Y ≅ Le^* Λ_Y ≅
Λ_X`. -/
noncomputable def dualizingComplexIsoOfEtale : dualizingComplex Λ e ≅ 𝟙_ _ :=
  (Adjunction.rightAdjointUniq (rightDerivedUpperShriekAdjunction Λ e)
      (rightDerivedLowerShriekEtaleAdjunction Λ e)).app (𝟙_ _) ≪≫
    leftDerivedUpperStarUnitIso _ e

/-- For an étale morphism `e`, the dualizing complex `ω_e` is invertible. -/
lemma isInvertible_dualizingComplex_of_etale :
    DerivedCategory.isInvertible Λ X (dualizingComplex Λ e) :=
  DerivedCategory.isInvertible.of_iso (dualizingComplexIsoOfEtale Λ e).symm
    (DerivedCategory.isInvertible_unit Λ X)

end Adjunction

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **The unit of `Rf_!(c) ⊣ Lj^*` is an isomorphism for an open immersion `j`.** The unit
commutes with base change (`AlgebraicGeometry.Etale.compactificationEtaleUnit_baseChange`), and
the base change of `j` along itself is `𝟙 U`, for which `Lj^*` is an equivalence. -/
theorem isIso_compactificationEtaleUnit_app_of_isOpenImmersion (c : Compactification j)
    (N : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((compactificationEtaleUnit Λ j c).app N) := by
  have sq : IsPullback (𝟙 U) (𝟙 U) j j := IsKernelPair.id_of_mono j
  have h := compactificationEtaleUnit_baseChange Λ sq c N
  have := isIso_compactificationEtaleComparison Λ (𝟙 U) (c.ofIsPullback sq)
  have : L((𝟙 U)^*[ModuleCat.{u + 1} Λ]).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId _ U).symm
  have hu : IsIso ((compactificationEtaleAdjunction Λ (𝟙 U) (c.ofIsPullback sq)).unit.app
      (L((𝟙 U)^*[ModuleCat.{u + 1} Λ]).obj N)) :=
    inferInstance
  rw [compactificationEtaleAdjunction_unit_app, ← h] at hu
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite Λ sq c
  have := (isIso_comp_right_iff _ _).1 hu
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarId _ U) _).1 this

/-- **Smooth duality for open immersions**: for an open immersion `j` admitting a
compactification, the canonical tensor map `θ_{j,K}` is an isomorphism for every `K`. The unit
of `R(j)_! ⊣ Lj^*` is an isomorphism, so the tensor maps of this adjunction are
(`CategoryTheory.Adjunction.isIso_projectionTensorMap_of_isIso_unit`), and so are those of
`R(j)_! ⊣ Rj^!`. -/
theorem isIso_dualizingComplexTensorMap_of_isOpenImmersion [HasCompactification j]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (dualizingComplexTensorMap Λ j K) := by
  have : IsIso (rightDerivedLowerShriekEtaleAdjunction Λ j).unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    have := isIso_compactificationEtaleComparison Λ j (HasCompactification.compactification j)
    rw [rightDerivedLowerShriekEtaleAdjunction, compactificationEtaleAdjunction_unit_app]
    exact isIso_compactificationEtaleUnit_app_of_isOpenImmersion Λ j _ N
  rw [dualizingComplexTensorMap, isIso_lowerShriekRightAdjointUnitTensorMap_iff]
  exact (Adjunction.isIso_projectionTensorMap_iff_of_adjunction _
    (rightDerivedUpperShriekAdjunction Λ j) (rightDerivedLowerShriekEtaleAdjunction Λ j)
    (projectionMap_app_app_naturality_left j) _ _).2
    (Adjunction.isIso_projectionTensorMap_of_isIso_unit _ _
      (fun A B ↦ leftDerivedUpperStarTensorIso _ j A B)
      (fun φ B ↦ leftDerivedUpperStarTensorIso_hom_naturality_left j φ B) _ _)

end OpenImmersion

section QuasiCompact

variable {Λ} in
/-- The tensor map at `(M', N)` is an isomorphism after applying a functor `H` if it is one at
`(M, N)` for `M ≅ M'`. -/
lemma isIso_map_rightDerivedUpperShriekTensorMap_of_iso_left {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    {M M' N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ≅ M') {E : Type*} [Category* E]
    (H : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ E)
    (h : IsIso (H.map (rightDerivedUpperShriekTensorMap f M N))) :
    IsIso (H.map (rightDerivedUpperShriekTensorMap f M' N)) := by
  have hn := Adjunction.projectionTensorMap_naturality_left (rightDerivedUpperShriekAdjunction Λ f)
    _ (projectionMap_app_app_naturality_left f) φ.hom N
  have : IsIso (H.map ((R(f)^![Λ]).map φ.hom ▷ (L((f)^*[ModuleCat.{u + 1} Λ])).obj N ≫
      rightDerivedUpperShriekTensorMap f M' N)) := by
    rw [hn, Functor.map_comp]
    infer_instance
  rw [Functor.map_comp] at this
  exact IsIso.of_isIso_comp_left (H.map ((R(f)^![Λ]).map φ.hom ▷ _)) _

/-- **Smooth duality for quasi-compact étale morphisms.** Base change `e` along itself: the
diagonal `Δ` is a section of the second projection `e'`, hence an open immersion, and by the
composition law `LΔ^*` of the tensor maps of `e'` are isomorphisms. The base change map being an
isomorphism (`AlgebraicGeometry.Etale.etaleBaseChange`), so is `LΔ^* Lg'^* θ_{e,K} ≅ θ_{e,K}`,
for the first projection `g'`. -/
theorem isIso_dualizingComplexTensorMap_of_quasiCompact {V W : Scheme.{u}} (e : V ⟶ W)
    [_root_.AlgebraicGeometry.Etale e] [QuasiCompact e] [HasCompactification e]
    (K : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (dualizingComplexTensorMap Λ e K) := by
  have sq := IsPullback.of_hasPullback e e
  have : HasCompactification (pullback.snd e e) := .of_isPullback sq
  have := etaleBaseChange Λ e sq
  let Δ : V ⟶ pullback e e := pullback.lift (𝟙 V) (𝟙 V) rfl
  have hΔ₁ : Δ ≫ pullback.fst e e = 𝟙 V := pullback.lift_fst _ _ _
  have hΔ₂ : Δ ≫ pullback.snd e e = 𝟙 V := pullback.lift_snd _ _ _
  have : IsOpenImmersion Δ := IsOpenImmersion.of_section_of_etale (pullback.snd e e) Δ hΔ₂
  have : HasCompactification Δ := (Compactification.ofIsOpenImmersion Δ).hasCompactification
  have : HasCompactification (𝟙 V) := (Compactification.ofIsOpenImmersion _).hasCompactification
  -- `LΔ^*` of the tensor maps of `e'` are isomorphisms
  have hΔ (K' : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((L((Δ)^*[ModuleCat.{u + 1} Λ])).map
        (rightDerivedUpperShriekTensorMap (pullback.snd e e) (𝟙_ _) K')) := by
    obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
    have := isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map
      (rightDerivedUpperShriekAdjunction Λ Δ)
      (isIso_dualizingComplexTensorMap_of_isOpenImmersion Λ Δ)
      ((isInvertible_iff_exists_derivedTensor _).2 (isInvertible_dualizingComplex_of_etale Λ Δ)) _
      (isIso_map_lowerShriekRightAdjointUnitTensorMap_of_comp hΔ₂
        (rightDerivedUpperShriekAdjunction Λ Δ) (rightDerivedUpperShriekAdjunction Λ _)
        (rightDerivedUpperShriekAdjunction Λ (𝟙 V)) (E _ _ _ hΔ₂) (hPF _ _ _ hΔ₂)
        (projectionMapAssociativity Λ Δ) (isIso_dualizingComplexTensorMap_of_isOpenImmersion Λ Δ)
        K' (isIso_dualizingComplexTensorMap_of_isOpenImmersion Λ (𝟙 V) K'))
    rw [lowerShriekRightAdjointUnitTensorMap_eq, Functor.map_comp] at this
    exact (isIso_comp_right_iff _ _).1 this
  have h := isIso_map_leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap sq (𝟙_ _) K
    (L((Δ)^*[ModuleCat.{u + 1} Λ]))
    (isIso_map_rightDerivedUpperShriekTensorMap_of_iso_left _
      (leftDerivedUpperStarUnitIso _ e).symm _ (hΔ _))
  have : IsIso (rightDerivedUpperShriekTensorMap e (𝟙_ _) K) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarCompSectionIso _ Δ (pullback.fst e e) hΔ₁) _).1 h
  rw [dualizingComplexTensorMap, lowerShriekRightAdjointUnitTensorMap_eq]
  infer_instance

end QuasiCompact

/-- **Smooth duality for étale morphisms, the tensor maps**: for an étale `e` admitting a
compactification, `θ_{e,K}` is an isomorphism for every `K`. Cover `X` by affine opens `V_x`
mapping to affine opens `U_x` of `Y`: the restriction `V_x ⟶ U_x` is quasi-compact
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_quasiCompact`), the tensor maps
compose with those of the open immersion `U_x ⟶ Y`, and they descend along the open cover. -/
theorem isIso_dualizingComplexTensorMap_of_etale {V W : Scheme.{u}} (e : V ⟶ W)
    [_root_.AlgebraicGeometry.Etale e] [HasCompactification e]
    (K : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (dualizingComplexTensorMap Λ e K) := by
  have hcov (x : V) : ∃ (U : W.Opens) (V' : V.Opens), IsAffineOpen U ∧ IsAffineOpen V' ∧
      x ∈ V' ∧ V' ≤ e ⁻¹ᵁ U := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := e.base x) (U := ⊤) trivial
    obtain ⟨V', hV', hxV', hle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := e ⁻¹ᵁ U) hxU
    exact ⟨U, V', hU, hV', hxV', hle⟩
  choose U V' hU hV' hx hle using hcov
  have (x : V) : HasCompactification (V' x).ι :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have (x : V) : HasCompactification ((V' x).ι ≫ e) :=
    ((HasCompactification.compactification e).precomp _).hasCompactification
  refine isIso_dualizingComplexTensorMap_of_jointlySurjective Λ (fun x ↦ (V' x).ι)
    (fun x ↦ ⟨x, ⟨x, hx x⟩, rfl⟩) e
    (fun x ↦ isIso_dualizingComplexTensorMap_of_isOpenImmersion Λ _)
    (fun x ↦ isInvertible_dualizingComplex_of_etale Λ _) K fun x ↦ ?_
  have : IsAffine (U x) := hU x
  have : IsAffine (V' x) := hV' x
  have : _root_.AlgebraicGeometry.Etale (e.resLE (U x) (V' x) (hle x)) :=
    IsZariskiLocalAtSource.resLE (hle x) inferInstance
  have : HasCompactification (e.resLE (U x) (V' x) (hle x)) :=
    HasCompactification.of_isQuasiAffine _
  have : HasCompactification (U x).ι := (Compactification.ofIsOpenImmersion _).hasCompactification
  exact isIso_dualizingComplexTensorMap_comp_of_forall Λ (e.resLE (U x) (V' x) (hle x)) (U x).ι _
    (Scheme.Hom.resLE_comp_ι _ _) (isIso_dualizingComplexTensorMap_of_quasiCompact Λ _)
    (isInvertible_dualizingComplex_of_etale Λ _) K
    (isIso_dualizingComplexTensorMap_of_isOpenImmersion Λ _ K)

/-- For an étale morphism `e`, the tensor map `Re^! M ⊗ᴸ Le^* N ⟶ Re^!(M ⊗ᴸ N)` is an
isomorphism. -/
theorem isIso_rightDerivedUpperShriekTensorMap_of_etale {X Y : Scheme.{u}} (e : X ⟶ Y)
    [_root_.AlgebraicGeometry.Etale e] [HasCompactification e]
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (rightDerivedUpperShriekTensorMap e M N) :=
  isIso_lowerShriekRightAdjointTensorMap_of_forall (rightDerivedUpperShriekAdjunction Λ e)
    (projectionMapAssociativity Λ e) (isIso_dualizingComplexTensorMap_of_etale Λ e) M N

variable {Λ} in
/-- **Smooth duality for étale morphisms** (the étale case of the proof of blueprint
`proposition-exceptional-inverse-image-smooth-morphism`): for every étale `e` admitting a
compactification, the canonical tensor map `θ_{e,K} : ω_e ⊗ᴸ Le^* K ⟶ Re^! K` is an isomorphism for
every `K`, and `ω_e ≅ Λ`. -/
theorem etaleSmoothDuality : EtaleSmoothDuality Λ := by
  intro V W e _ _
  exact ⟨isIso_dualizingComplexTensorMap_of_etale Λ e, ⟨dualizingComplexIsoOfEtale Λ e⟩⟩

end Etale

end AlgebraicGeometry
