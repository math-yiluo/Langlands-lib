/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-!
# The exceptional inverse image preserves bounded constructibility

For a separated finite-type morphism `f : X ⟶ Y` over a finite-type `k`-scheme `Y` and a finite
`Λ` whose exponent is invertible on `Y`, the exceptional inverse image `Rf^!` carries `Dᵇc(Y, Λ)`
into `Dᵇc(X, Λ)`. This is the bounded constructible half of `theorem-f-shriek-finite-coefficients`
(iv), without any Tor-amplitude condition, and it is what makes the exceptional adjunction of the
six-functor datum `def-fix-six-functor-datum` (4) restrict to the bounded constructible
categories (`fix-prop-adjunctions` (2)).

The proof follows the one of clause (iv) with amplitudes
(`exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le`),
dropping the amplitudes: localise to affine charts `U ↪ 𝔸ⁿ_V ⟶ V`; for an open immersion
`Rj^! = j^*`; for the smooth projection `Rπ^! K ≅ Lπ^* K ⊗ᴸ L[2n]` with `L` locally constant of
rank one; for a closed immersion `i` with open complement `j`, the localization triangle
`Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` and the finiteness theorem for `Rj_*`.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedUpperShriek`
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

/-- For a quasi-compact open immersion `j`, `Rj^! = j^*` preserves bounded constructibility. -/
theorem boundedConstructible_rightDerivedUpperShriek_of_isOpenImmersion {U Y : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] [HasCompactification j]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) U ((R(j)^![Λ]).obj K) :=
  (boundedConstructible _ U).prop_of_iso
    ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app K).symm
    (hK.mapDerivedCategory_upperStar j)

/-- For `f` smooth of pure relative dimension `d` and a finite `Λ` whose exponent is invertible on
`Y`, `Rf^! K ≅ Lf^* K ⊗ᴸ L[2d]` with `L` flat, locally constant and constructible, so `Rf^!`
preserves bounded constructibility. -/
theorem boundedConstructible_rightDerivedUpperShriek_of_smoothOfRelativeDimension
    {X Y : Scheme.{u}} [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  have : HasInvertibleExponent Λ X := .of_hom f
  obtain ⟨L, _, hLs, ⟨eω⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ f d
  obtain ⟨et⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex Λ f d K
  obtain ⟨_, hLf⟩ := isConstructibleSheaf_and_flat_of_sheafFiber_iso Λ L hLs
  have hL₀ := torAmplitudeIn_singleFunctor_zero_of_flat _ L hLf
  have hMbc := boundedConstructible_tensor Λ X (boundedConstructible_leftDerivedUpperStar _ f hK)
    (DerivedCategory.boundedConstructible_singleFunctor_obj L 0) ⟨0, 0, hL₀⟩
  exact (boundedConstructible _ X).prop_of_iso (et.symm ≪≫
    ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj _).mapIso eω ≪≫
    ((((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj _).commShiftIso (2 * d : ℤ)).app _)).symm
    ((boundedConstructible _ X).le_shift _ _ hMbc)

/-- For a closed immersion `i : Z ⟶ T` into a finite-type `k`-scheme and a finite `Λ` whose
exponent is invertible on `T`, `Ri^!` preserves bounded constructibility: in the localization
triangle `Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` for the open complement `j`, the third term is bounded
constructible by the finiteness theorem, hence so is `Ri_! Ri^! K`, and
`Ri^! K ≅ i^* Ri_! Ri^! K`. -/
theorem boundedConstructible_rightDerivedUpperShriek_of_isClosedImmersion
    {Z T : Scheme.{u}} (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    [HasInvertibleExponent Λ T] (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) T K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) Z ((R(i)^![Λ]).obj K) := by
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  have : IsNoetherian T := { __ := LocallyOfFiniteType.isLocallyNoetherian aT }
  let V := openComplementOfIsClosedImmersion i
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hij : Set.range i.base = (Set.range V.ι.base)ᶜ := by
    simp [V, openComplementOfIsClosedImmersion]
  have hM := boundedConstructible_rightDerivedLowerStar_of_finite Λ (V.ι ≫ aT) aT V.ι rfl
    (boundedConstructible_leftDerivedUpperStar _ V.ι hK)
  have hT := supportedLocalizationTriangle_mem_distTriang Λ i V.ι hij K
  have hNbc := (boundedConstructible (ModuleCat.{u + 1} Λ) T).ext_of_isTriangulatedClosed₂ _
    (Pretriangulated.inv_rot_of_distTriang _ hT) ((boundedConstructible _ T).le_shift (-1) _ hM) hK
  exact (boundedConstructible _ Z).prop_of_iso
    ((mapDerivedCategoryUpperStarRightDerivedLowerShriekIso (ModuleCat.{u + 1} Λ) i).app _)
    (hNbc.mapDerivedCategory_upperStar i)

/-- The chart step: for an immersion `c : U ⟶ 𝔸ⁿ_V` over an affine open `v : V ⟶ Y`,
`R(c ≫ π ≫ v)^!` preserves bounded constructibility. -/
theorem boundedConstructible_rightDerivedUpperShriek_chart {U V Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (v : V ⟶ Y) [IsOpenImmersion v] [IsAffine V] {n : ℕ}
    (c : U ⟶ 𝔸(ULift.{u} (Fin n); V)) [IsImmersion c] [IsAffine U]
    [HasCompactification (c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) U
      ((R(c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)^![Λ]).obj K) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  let π := 𝔸(ULift.{u} (Fin n); V) ↘ V
  let W := c.coborderRange
  let ι := c.liftCoborder
  have : TopologicalSpace.NoetherianSpace V := v.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact v := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  have : IsNoetherian V := {}
  have : IsNoetherianRing Γ(V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V⟩
  have : IsLocallyNoetherian 𝔸(ULift.{u} (Fin n); V) := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian 𝔸(ULift.{u} (Fin n); V) := {}
  have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification v := (Compactification.ofIsOpenImmersion v).hasCompactification
  have : HasCompactification W.ι := (Compactification.ofIsOpenImmersion W.ι).hasCompactification
  have : HasCompactification ι := (Compactification.ofIsProper ι).hasCompactification
  have : HasInvertibleExponent Λ V := HasInvertibleExponent.of_hom v
  have : HasInvertibleExponent Λ W := HasInvertibleExponent.of_hom (W.ι ≫ π ≫ v)
  have : SmoothOfRelativeDimension n π := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) V
  have h₁ := boundedConstructible_rightDerivedUpperShriek_of_isOpenImmersion Λ v hK
  have h₂ := boundedConstructible_rightDerivedUpperShriek_of_smoothOfRelativeDimension Λ π n h₁
  have h₃ := boundedConstructible_rightDerivedUpperShriek_of_isOpenImmersion Λ W.ι h₂
  have h₄ := boundedConstructible_rightDerivedUpperShriek_of_isClosedImmersion Λ
    (W.ι ≫ π ≫ v ≫ aY) ι h₃
  have hc : c ≫ π ≫ v = ι ≫ W.ι ≫ π ≫ v := by
    rw [← Category.assoc ι, c.liftCoborder_ι]
  have heq : ∀ {g₁ g₂ : U ⟶ Y} [HasCompactification g₁] [HasCompactification g₂], g₁ = g₂ →
      Nonempty (R(g₁)^![Λ] ≅ R(g₂)^![Λ]) := by
    intro g₁ g₂ _ _ h
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨e₀⟩ := heq hc
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ ι (W.ι ≫ π ≫ v)
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ W.ι (π ≫ v)
  obtain ⟨e₃⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ π v
  exact (boundedConstructible _ U).prop_of_iso ((e₀ ≪≫ e₁ ≪≫ Functor.isoWhiskerRight e₂ _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight e₃ _) _).app K).symm h₄

/-- The exceptional inverse image preserves bounded constructibility: for a separated
finite-type `f : X ⟶ Y` admitting a compactification, over a finite-type `k`-scheme `Y`, and a
finite `Λ` whose exponent is invertible on `Y`, `Rf^!` carries `Dᵇc(Y, Λ)` into `Dᵇc(X, Λ)`. This
is the constructibility part of `theorem-f-shriek-finite-coefficients` (iv), with no Tor-amplitude
condition; it makes `Rf^! : Dᵇc(Y, Λ) ⥤ Dᵇc(X, Λ)` of `def-fix-six-functor-datum` (4) defined. -/
theorem boundedConstructible_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj K) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  -- affine charts `U ⊆ f⁻¹ V`
  have hchart (x : X) : ∃ (U : X.affineOpens) (V : Y.affineOpens),
      x ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens) := by
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show f.base x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ f ⁻¹ᵁ V from hxV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxU, hUV⟩
  choose U V hxU hUV using hchart
  -- immersions of the charts into affine spaces over the `V`
  have hemb (x : X) : ∃ (n : ℕ) (c : ((U x : X.Opens) : Scheme.{u}) ⟶
      𝔸(ULift.{u} (Fin n); (V x : Y.Opens))), IsImmersion c ∧
      c ≫ 𝔸(ULift.{u} (Fin n); (V x : Y.Opens)) ↘ _ ≫ (V x : Y.Opens).ι =
        (U x : X.Opens).ι ≫ f := by
    have hr : Set.range ((U x : X.Opens).ι ≫ f).base ⊆ Set.range (V x : Y.Opens).ι.base := by
      rintro - ⟨y, rfl⟩
      simpa using hUV x y.2
    let g := IsOpenImmersion.lift (V x : Y.Opens).ι ((U x : X.Opens).ι ≫ f) hr
    have hg : g ≫ (V x : Y.Opens).ι = (U x : X.Opens).ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have : LocallyOfFiniteType (g ≫ (V x : Y.Opens).ι) := by rw [hg]; infer_instance
    have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (V x : Y.Opens).ι
    have : IsAffine ((U x : X.Opens) : Scheme.{u}) := (U x).2
    obtain ⟨n, c, hc, himm⟩ := exists_immersion_affineSpace_of_quasiAffine g
    exact ⟨n, c, himm, by rw [← Category.assoc, hc, hg]⟩
  choose n c hc hcf using hemb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((U x : X.Opens) : Set X))
    (fun x ↦ (U x : X.Opens).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxU x⟩)
  let Uc : Fin t.card → X.Opens := fun i ↦ (U (t.equivFin.symm i)).1
  refine boundedConstructible_of_openCover Λ Uc (fun x ↦ ?_) _ fun i ↦ ?_
  · obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨y, hy⟩, by simpa [Uc] using hx⟩
  set x := (t.equivFin.symm i).1
  have : IsAffine ((U x : X.Opens) : Scheme.{u}) := (U x).2
  have : IsAffine ((V x : Y.Opens) : Scheme.{u}) := (V x).2
  have := hc x
  have : TopologicalSpace.NoetherianSpace (U x : X.Opens) :=
    (U x : X.Opens).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (U x : X.Opens).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification (U x : X.Opens).ι :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have hK' := boundedConstructible_rightDerivedUpperShriek_chart Λ aY (V x : Y.Opens).ι (c x) hK
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ (U x : X.Opens).ι f
  have heq : ∀ {g₁ g₂ : ((U x : X.Opens) : Scheme.{u}) ⟶ Y} [HasCompactification g₁]
      [HasCompactification g₂], g₁ = g₂ →
      Nonempty (R(g₁)^![Λ] ≅ R(g₂)^![Λ]) := by
    intro g₁ g₂ _ _ h
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨e₂⟩ := heq (hcf x)
  exact (boundedConstructible _ _).prop_of_iso (((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ
    (U x : X.Opens).ι).app _).symm ≪≫ (e₁.app K).symm ≪≫ (e₂.app K).symm).symm hK'

end Etale

end AlgebraicGeometry
