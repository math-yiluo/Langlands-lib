/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-!
# The preservation clauses for smooth and for separated finite-type morphisms

For a finite coefficient ring `Λ` with invertible exponent, the exceptional inverse image `Rf^!`
satisfies the two preservation clauses of exceptional-adjoint admissibility:

* (constructibility) `Rf^!` carries `D_c^[a, b](Y, Λ)` into `D_c^[a', b'](X, Λ)`;
* (finite Tor) `Rf^!` carries bounded constructible complexes of Tor amplitude in `[a, b]` to
  bounded constructible complexes of Tor amplitude in `[a', b']`,

with explicit bounds:

* for `f` smooth of pure relative dimension `d`, `[a', b'] = [a - 2d, b - 2d]`
  (`AlgebraicGeometry.Etale.smooth_preservationClauses`, blueprint
  `theorem-f-shriek-finite-coefficients`), by smooth duality `Rf^! K ≅ Lf^* K ⊗ᴸ L[2d]` with `L`
  locally free of rank one (`proposition-exceptional-inverse-image-smooth-morphism`);
* for `f` separated of finite type, covered by affine charts `U ↪ 𝔸^{d_U}_V` (closed immersions
  over affine opens `V ⊆ Y`) whose open complements `W_U ⊆ 𝔸^{d_U}_V` satisfy the open-complement
  condition with constants `c_U`, `[a', b'] = [a - 2D, b - 2D + c]` for `D ≥ d_U` and
  `c ≥ c_U + 1 + 2(D - d_U)` (`AlgebraicGeometry.Etale.preservationClauses_of_charts`, blueprint
  `theorem-f-shriek-finite-coefficients`);
* the open-complement condition holds with `c_U = 2(d_U + dim Y)`
  (`AlgebraicGeometry.Etale.preservationClauses_of_charts_of_topologicalKrullDim_le`, blueprint
  `theorem-f-shriek-finite-coefficients--1`), and such charts always exist, so every separated
  finite-type `f` satisfies both clauses without any hypothesis
  (`AlgebraicGeometry.Etale.exists_preservationClauses`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- Shifting moves homology concentration: if `K` has homology in `[a, b]`, then `K⟦n⟧` has
homology in `[a - n, b - n]`. -/
lemma homologyConcentratedIn_shift {X : Scheme.{u}}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {a b : ℤ}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) (n : ℤ) :
    _root_.DerivedCategory.homologyConcentratedIn (a - n) (b - n) (K⟦n⟧) := by
  have : _root_.DerivedCategory.TStructure.t.IsGE K a := hK.1
  have : _root_.DerivedCategory.TStructure.t.IsLE K b := hK.2
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_shift K a n (a - n),
    _root_.DerivedCategory.TStructure.t.isLE_shift K b n (b - n)⟩

/-- For a quasi-compact open immersion `j`, `Rj^! = j^*` preserves `D_c^[a, b]`. -/
lemma constructibleIn_rightDerivedUpperShriek_of_isOpenImmersion {U Y : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] [HasCompactification j] [QuasiCompact j] {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b K) :
    DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) U a b
      ((R(j)^![Λ]).obj K) :=
  ⟨(DerivedCategory.boundedConstructible _ U).prop_of_iso
      ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app K).symm
      (hK.1.mapDerivedCategory_upperStar j),
    homologyConcentratedIn_of_iso _ ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app K).symm
      (((j)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hK.2)⟩

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Smooth morphisms satisfy the preservation
clauses.

Let `f : X ⟶ Y` be smooth (and compactifiable, hence separated of finite type) of pure relative
dimension `d`, and `Λ` a finite ring whose exponent is invertible on `Y`. Then `f` satisfies
the two preservation clauses with `c_f^- = c_f^+ = -2d`:

1. (constructibility) `Rf^!` carries `D_c^[a, b](Y, Λ)` into `D_c^[a - 2d, b - 2d](X, Λ)`;
2. (finite Tor amplitude) if `K` is bounded constructible with Tor amplitude in `[a, b]`, then
   `Rf^! K` is bounded constructible with Tor amplitude in `[a - 2d, b - 2d]`.

By smooth duality (`proposition-exceptional-inverse-image-smooth-morphism`,
`proposition-smooth-purity-finite-coefficients--1`) `Rf^! K ≅ Lf^* K ⊗ᴸ ω_f` with `ω_f ≅ L[2d]` for
a locally constant sheaf `L` of free rank-one `Λ`-modules (étale-locally `Λ_X(d)`): `Lf^*` is exact,
tensoring with the flat `L` preserves the homology interval and the Tor amplitude, and `[2d]` shifts
both intervals by `-2d`. The ambient adjoint `Rf^!` is the right adjoint of `Rf_!` on the unbounded
derived categories, which exists unconditionally here. -/
theorem smooth_preservationClauses {X Y : Scheme.{u}} [HasInvertibleExponent Λ Y] (f : X ⟶ Y)
    [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f] :
    (∀ (a b : ℤ) (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b L →
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X (a - 2 * d) (b - 2 * d)
          ((R(f)^![Λ]).obj L)) ∧
    ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
            ((R(f)^![Λ]).obj K) ∧
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * d) (b - 2 * d)
            ((R(f)^![Λ]).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  have : HasInvertibleExponent Λ X := .of_hom f
  refine ⟨fun a b K hK ↦ ?_, fun a b K hbc hta ↦ ?_⟩
  · obtain ⟨L, _, hLs, ⟨eω⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ f d
    obtain ⟨et⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex Λ f d K
    obtain ⟨_, hLf⟩ := isConstructibleSheaf_and_flat_of_sheafFiber_iso Λ L hLs
    have hL₀ := torAmplitudeIn_singleFunctor_zero_of_flat _ L hLf
    obtain ⟨hbc, hab⟩ := hK
    set M := (L((f)^*[ModuleCat.{u + 1} Λ])).obj K
    set L₀ := (_root_.DerivedCategory.singleFunctor _ 0).obj L
    have hMab : _root_.DerivedCategory.homologyConcentratedIn a b M :=
      homologyConcentratedIn_of_iso _
        ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app K).symm
        (((f)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hab)
    have hT : _root_.DerivedCategory.homologyConcentratedIn a b
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj M).obj L₀) := by
      have h := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right
        hMab hL₀
      rw [add_zero, add_zero] at h
      exact h
    have hMbc := boundedConstructible_tensor Λ X (boundedConstructible_leftDerivedUpperStar _ f hbc)
      (DerivedCategory.boundedConstructible_singleFunctor_obj L 0) ⟨0, 0, hL₀⟩
    let e : (R(f)^![Λ]).obj K ≅
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj M).obj L₀)⟦(2 * d : ℤ)⟧ :=
      et.symm ≪≫ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj M).mapIso eω ≪≫
        ((((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj M).commShiftIso (2 * d : ℤ)).app L₀)
    exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e.symm
        ((DerivedCategory.boundedConstructible _ X).le_shift _ _ hMbc),
      homologyConcentratedIn_of_iso _ e.symm (homologyConcentratedIn_shift Λ hT _)⟩
  · have h := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension Λ
      f d a b ⟨⟨hbc, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta⟩, hta⟩
    exact ⟨h.1.1, h.2⟩

/-- The chart step of `theorem-f-shriek-finite-coefficients`: for a closed immersion
`c : U ⟶ 𝔸ⁿ_V` over an affine open `v : V ⟶ Y`, whose open complement `j : W ⟶ 𝔸ⁿ_V` satisfies
the open-complement condition with constant `c_U`, `R(c ≫ π ≫ v)^!` carries `[a, b]` to
`[a - 2n, b - 2n + c_U + 1]`, in both preservation clauses: `Rv^! = v^*`, the smooth clause for
`π : 𝔸ⁿ_V ⟶ V` and the closed-immersion clauses (`theorem-f-shriek-finite-coefficients--1`,
`theorem-f-shriek-finite-coefficients--1`). -/
theorem preservationClauses_closedChart {k : Type u} [Field k] {U V W Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (v : V ⟶ Y) [IsOpenImmersion v] [IsAffine V] {n : ℕ}
    (c : U ⟶ 𝔸(ULift.{u} (Fin n); V)) [IsClosedImmersion c]
    (j : W ⟶ 𝔸(ULift.{u} (Fin n); V)) [IsOpenImmersion j]
    (hcj : Set.range c.base = (Set.range j.base)ᶜ) {cU : ℕ}
    (hOC : OpenComplementCondition Λ j cU)
    [HasCompactification (c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)] :
    (∀ (a b : ℤ) (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b L →
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) U (a - 2 * n)
          (b - 2 * n + cU + 1)
          ((R(c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)^![Λ]).obj L)) ∧
    ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) U
            ((R(c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)^![Λ]).obj K) ∧
          torAmplitudeIn (ModuleCat.{u + 1} Λ) U (a - 2 * n) (b - 2 * n + cU + 1)
            ((R(c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)^![Λ]).obj K) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  let π := 𝔸(ULift.{u} (Fin n); V) ↘ V
  have : TopologicalSpace.NoetherianSpace V := v.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact v := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  have : IsNoetherian V := {}
  have : IsLocallyNoetherian 𝔸(ULift.{u} (Fin n); V) := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian 𝔸(ULift.{u} (Fin n); V) := {}
  have : TopologicalSpace.NoetherianSpace U := c.isClosedEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (π ≫ v) := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : QuasiCompact (c ≫ π ≫ v) := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification v := (Compactification.ofIsOpenImmersion v).hasCompactification
  have : HasInvertibleExponent Λ V := HasInvertibleExponent.of_hom v
  have : SmoothOfRelativeDimension n π := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) V
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ c (π ≫ v)
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ π v
  have e (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      (R(c ≫ π ≫ v)^![Λ]).obj K ≅ (R(c)^![Λ]).obj
        ((R(π)^![Λ]).obj ((R(v)^![Λ]).obj K)) :=
    e₁.app K ≪≫ (R(c)^![Λ]).mapIso (e₂.app K)
  have hπ := smooth_preservationClauses Λ π n
  refine ⟨fun a b K hK ↦ ?_, fun a b K hbc hta ↦ ?_⟩
  · have h₁ := constructibleIn_rightDerivedUpperShriek_of_isOpenImmersion Λ v hK
    have h₂ := hπ.1 a b _ h₁
    have h₃ := constructibleIn_rightDerivedUpperShriek c j hcj hOC h₂
    exact ⟨(DerivedCategory.boundedConstructible _ U).prop_of_iso (e K).symm h₃.1,
      homologyConcentratedIn_of_iso _ (e K).symm h₃.2⟩
  · obtain ⟨⟨hb₁, -⟩, ht₁⟩ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion
      Λ v a b ⟨⟨hbc, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta⟩, hta⟩
    obtain ⟨hb₂, ht₂⟩ := hπ.2 a b _ hb₁ ht₁
    obtain ⟨hb₃, ht₃⟩ := boundedConstructible_torAmplitudeIn_rightDerivedUpperShriek c j hcj hOC
      hb₂ ht₂
    exact ⟨(DerivedCategory.boundedConstructible _ U).prop_of_iso (e K).symm hb₃,
      (torAmplitudeIn (ModuleCat.{u + 1} Λ) U _ _).prop_of_iso (e K).symm ht₃⟩

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Preservation for an affine base, modulo the
open-complement condition.

Let `f : X ⟶ Y` be separated of finite type (compactifiable and quasi-compact), with `Y` of
finite type over a field `k`, and `Λ` a finite ring whose exponent is invertible on `Y`. Let
`U₁, …, U_m` be affine opens covering `X` and `V₁, …, V_m` affine opens of `Y`, with closed
immersions `cᵢ : Uᵢ ⟶ 𝔸^{dᵢ}_{Vᵢ}` over `Vᵢ` (so `f ∣_{Uᵢ}` is `cᵢ` followed by the projection and
`Vᵢ ⊆ Y`), and let `jᵢ : Wᵢ ⟶ 𝔸^{dᵢ}_{Vᵢ}` be the open complements. Assume the open-complement
condition (`theorem-f-shriek-finite-coefficients--1`) for every pair `(Wᵢ, 𝔸^{dᵢ}_{Vᵢ})` with
constant `cᵢ'`, and let `D ≥ dᵢ` and `c ≥ cᵢ' + 1 + 2(D - dᵢ)` for all `i` (the blueprint takes
`D = maxᵢ dᵢ` and `c = maxᵢ (cᵢ' + 1 + 2(D - dᵢ))`). Then:

1. `Rf^!` carries `D_c^[a, b](Y, Λ)` into `D_c^[a - 2D, b - 2D + c](X, Λ)`;
2. if `K` is bounded constructible with Tor amplitude in `[a, b]`, then `Rf^! K` is bounded
   constructible with Tor amplitude in `[a - 2D, b - 2D + c]`.

Both clauses are local on `X`, and on the chart `Uᵢ` the exceptional inverse image is
`Rcᵢ^! Rπᵢ^! Rvᵢ^!` (`AlgebraicGeometry.Etale.preservationClauses_closedChart`). The ambient
right adjoint `Rf^!` exists unconditionally. -/
theorem preservationClauses_of_charts {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] {m : ℕ}
    (U : Fin m → X.affineOpens) (hU : ∀ x, ∃ i, x ∈ (U i : X.Opens)) (V : Fin m → Y.affineOpens)
    (n : Fin m → ℕ)
    (c : ∀ i, ((U i : X.Opens) : Scheme.{u}) ⟶ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)))
    [∀ i, IsClosedImmersion (c i)]
    (hc : ∀ i, c i ≫ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)) ↘ _ ≫ (V i : Y.Opens).ι =
      (U i : X.Opens).ι ≫ f)
    (W : Fin m → Scheme.{u}) (j : ∀ i, W i ⟶ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)))
    [∀ i, IsOpenImmersion (j i)] (hcj : ∀ i, Set.range (c i).base = (Set.range (j i).base)ᶜ)
    (cU : Fin m → ℕ) (hOC : ∀ i, OpenComplementCondition Λ (j i) (cU i)) (D C : ℕ)
    (hD : ∀ i, n i ≤ D) (hC : ∀ i, cU i + 1 + 2 * (D - n i) ≤ C) :
    (∀ (a b : ℤ) (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b L →
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b - 2 * D + C)
          ((R(f)^![Λ]).obj L)) ∧
    ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
            ((R(f)^![Λ]).obj K) ∧
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b - 2 * D + C)
            ((R(f)^![Λ]).obj K) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  -- the restriction of `Rf^! K` to the chart `Uᵢ` is `R(cᵢ ≫ πᵢ ≫ vᵢ)^! K`
  have hres (i : Fin m)
      (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      Nonempty ((D(((U i : X.Opens).ι)^*[ModuleCat.{u + 1} Λ])).obj
          ((R(f)^![Λ]).obj K) ≅
        (R(c i ≫ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)) ↘ _ ≫
          (V i : Y.Opens).ι)^![Λ]).obj K) := by
    have : TopologicalSpace.NoetherianSpace (U i : X.Opens) :=
      (U i : X.Opens).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (U i : X.Opens).ι :=
      ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    have : QuasiCompact ((U i : X.Opens).ι ≫ f) :=
      ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    have : HasCompactification (U i : X.Opens).ι :=
      (Compactification.ofIsOpenImmersion _).hasCompactification
    obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ (U i : X.Opens).ι f
    have heq : ∀ {g₁ g₂ : ((U i : X.Opens) : Scheme.{u}) ⟶ Y} [HasCompactification g₁]
        [HasCompactification g₂], g₁ = g₂ →
        Nonempty (R(g₁)^![Λ] ≅ R(g₂)^![Λ]) := by
      intro g₁ g₂ _ _ h
      subst h
      exact ⟨Iso.refl _⟩
    obtain ⟨e₂⟩ := heq (hc i)
    exact ⟨((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ (U i : X.Opens).ι).app _).symm ≪≫
      (e₁.app K).symm ≪≫ (e₂.app K).symm⟩
  have hchart := fun i ↦
    preservationClauses_closedChart Λ aY (V i : Y.Opens).ι (c i) (j i) (hcj i) (hOC i)
  have hb (i : Fin m) (a b : ℤ) : (a - 2 * D : ℤ) ≤ a - 2 * (n i : ℕ) ∧
      (b - 2 * (n i : ℕ) + cU i + 1 : ℤ) ≤ b - 2 * D + C := by
    have := hD i
    have := hC i
    omega
  refine ⟨fun a b K hK ↦ ?_, fun a b K hbc hta ↦ ?_⟩
  · refine ⟨boundedConstructible_of_openCover Λ (fun i ↦ (U i : X.Opens)) hU _ fun i ↦ ?_,
      homologyConcentratedIn_of_openCover _ (fun i ↦ (U i : X.Opens)) hU _ fun i ↦ ?_⟩
    · exact (DerivedCategory.boundedConstructible _ _).prop_of_iso (hres i K).some.symm
        ((hchart i).1 a b K hK).1
    · exact homologyConcentratedIn_of_iso _ (hres i K).some.symm
        (((hchart i).1 a b K hK).2.mono (hb i a b).1 (hb i a b).2)
  · refine ⟨boundedConstructible_of_openCover Λ (fun i ↦ (U i : X.Opens)) hU _ fun i ↦ ?_,
      torAmplitudeIn_of_openCover _ (fun i ↦ (U i : X.Opens)) hU _ fun i ↦ ?_⟩
    · exact (DerivedCategory.boundedConstructible _ _).prop_of_iso (hres i K).some.symm
        ((hchart i).2 a b K hbc hta).1
    · exact (torAmplitudeIn (ModuleCat.{u + 1} Λ) _ _ _).prop_of_iso (hres i K).some.symm
        (((hchart i).2 a b K hbc hta).2.mono (hb i a b).1 (hb i a b).2)

/-- The open-complement condition for an open subscheme `W` of an affine space `𝔸ⁿ_V` over an
affine open `V` of a finite-type `k`-scheme `Y` with `dim Y ≤ d_Y`: it holds with the constant
`2(d_Y + n)`, independently of `Λ` (`theorem-f-shriek-finite-coefficients--1`, as
`dim 𝔸ⁿ_V ≤ d_Y + n`). -/
theorem openComplementCondition_affineSpace {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] (dY : ℕ)
    (hY : topologicalKrullDim Y ≤ (dY : WithBot ℕ∞)) (V : Y.affineOpens) (n : ℕ)
    {W : Scheme.{u}} (j : W ⟶ 𝔸(ULift.{u} (Fin n); (V : Y.Opens))) [IsOpenImmersion j] :
    OpenComplementCondition Λ j (2 * (dY + n)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  let π := 𝔸(ULift.{u} (Fin n); (V : Y.Opens)) ↘ (V : Y.Opens)
  let v := (V : Y.Opens).ι
  have : TopologicalSpace.NoetherianSpace (V : Y.Opens) :=
    v.isOpenEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian (V : Y.Opens) := isLocallyNoetherian_of_isOpenImmersion v
  have : IsNoetherian (V : Y.Opens) := {}
  have : IsNoetherianRing Γ((V : Y.Opens), ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsLocallyNoetherian 𝔸(ULift.{u} (Fin n); (V : Y.Opens)) :=
    LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian 𝔸(ULift.{u} (Fin n); (V : Y.Opens)) := {}
  have : TopologicalSpace.NoetherianSpace W := j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : QuasiCompact (π ≫ v ≫ aY) :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hdim : topologicalKrullDim 𝔸(ULift.{u} (Fin n); (V : Y.Opens)) ≤
      ((dY + n : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_affineSpace_of_isAffine]
    have hV := (v.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hY
    simp only [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_fin, Nat.cast_add]
    exact add_le_add hV le_rfl
  exact openComplementCondition_two_mul (π ≫ v ≫ aY) j (dY + n) hdim

/-- Blueprint `theorem-f-shriek-finite-coefficients--1`: Preservation for a general separated
finite-type morphism.

In the situation of `AlgebraicGeometry.Etale.preservationClauses_of_charts`
(`theorem-f-shriek-finite-coefficients`), with closed affine charts `cᵢ : Uᵢ ⟶ 𝔸^{dᵢ}_{Vᵢ}` of `f`
and without assuming the open-complement condition: let `Λ` be a finite ring whose exponent is
invertible in `k`, `dim Y ≤ d_Y` and `D ≥ dᵢ` for all `i`. The open complement
`Wᵢ = 𝔸^{dᵢ}_{Vᵢ} ∖ Uᵢ` satisfies the open-complement condition with `cᵢ' = 2(dᵢ + d_Y)`
(`theorem-f-shriek-finite-coefficients--1`, as `dim 𝔸^{dᵢ}_{Vᵢ} ≤ dᵢ + d_Y`), so with
`c = 2D + 2d_Y + 1 = maxᵢ (cᵢ' + 1 + 2(D - dᵢ))` (for `D = maxᵢ dᵢ`) the two preservation
clauses hold with the interval `[a - 2D, b - 2D + c] = [a - 2D, b + 2d_Y + 1]`:

1. `Rf^!` carries `D_c^[a, b](Y, Λ)` into `D_c^[a - 2D, b + 2d_Y + 1](X, Λ)`;
2. `Rf^!` carries bounded constructible complexes of Tor amplitude in `[a, b]` to bounded
   constructible complexes of Tor amplitude in `[a - 2D, b + 2d_Y + 1]`. -/
theorem preservationClauses_of_charts_of_topologicalKrullDim_le {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] (dY : ℕ)
    (hY : topologicalKrullDim Y ≤ (dY : WithBot ℕ∞)) {m : ℕ}
    (U : Fin m → X.affineOpens) (hU : ∀ x, ∃ i, x ∈ (U i : X.Opens)) (V : Fin m → Y.affineOpens)
    (n : Fin m → ℕ)
    (c : ∀ i, ((U i : X.Opens) : Scheme.{u}) ⟶ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)))
    [∀ i, IsClosedImmersion (c i)]
    (hc : ∀ i, c i ≫ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)) ↘ _ ≫ (V i : Y.Opens).ι =
      (U i : X.Opens).ι ≫ f)
    (D : ℕ) (hD : ∀ i, n i ≤ D) :
    (∀ (a b : ℤ) (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b L →
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * dY + 1)
          ((R(f)^![Λ]).obj L)) ∧
    ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
            ((R(f)^![Λ]).obj K) ∧
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * dY + 1)
            ((R(f)^![Λ]).obj K) := by
  have : HasInvertibleExponent Λ Y := .of_hom aY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  -- the open complements of the charts
  let W (i : Fin m) : (𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens))).Opens :=
    ⟨(Set.range (c i).base)ᶜ, (c i).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hcj (i : Fin m) : Set.range (c i).base = (Set.range (W i).ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hOC (i : Fin m) : OpenComplementCondition Λ (W i).ι (2 * (dY + n i)) :=
    openComplementCondition_affineSpace Λ aY dY hY (V i) (n i) (W i).ι
  have h := preservationClauses_of_charts Λ aY f U hU V n c hc (fun i ↦ W i) (fun i ↦ (W i).ι)
    hcj (fun i ↦ 2 * (dY + n i)) hOC D (2 * D + 2 * dY + 1) hD (fun i ↦ by have := hD i; omega)
  have hC (b : ℤ) : b - 2 * (D : ℤ) + ((2 * D + 2 * dY + 1 : ℕ) : ℤ) = b + 2 * dY + 1 := by
    push_cast; ring
  exact ⟨fun a b L hL ↦ hC b ▸ h.1 a b L hL, fun a b K hbc hta ↦ hC b ▸ h.2 a b K hbc hta⟩

/-- Every separated finite-type morphism `f : X ⟶ Y` (compactifiable and quasi-compact) over a
finite-type `k`-scheme `Y` satisfies both preservation clauses, without any hypothesis, for every
finite `Λ` whose exponent is invertible in `k`: there is `D` (the maximal dimension of the affine
spaces of a finite family of closed affine charts of `f`, which exist by
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_of_isAffine`) such that for `dim Y ≤ d_Y`
the exceptional inverse image `Rf^!` carries `[a, b]` to `[a - 2D, b + 2d_Y + 1]` in both clauses
(`AlgebraicGeometry.Etale.preservationClauses_of_charts_of_topologicalKrullDim_le`,
`theorem-f-shriek-finite-coefficients--1`). -/
theorem exists_preservationClauses {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    ∃ D : ℕ, ∀ dY : ℕ, topologicalKrullDim Y ≤ (dY : WithBot ℕ∞) →
    (∀ (a b : ℤ) (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b L →
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * dY + 1)
          ((R(f)^![Λ]).obj L)) ∧
    ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
            ((R(f)^![Λ]).obj K) ∧
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * dY + 1)
            ((R(f)^![Λ]).obj K) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  -- affine charts `U ⊆ f⁻¹ V`
  have hchart (x : X) : ∃ (U : X.affineOpens) (V : Y.affineOpens),
      x ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens) := by
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show f.base x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUV⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ f ⁻¹ᵁ V from hxV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxU, hUV⟩
  choose U V hxU hUV using hchart
  -- closed immersions of the charts into affine spaces over the `V`
  have hemb (x : X) : ∃ (n : ℕ) (c : ((U x : X.Opens) : Scheme.{u}) ⟶
      𝔸(ULift.{u} (Fin n); (V x : Y.Opens))), IsClosedImmersion c ∧
      c ≫ 𝔸(ULift.{u} (Fin n); (V x : Y.Opens)) ↘ _ ≫ (V x : Y.Opens).ι =
        (U x : X.Opens).ι ≫ f := by
    have hr : Set.range ((U x : X.Opens).ι ≫ f).base ⊆ Set.range (V x : Y.Opens).ι.base := by
      rintro - ⟨y, rfl⟩
      simpa using hUV x y.2
    let g := IsOpenImmersion.lift (V x : Y.Opens).ι ((U x : X.Opens).ι ≫ f) hr
    have hg : g ≫ (V x : Y.Opens).ι = (U x : X.Opens).ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have : LocallyOfFiniteType (g ≫ (V x : Y.Opens).ι) := by rw [hg]; infer_instance
    have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (V x : Y.Opens).ι
    obtain ⟨n, c, hc, hcl⟩ := exists_isClosedImmersion_affineSpace_of_isAffine g
    exact ⟨n, c, hcl, by rw [← Category.assoc, hc, hg]⟩
  choose n c hc hcf using hemb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((U x : X.Opens) : Set X))
    (fun x ↦ (U x : X.Opens).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxU x⟩)
  let pt : Fin t.card → X := fun i ↦ (t.equivFin.symm i).1
  have : ∀ i, IsClosedImmersion (c (pt i)) := fun i ↦ hc (pt i)
  refine ⟨t.sup n, fun dY hY ↦ preservationClauses_of_charts_of_topologicalKrullDim_le Λ aY f dY
    hY (fun i ↦ U (pt i)) (fun x ↦ ?_) (fun i ↦ V (pt i)) (fun i ↦ n (pt i)) (fun i ↦ c (pt i))
    (fun i ↦ hcf (pt i)) _ fun i ↦ Finset.le_sup (t.equivFin.symm i).2⟩
  obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa [pt] using hx⟩

end Etale

end AlgebraicGeometry
