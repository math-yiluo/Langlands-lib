/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-!
# Exceptional admissibility of the trace formula

The trace-formula chapter uses, for a separated finite-type morphism `f : X ⟶ Y` of finite-type
`k`-schemes and a finite coefficient ring `Λ` (a stage `A_{E,n} = 𝒪_E / ϖ_Eⁿ`), the adjunction
`Rf_! ⊣ Rf^!` on the finite-Tor categories `Dctf`, the composition isomorphisms and the
base-change exchange isomorphisms, and the preservation of `Dctf` by `Rf^!` with constants
independent of the coefficient stage. Blueprint `theorem-f-shriek-finite-coefficients` names this
datum
*exceptional admissibility* (`AlgebraicGeometry.Etale.IsExceptionallyAdmissible` at one
coefficient ring, `AlgebraicGeometry.Etale.IsUniformlyExceptionallyAdmissible` at all of them
with uniform constants) and observes that it is a theorem, not a restriction
(`AlgebraicGeometry.Etale.isExceptionallyAdmissible`,
`AlgebraicGeometry.Etale.isUniformlyExceptionallyAdmissible`): it is satisfied by the
constructible exceptional inverse image `Rf^!` of `theorem-f-shriek-ell-adic-coefficients--4` (vi).

This is unrelated to the *ambient* admissibility datum of `sk-def-sf-admissible`
(`AlgebraicGeometry.ProEtale.IsExceptionalAdjointAdmissible`), which fails in general.

## Implementation notes

The data are stated on the small étale sites, where the finite-Tor categories and the
exceptional pair of the six-operations package live; the pro-étale finite-coefficient categories
are identified with them by the comparison of `WeilConjectures.SixFunctors.ProEtale.Comparison`.
The finite coefficient stages are generalised to all finite rings `Λ` whose exponent is
invertible on `Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Exceptional-adjoint admissibility datum.

A separated finite-type morphism `f : X ⟶ Y` over a finite-type `k`-scheme `Y` is
*exceptionally admissible at `Λ`* if

* the compact-support direct image `Rf_! : Dctf(X, Λ) ⥤ Dctf(Y, Λ)` has a right adjoint `Rf^!`
  (with its unit and counit, i.e. an adjunction `Rf_! ⊣ Rf^!`);
* `Rf^!` sends `D_c^[a, b]` with Tor amplitude in `[a, b]` to `D_c^[a - c, b + c]` with Tor
  amplitude in `[a - c, b + c]`, for a constant `c` independent of `a, b`;
* for every `g : Y ⟶ Z` there is a composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` whose
  mate carries the adjunction of `f ≫ g` to the composite adjunction;
* for every cartesian square `g' ≫ f = f' ≫ g` the compact-support exchange
  `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` and its mate `Rg'_* Rf'^! ⟶ Rf^! Rg_*` are isomorphisms.

The condition is a theorem: `AlgebraicGeometry.Etale.isExceptionallyAdmissible`. -/
structure IsExceptionallyAdmissible (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f] : Prop where
  /-- `Rf_!` has a right adjoint on the finite-Tor categories. -/
  exists_adjunction : ∃ G : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X,
    Nonempty (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣ G)
  /-- `Rf^!` preserves the constructible intervals with finite Tor amplitude up to a shift. -/
  exists_shift : ∃ c : ℤ, ∀ (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - c) (b + c)
        ((R(f)^![Λ]).obj K)
  /-- The composition isomorphisms, compatible with the adjunctions. -/
  exists_comp : ∀ {Z : Scheme.{u}} (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aZ]
    [QuasiCompact aZ] [HasInvertibleExponent Λ Z] (g : Y ⟶ Z) [HasCompactification g]
    [QuasiCompact g] [HasCompactification (f ≫ g)],
    ∃ e : DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aZ (f ≫ g) ≅
        DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⋙
          DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aZ g,
      ((DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ (f ≫ g)).ofNatIsoLeft
          e).ofNatIsoRight
        (conjugateIsoEquiv
          ((DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f).comp
            (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ g))
          (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ (f ≫ g)) e).symm =
        (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f).comp
          (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ g)
  /-- The base-change exchange isomorphisms. -/
  isIso_baseChange : ∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g),
    IsIso (rightDerivedLowerShriekBaseChangeMap Λ sq) ∧
      IsIso (rightDerivedUpperShriekLowerStarBaseChangeMap Λ sq)

/-- Every separated finite-type morphism admitting a compactification, over a finite-type
`k`-scheme, is exceptionally admissible at every finite `Λ` whose exponent is invertible on the
base: the constructible exceptional inverse image `Rf^!` provides the datum. -/
theorem isExceptionallyAdmissible (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f] : IsExceptionallyAdmissible Λ aY f where
  exists_adjunction := ⟨_, ⟨DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f⟩⟩
  exists_shift := exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek Λ aY f
  exists_comp aZ _ _ _ g _ _ _ :=
    DerivedCategoryFiniteTor.exists_rightDerivedLowerShriekAdjunction_comp_eq Λ aY aZ f g
  isIso_baseChange _ _ _ _ _ sq :=
    ⟨isIso_rightDerivedLowerShriekBaseChangeMap Λ sq,
      isIso_rightDerivedUpperShriekLowerStarBaseChangeMap Λ sq⟩

/-- The preservation of the constructible intervals by `Rf^!` with a shift independent of the
finite coefficient ring: the shift of
`AlgebraicGeometry.Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek` only
depends on affine charts of `f` and on the dimension of `Y`. -/
theorem exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek_uniform
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] :
    ∃ c : ℤ, ∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ Y] (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - c) (b + c)
          ((R(f)^![Λ]).obj K) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aY
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
  refine ⟨2 * t.sup n + 2 * d + 1, fun Λ _ _ _ a b K hK ↦ ?_⟩
  let Uc : Fin t.card → X.Opens := fun i ↦ (U (t.equivFin.symm i)).1
  refine constructibleTorAmplitudeIn_of_openCover Λ Uc (fun x ↦ ?_) _ fun i ↦ ?_
  · obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨y, hy⟩, by simpa [Uc] using hx⟩
  set x := (t.equivFin.symm i).1
  have hxt : x ∈ t := (t.equivFin.symm i).2
  have : IsAffine ((U x : X.Opens) : Scheme.{u}) := (U x).2
  have : IsAffine ((V x : Y.Opens) : Scheme.{u}) := (V x).2
  have := hc x
  have : TopologicalSpace.NoetherianSpace (U x : X.Opens) :=
    (U x : X.Opens).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (U x : X.Opens).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification (U x : X.Opens).ι :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have hK' := constructibleTorAmplitudeIn_rightDerivedUpperShriek_chart Λ aY (V x : Y.Opens).ι
    (c x) d hd a b hK
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ (U x : X.Opens).ι f
  have heq : ∀ {g₁ g₂ : ((U x : X.Opens) : Scheme.{u}) ⟶ Y} [HasCompactification g₁]
      [HasCompactification g₂], g₁ = g₂ →
      Nonempty (R(g₁)^![Λ] ≅ R(g₂)^![Λ]) := by
    intro g₁ g₂ _ _ h
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨e₂⟩ := heq (hcf x)
  refine constructibleTorAmplitudeIn_of_iso _ (((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ
    (U x : X.Opens).ι).app _).symm ≪≫ (e₁.app K).symm ≪≫ (e₂.app K).symm).symm ?_
  obtain ⟨⟨hbc, hconc⟩, hta⟩ := hK'
  have hn : n x ≤ t.sup n := Finset.le_sup hxt
  exact ⟨⟨hbc, hconc.mono (by omega) (by omega)⟩, hta.mono (by omega) (by omega)⟩

/-- Blueprint `theorem-f-shriek-finite-coefficients`, the stage-independent form: `f`
is *exceptionally admissible* if it is exceptionally admissible at every finite coefficient ring `Λ`
whose exponent is invertible on `Y` (in particular at every stage `A_{E,n}`), with a preservation
constant `c` independent of `Λ`. -/
def IsUniformlyExceptionallyAdmissible (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] : Prop :=
  (∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ Y],
    IsExceptionallyAdmissible Λ aY f) ∧
  ∃ c : ℤ, ∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ Y] (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - c) (b + c)
        ((R(f)^![Λ]).obj K)

/-- Every separated finite-type morphism admitting a compactification, over a finite-type
`k`-scheme, is exceptionally admissible, with stage-independent constants. -/
theorem isUniformlyExceptionallyAdmissible (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    IsUniformlyExceptionallyAdmissible aY f :=
  ⟨fun Λ _ _ _ ↦ isExceptionallyAdmissible Λ aY f,
    exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek_uniform aY f⟩

end AlgebraicGeometry.Etale
