/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Explicit
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenComplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso

/-!
# Preservation for the exceptional inverse image of a general morphism

Let `f : X ⟶ Y` be a separated finite-type morphism of finite-type schemes over a field `k`, and
`Λ` a finite ring whose exponent is invertible on `Y`. Cover `X` by finitely many affine charts
`U ⊆ f⁻¹(V)` over affine opens `V ⊆ Y`, each presented as a closed subscheme
`c_U : U ⟶ 𝔸^{d_U}_V`, with open complement `W_U`. This file proves the chartwise assembly of
the preservation clauses for `Rf^!`:

- `AlgebraicGeometry.Etale.preservation_rightDerivedUpperShriek_of_charts`: if each pair
  `(W_U, 𝔸^{d_U}_V)` satisfies the open-complement condition with constant `c_U`, then `Rf^!`
  sends `D_c^[a, b]` into `D_c^[a - 2D, b - 2D + c]`, where `D ≥ d_U` and
  `c ≥ c_U + 1 + 2 (D - d_U)` for all charts; the same holds for the Tor amplitude as soon as the
  direct images along the `W_U ⟶ 𝔸^{d_U}_V` move the Tor amplitude by at most `c_U`.

## Main statements

- `Etale.preservation_rightDerivedUpperShriek_of_openComplementBound_constructible`
  (`theorem-f-shriek-finite-coefficients`, constructibility clause).
- `AlgebraicGeometry.Etale.preservation_rightDerivedUpperShriek_unconditional`
  (`theorem-f-shriek-finite-coefficients--1`): the open-complement condition holds with
  `c_U = 2 (d_U + dim Y)` over a separably closed field.
- `AlgebraicGeometry.Etale.preservation_rightDerivedUpperShriek_class`
  (`theorem-f-shriek-finite-coefficients--1`): `Rf^!` sends `D_c^[a, b]` into
  `D_c^[a - 2D, b + 2 dim Y + 1]`, with the same Tor bound, at every finite coefficient ring at
  once.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-! ### The direct image along the open complement -/

section DirectImage

omit [Finite Λ] in
/-- Under the open-complement condition with constant `e`, the direct image of a constructible
sheaf placed in degree `0` is bounded constructible and concentrated in `[0, e]`. -/
lemma boundedConstructible_rightDerivedLowerStar_singleFunctor_of_openComplementBound
    {V T : Scheme.{u}} {j : V ⟶ T} {e : ℕ} (hj : OpenComplementBound Λ j e)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    boundedConstructible (ModuleCat.{u + 1} Λ) T
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ∧
      _root_.DerivedCategory.homologyConcentratedIn 0 e
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  have hge := ((j)_*[ModuleCat.{u + 1} Λ]).isGE_rightDerivedFunctor_obj_singleFunctor F
  have hle : _root_.DerivedCategory.TStructure.t.IsLE
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) e :=
    (_root_.DerivedCategory.isLE_iff _ _).2 fun q hq ↦
      (hj.1 F q hq).of_iso (higherDirectImageIsoHomologyRightDerivedLowerStar Λ j q F).symm
  refine ⟨⟨⟨⟨0, hge⟩, ⟨e, hle⟩⟩, fun q ↦ ?_⟩, hge, hle⟩
  have := hj.2 F ‹_› q
  exact IsConstructibleSheaf.of_iso (higherDirectImageIsoHomologyRightDerivedLowerStar Λ j q F)

open _root_.DerivedCategory in
/-- **Dévissage for the direct image under the open-complement condition.** Under the
open-complement condition with constant `e`, the direct image of a complex with constructible
homology concentrated in `[a, a + m - 1]` is bounded constructible and concentrated in
`[a, a + m - 1 + e]`: by induction on `m`, along the truncation triangle
`τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶` with `b = a + m - 1`, whose third term is `Hᵇ K` placed in
degree `b`. -/
lemma boundedConstructible_rightDerivedLowerStar_of_openComplementBound_aux
    {V T : Scheme.{u}} {j : V ⟶ T} {e : ℕ} (hj : OpenComplementBound Λ j e) (m : ℕ) :
    ∀ (a : ℤ) (K : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      K.IsGE a → K.IsLE (a + m - 1) →
      (∀ q, IsConstructibleSheaf ((homologyFunctor _ q).obj K)) →
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T
          ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K) ∧
        TStructure.t.IsGE ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K) a ∧
        TStructure.t.IsLE ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K) (a + m - 1 + e) := by
  have : IsNoetherianRing Λ := inferInstance
  induction m with
  | zero =>
    intro a K _ _ _
    have : K.IsLE (a - 1) := by simpa using ‹K.IsLE (a + ↑(0 : ℕ) - 1)›
    have hK := (R((j)_*[ModuleCat.{u + 1} Λ])).map_isZero
      (TStructure.t.isZero K (a - 1) a (by lia))
    exact ⟨boundedConstructible_of_isZero Λ hK,
      (isGE_iff _ _).2 fun i _ ↦ (homologyFunctor _ i).map_isZero hK,
      (isLE_iff _ _).2 fun i _ ↦ (homologyFunctor _ i).map_isZero hK⟩
  | succ m ih =>
    intro a K _ _ hK
    set b : ℤ := a + m
    let T' := (TStructure.t.triangleLTGE b).obj K
    have hT : T' ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K
    -- the third term is `Hᵇ K` placed in degree `b`
    have : T'.obj₃.IsLE b := by
      have : K.IsLE b := TStructure.t.isLE_of_le K (a + ↑(m + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b)
    have : T'.obj₃.IsGE b :=
      inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE b).obj K) b)
    obtain ⟨G, ⟨eG⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T'.obj₃ b
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl (isZero_of_isLE _ (b - 1) _ (by lia))
      (isZero_of_isLE _ (b - 1) _ (by lia))
    have hG : IsConstructibleSheaf G := by
      have : IsConstructibleSheaf ((homologyFunctor _ b).obj T'.obj₂) := hK b
      exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ b).map T'.mor₂) ≪≫
        (homologyFunctor _ b).mapIso eG ≪≫ (singleFunctorCompHomologyFunctorIso _ b).app G)
    obtain ⟨hGbc, hG₁, hG₂⟩ :=
      boundedConstructible_rightDerivedLowerStar_singleFunctor_of_openComplementBound Λ hj G
    let e₃ : (R((j)_*[ModuleCat.{u + 1} Λ])).obj T'.obj₃ ≅
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj (((singleFunctors _).functor 0).obj G))⟦-b⟧ :=
      (R((j)_*[ModuleCat.{u + 1} Λ])).mapIso
        (eG ≪≫ (((singleFunctors _).shiftIso (-b) b 0 (by lia)).app G).symm) ≪≫
          ((R((j)_*[ModuleCat.{u + 1} Λ])).commShiftIso (-b)).app _
    have : TStructure.t.IsGE ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        (((singleFunctors _).functor 0).obj G)⟦-b⟧) b :=
      TStructure.t.isGE_shift _ 0 (-b) b (by lia)
    have : TStructure.t.IsLE ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        (((singleFunctors _).functor 0).obj G)⟦-b⟧) (b + e) :=
      TStructure.t.isLE_shift _ e (-b) (b + e) (by lia)
    have h₃ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T
          ((R((j)_*[ModuleCat.{u + 1} Λ])).obj T'.obj₃) ∧
        TStructure.t.IsGE ((R((j)_*[ModuleCat.{u + 1} Λ])).obj T'.obj₃) b ∧
        TStructure.t.IsLE ((R((j)_*[ModuleCat.{u + 1} Λ])).obj T'.obj₃) (b + e) :=
      ⟨(Etale.DerivedCategory.boundedConstructible _ T).prop_of_iso e₃.symm
          ((Etale.DerivedCategory.boundedConstructible _ T).le_shift _ _ hGbc),
        TStructure.t.isGE_of_iso e₃.symm b, TStructure.t.isLE_of_iso e₃.symm (b + e)⟩
    -- the first term is handled by induction
    have h₁ := ih a T'.obj₁
      (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a))
      (TStructure.t.isLE_truncLT_obj _ _ _ (by lia)) fun q ↦ by
        by_cases hq : q < b
        · have : IsIso ((homologyFunctor _ q).map T'.mor₁) :=
            isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
              (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
          have : IsConstructibleSheaf ((homologyFunctor _ q).obj T'.obj₂) := hK q
          exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ q).map T'.mor₁)).symm
        · have : T'.obj₁.IsLE (b - 1) := TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
          exact IsConstructibleSheaf.of_isZero (isZero_of_isLE _ (b - 1) _ (by lia))
    obtain ⟨h₁bc, h₁₁, h₁₂⟩ := h₁
    obtain ⟨h₃bc, h₃₁, h₃₂⟩ := h₃
    have hRT := (R((j)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hT
    refine ⟨(Etale.DerivedCategory.boundedConstructible _ T).ext_of_isTriangulatedClosed₂ _ hRT
      h₁bc h₃bc, TStructure.t.isGE₂ _ hRT a h₁₁
        (TStructure.t.isGE_of_ge ((R((j)_*[ModuleCat.{u + 1} Λ])).obj T'.obj₃) a b (by lia)), ?_⟩
    have : TStructure.t.IsLE ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K) (b + e) :=
      TStructure.t.isLE₂ _ hRT (b + e)
        (TStructure.t.isLE_of_le ((R((j)_*[ModuleCat.{u + 1} Λ])).obj T'.obj₁) (a + m - 1 + e) _
          (by lia)) h₃₂
    exact TStructure.t.isLE_of_le _ (b + e) _ (by lia)

/-- Under the open-complement condition with constant `e` for `j : V ⟶ T`, the direct image
`Rj_*` sends `D_c^[a, b](V)` into `D_c^[a, b + e](T)`. -/
theorem boundedConstructible_rightDerivedLowerStar_of_openComplementBound
    {V T : Scheme.{u}} {j : V ⟶ T} {e : ℕ} (hj : OpenComplementBound Λ j e) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) V K)
    (hab : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) T ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K) ∧
      _root_.DerivedCategory.homologyConcentratedIn a (b + e)
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨hga, hlb⟩ := hab
  by_cases h : a ≤ b
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, a + m - 1 = b := ⟨(b - a + 1).toNat, by lia⟩
    have hle : _root_.DerivedCategory.TStructure.t.IsLE K (a + m - 1) := by rwa [hm]
    obtain ⟨hbc, hge, hle'⟩ := boundedConstructible_rightDerivedLowerStar_of_openComplementBound_aux
      Λ hj m a K hga hle hK.2
    rw [hm] at hle'
    exact ⟨hbc, hge, hle'⟩
  · have hK0 := (R((j)_*[ModuleCat.{u + 1} Λ])).map_isZero
      (_root_.DerivedCategory.TStructure.t.isZero K b a (by lia))
    exact ⟨boundedConstructible_of_isZero Λ hK0,
      (_root_.DerivedCategory.isGE_iff _ _).2 fun i _ ↦
        (_root_.DerivedCategory.homologyFunctor _ i).map_isZero hK0,
      (_root_.DerivedCategory.isLE_iff _ _).2 fun i _ ↦
        (_root_.DerivedCategory.homologyFunctor _ i).map_isZero hK0⟩

end DirectImage

/-! ### Closed immersions under the open-complement condition -/

section ClosedImmersion

/-- Let `i : Z ⟶ T` be a closed immersion whose open complement `j : U ⟶ T` satisfies the
open-complement condition with constant `e`. Then `Ri^!` sends `D_c^[a, b](T)` into
`D_c^[a, b + e + 1](Z)`: the localization triangle `Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` bounds
`Ri_! Ri^! K`, `Rj_* j^* K` lying in `D_c^[a, b + e]`. -/
theorem boundedConstructible_rightDerivedUpperShriek_of_isClosedImmersion_of_openComplementBound
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    (j : U ⟶ T) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ) {e : ℕ}
    (hj : OpenComplementBound Λ j e) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) T K)
    (hab : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) Z ((R(i)^![Λ]).obj K) ∧
      _root_.DerivedCategory.homologyConcentratedIn a (b + e + 1)
        ((R(i)^![Λ]).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  have hT := supportedLocalizationTriangle_mem_distTriang Λ i j hij K
  obtain ⟨hMbc, hMc⟩ := boundedConstructible_rightDerivedLowerStar_of_openComplementBound Λ hj
    (boundedConstructible_leftDerivedUpperStar _ j hK)
    (homologyConcentratedIn_of_iso _ ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app K).symm
      (((j)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hab))
  have hNbc : boundedConstructible (ModuleCat.{u + 1} Λ) T
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj K)) :=
    (boundedConstructible _ T).ext_of_isTriangulatedClosed₂ _ (inv_rot_of_distTriang _ hT)
      ((boundedConstructible _ T).le_shift (-1) _ hMbc) hK
  have hNc := homologyConcentratedIn_obj₁ _ _ hT (by lia : b ≤ b + e) hab hMc
  let ε := mapDerivedCategoryUpperStarRightDerivedLowerShriekIso (ModuleCat.{u + 1} Λ) i
  exact ⟨(boundedConstructible _ Z).prop_of_iso (ε.app _) (hNbc.mapDerivedCategory_upperStar i),
    homologyConcentratedIn_of_iso _ (ε.app _)
      (((i)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hNc)⟩

/-- Let `i : Z ⟶ T` be a closed immersion whose open complement `j : U ⟶ T` satisfies the
open-complement condition with constant `e`, and suppose that `Rj_*` moves the Tor amplitude of
complexes in `D_c^[a, b]` by at most `e`. Then `Ri^!` sends `D_c^[a, b](T)` with Tor amplitude in
`[a, b]` into `D_c^[a, b + e + 1](Z)` with Tor amplitude in `[a, b + e + 1]`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion_of_bound
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    (j : U ⟶ T) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ) {e : ℕ}
    (hj : OpenComplementBound Λ j e)
    (hjt : ∀ (a b : ℤ) (M : _root_.DerivedCategory (Sheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} Λ))), constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U a b M →
      torAmplitudeIn (ModuleCat.{u + 1} Λ) T a (b + e) ((R((j)_*[ModuleCat.{u + 1} Λ])).obj M))
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + e + 1)
      ((R(i)^![Λ]).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  obtain ⟨⟨hbc, hc⟩, ht⟩ := hK
  have hbc' := boundedConstructible_leftDerivedUpperStar _ j hbc
  have hc' : _root_.DerivedCategory.homologyConcentratedIn a b
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K) :=
    homologyConcentratedIn_of_iso _ ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app K).symm
      (((j)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hc)
  have ht' := torAmplitudeIn_leftDerivedUpperStar _ j a b ht
  obtain ⟨hMbc, hMc⟩ := boundedConstructible_rightDerivedLowerStar_of_openComplementBound Λ hj
    hbc' hc'
  exact constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion_of_lowerStar
    Λ i j hij (by lia : b ≤ b + e) ⟨⟨hbc, hc⟩, ht⟩
    ⟨⟨hMbc, hMc⟩, hjt a b _ ⟨⟨hbc', hc'⟩, ht'⟩⟩ (fun L ↦ hasProjectionFormula_of_finite Λ i _ L)

end ClosedImmersion
/-! ### The chartwise assembly -/

section Charts

variable {k : Type u} [Field k]

/-- **The chart step.** Let `v : V ⟶ Y` be an affine open of a finite-type `k`-scheme `Y`, and
`c : U ⟶ 𝔸ⁿ_V` a closed immersion whose open complement `W` satisfies the open-complement
condition with constant `e`. Then `R(c ≫ π ≫ v)^! ≅ Rc^! ∘ Rπ^! ∘ Rv^!` sends `D_c^[a, b](Y)` into
`D_c^[a - 2n, b - 2n + e + 1](U)`: the open immersion `v` preserves the interval, the smooth
projection `π` shifts it by `-2n`, and the closed immersion `c` widens it by `e + 1`. The same
holds with Tor amplitudes, as soon as the direct image along `W ⟶ 𝔸ⁿ_V` moves the Tor amplitude
by at most `e`. -/
theorem preservation_rightDerivedUpperShriek_chart {U V Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (v : V ⟶ Y) [IsOpenImmersion v] [IsAffine V] {n : ℕ}
    (c : U ⟶ 𝔸(ULift.{u} (Fin n); V)) [IsClosedImmersion c]
    [HasCompactification (c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)] {e : ℕ}
    (he : OpenComplementBound Λ (openComplementOfIsClosedImmersion c).ι e) :
    (∀ (a b : ℤ) (L : DerivedCategoryModule Λ Y),
      boundedConstructible (ModuleCat.{u + 1} Λ) Y L →
        _root_.DerivedCategory.homologyConcentratedIn a b L →
          boundedConstructible (ModuleCat.{u + 1} Λ) U
              ((R(c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)^![Λ]).obj L) ∧
            _root_.DerivedCategory.homologyConcentratedIn (a - 2 * n) (b - 2 * n + e + 1)
              ((R(c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)^![Λ]).obj L)) ∧
    ((∀ (a b : ℤ) (M : DerivedCategoryModule Λ (openComplementOfIsClosedImmersion c)),
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) _ a b M →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin n); V) a (b + e)
            ((R(((openComplementOfIsClosedImmersion c).ι)_*[ModuleCat.{u + 1} Λ])).obj M)) →
      ∀ (a b : ℤ) (K : DerivedCategoryModule Λ Y),
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
          constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U (a - 2 * n) (b - 2 * n + e + 1)
            ((R(c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)^![Λ]).obj K)) := by
  have : IsNoetherianRing Λ := inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  let π := 𝔸(ULift.{u} (Fin n); V) ↘ V
  let W := openComplementOfIsClosedImmersion c
  have : TopologicalSpace.NoetherianSpace V := v.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact v := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  have : IsNoetherian V := {}
  have : IsNoetherianRing Γ(V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V⟩
  have : IsLocallyNoetherian 𝔸(ULift.{u} (Fin n); V) := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian 𝔸(ULift.{u} (Fin n); V) := {}
  have : HasCompactification v := (Compactification.ofIsOpenImmersion v).hasCompactification
  have : HasInvertibleExponent Λ V := HasInvertibleExponent.of_hom v
  have : SmoothOfRelativeDimension n π := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) V
  have hij : Set.range c.base = (Set.range W.ι.base)ᶜ := by
    simp [W, openComplementOfIsClosedImmersion]
  -- `R(c ≫ π ≫ v)^! ≅ Rv^! ⋙ Rπ^! ⋙ Rc^!`
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ c (π ≫ v)
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ π v
  let E := e₁ ≪≫ Functor.isoWhiskerRight e₂ _
  refine ⟨fun a b L hL hab ↦ ?_, fun hjt a b K hK ↦ ?_⟩
  · obtain ⟨h₁, h₁'⟩ :=
      (preservation_rightDerivedUpperShriek_of_isOpenImmersion Λ v ⊥).1 a b L hL hab
    obtain ⟨h₂, h₂'⟩ :=
      (preservation_rightDerivedUpperShriek_of_smoothOfRelativeDimension Λ π n).1 a b _ h₁ h₁'
    obtain ⟨h₃, h₃'⟩ :=
      boundedConstructible_rightDerivedUpperShriek_of_isClosedImmersion_of_openComplementBound
        Λ c W.ι hij he h₂ h₂'
    exact ⟨(boundedConstructible _ U).prop_of_iso (E.app L).symm h₃,
      homologyConcentratedIn_of_iso _ (E.app L).symm h₃'⟩
  · have h₁ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion Λ v a b hK
    have h₂ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
      Λ π n a b h₁
    have h₃ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion_of_bound
      Λ c W.ι hij he hjt h₂
    exact constructibleTorAmplitudeIn_of_iso _ (E.app K).symm h₃

/-- **The chartwise assembly.** Let `f : X ⟶ Y` be a separated finite-type morphism, with `Y` of
finite type over `k`, and `Λ` finite with exponent invertible on `Y`. Let `U i ⊆ f⁻¹(V i)` be
finitely many affine charts covering `X`, over affine opens `V i ⊆ Y`, presented as closed
subschemes `c i : U i ⟶ 𝔸^{n i}_{V i}` whose open complements satisfy the open-complement
condition with constants `e i`. If `n i ≤ D` and `e i + 1 + 2 (D - n i) ≤ C` for all `i`, then
`Rf^!` sends `D_c^[a, b](Y)` into `D_c^[a - 2D, b - 2D + C](X)`; and with Tor amplitudes as soon
as the direct images along the open complements move the Tor amplitude by at most `e i`.

Both conditions are local on `X`, and on the chart `U i` the restriction of `Rf^!` is
`R(c i ≫ π ≫ v)^!` (`AlgebraicGeometry.Etale.preservation_rightDerivedUpperShriek_chart`). -/
theorem preservation_rightDerivedUpperShriek_of_charts {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    {ι : Type*} [Finite ι] (V : ι → Y.affineOpens) (U : ι → X.affineOpens)
    (hU : ∀ x, ∃ i, x ∈ (U i : X.Opens)) (n : ι → ℕ)
    (c : ∀ i, ((U i : X.Opens) : Scheme.{u}) ⟶ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)))
    [∀ i, IsClosedImmersion (c i)]
    (hc : ∀ i, c i ≫ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)) ↘ _ ≫ (V i : Y.Opens).ι =
      (U i : X.Opens).ι ≫ f)
    (e : ι → ℕ)
    (he : ∀ i, OpenComplementBound Λ (openComplementOfIsClosedImmersion (c i)).ι (e i))
    (D C : ℕ) (hD : ∀ i, n i ≤ D) (hC : ∀ i, e i + 1 + 2 * (D - n i) ≤ C) :
    (∀ (a b : ℤ) (L : DerivedCategoryModule Λ Y),
      boundedConstructible (ModuleCat.{u + 1} Λ) Y L →
        _root_.DerivedCategory.homologyConcentratedIn a b L →
          boundedConstructible (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj L) ∧
            _root_.DerivedCategory.homologyConcentratedIn (a - 2 * D) (b - 2 * D + C)
              ((R(f)^![Λ]).obj L)) ∧
    ((∀ i (a b : ℤ) (M : DerivedCategoryModule Λ (openComplementOfIsClosedImmersion (c i))),
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) _ a b M →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)) a
            (b + e i)
            ((R(((openComplementOfIsClosedImmersion (c i)).ι)_*[ModuleCat.{u + 1} Λ])).obj M)) →
      ∀ (a b : ℤ) (K : DerivedCategoryModule Λ Y),
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
          constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b - 2 * D + C)
            ((R(f)^![Λ]).obj K)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  -- the restriction of `Rf^!` to a chart
  have hres (i : ι) : Nonempty (R(f)^![Λ] ⋙
      D(((U i : X.Opens).ι)^*[ModuleCat.{u + 1} Λ]) ≅
        R(c i ≫ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)) ↘ _ ≫
          (V i : Y.Opens).ι)^![Λ]) := by
    have : TopologicalSpace.NoetherianSpace (U i : X.Opens) :=
      (U i : X.Opens).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (U i : X.Opens).ι :=
      ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    have : HasCompactification (U i : X.Opens).ι :=
      (Compactification.ofIsOpenImmersion _).hasCompactification
    obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ (U i : X.Opens).ι f
    obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq Λ (hc i)
    exact ⟨Functor.isoWhiskerLeft _
      (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ (U i : X.Opens).ι).symm ≪≫ e₁.symm ≪≫
        e₂.symm⟩
  have : ∀ i, IsAffine ((V i : Y.Opens) : Scheme.{u}) := fun i ↦ (V i).2
  have hchart (i : ι) := preservation_rightDerivedUpperShriek_chart Λ aY (V i : Y.Opens).ι
    (c i) (he i)
  obtain ⟨m, ⟨σ⟩⟩ := Finite.exists_equiv_fin ι
  let Uc : Fin m → X.Opens := fun k ↦ (U (σ.symm k)).1
  have hUc (x : X) : ∃ k, x ∈ Uc k := by
    obtain ⟨i, hi⟩ := hU x
    exact ⟨σ i, by simpa [Uc] using hi⟩
  refine ⟨fun a b L hL hab ↦ ?_, fun hjt a b K hK ↦ ?_⟩
  · have h (k : Fin m) := ((hchart (σ.symm k)).1 a b L hL hab)
    refine ⟨boundedConstructible_of_openCover Λ Uc hUc _ fun k ↦ ?_,
      homologyConcentratedIn_of_openCover _ Uc hUc _ fun k ↦ ?_⟩
    · exact (boundedConstructible _ _).prop_of_iso ((hres (σ.symm k)).some.app L).symm (h k).1
    · have := hD (σ.symm k)
      have := hC (σ.symm k)
      exact (homologyConcentratedIn_of_iso _ ((hres (σ.symm k)).some.app L).symm
        (h k).2).mono (by omega) (by omega)
  · refine constructibleTorAmplitudeIn_of_openCover Λ Uc hUc _ fun k ↦ ?_
    obtain ⟨⟨hbc, hconc⟩, hta⟩ := constructibleTorAmplitudeIn_of_iso _
      ((hres (σ.symm k)).some.app K).symm ((hchart (σ.symm k)).2 (hjt (σ.symm k)) a b K hK)
    have := hD (σ.symm k)
    have := hC (σ.symm k)
    have h₁ : a - 2 * (D : ℤ) ≤ a - 2 * (n (σ.symm k) : ℤ) := by omega
    have h₂ : b - 2 * (n (σ.symm k) : ℤ) + (e (σ.symm k) : ℤ) + 1 ≤ b - 2 * (D : ℤ) + C := by
      omega
    exact ⟨⟨hbc, hconc.mono h₁ h₂⟩, hta.mono h₁ h₂⟩

end Charts

end Etale

end AlgebraicGeometry
