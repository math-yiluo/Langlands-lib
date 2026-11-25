/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
public import WeilConjectures.SixFunctors.Etale.DivisorComplementDirectImageStalk
public import WeilConjectures.SixFunctors.Etale.StrictLocalizationStalkConstantZMod
public import WeilConjectures.TraceFormula.TransverseBoundary.LocalPurity.DirectImage

/-!
# Local purity for a regular divisor of an étale limit of smooth surfaces

Let `Z` be an étale limit with affine transition maps of smooth surfaces over an algebraically
closed field `k` (`AlgebraicGeometry.Scheme.IsEtaleLimitOfSmoothSurfaces`), `i : D ⟶ Z` a regular
divisor with `D` regular, `j : U ⟶ Z` its open complement, `ℓ` a prime invertible in `k`, and
`ybar` a geometric point of `Z` lying on `D`. Let `S = Z_(ybar)` be the strict localization and
`P = U ×_Z S = S - D_S`. Then

`H^q(P, ℤ/ℓ) = 0` for `q ≥ 2`, and `H⁰(P, ℤ/ℓ) ≅ H¹(P, ℤ/ℓ) ≅ ℤ/ℓ`

(blueprint `lemma-punctured-surface-punctured-curve--1`, *the surface*).

*Proof.* By the stalk formula (Stacks 03Q9,
`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafH_constantZMod_sheafFiber`),
`H^q(P, ℤ/ℓ)` is the stalk at `ybar` of `R^q j_* ℤ/ℓ`. Near the image of `ybar`, purity on a
smooth chart computes these direct images: `ℤ/ℓ` in degree `0`, `i'_* ℤ/ℓ` (that is,
`i_* ℤ/ℓ(-1)`) in degree `1`, and `0` above
(`Scheme.exists_hasDivisorComplementDirectImages_of_isEtaleLimitOfSmoothSurfaces`).
Their stalks at a geometric point of `D` are `ℤ/ℓ`, `ℤ/ℓ` and `0`.

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_sheafH_pullback_strictLocalizationToBase`
- `AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_pullback_strictLocalizationToBase`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.Etale

variable {k : Type u} [Field k] [IsAlgClosed k] {Z D U : Scheme.{u}} (aZ : Z ⟶ Spec (.of k))
  (hZ : IsEtaleLimitOfSmoothSurfaces aZ) [IsLocallyNoetherian Z] [IsRegular Z] (iD : D ⟶ Z)
  [IsRegularImmersion 1 iD] [IsRegular D] (j : U ⟶ Z) [IsOpenImmersion j]
  (hj : Set.range j = (Set.range iD)ᶜ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (ybar : Spec (.of Ω) ⟶ Z)
  (hy : Set.range ybar ⊆ Set.range iD)

include hZ hj hℓ hy in
/-- Blueprint `lemma-punctured-surface-punctured-curve--1`: for a geometric point `ybar` on a
regular divisor `D` of an étale limit of smooth surfaces, the cohomology `H^q(S - D_S, ℤ/ℓ)` of the
punctured strict localization is the stalk at `ybar` of `R^q j_* ℤ/ℓ`, and there is an open
neighbourhood of the image of `ybar` over which `j` has the higher direct images of the
complement of a divisor through which `ybar` factors. -/
theorem exists_hasDivisorComplementDirectImages_addEquiv_sheafH :
    ∃ (O : Z.Opens) (D' : Scheme.{u}) (i' : D' ⟶ O) (_ : IsClosedImmersion i')
      (s : Spec (.of Ω) ⟶ D'),
      HasDivisorComplementDirectImages ℓ (pullback.snd j O.ι) i' ∧
      ∀ q : ℕ, Nonempty (Sheaf.H ((pullback j (strictLocalizationToBase ybar)).constantZMod ℓ) q ≃+
        ((pointSmallEtale (s ≫ i')).sheafFiber (A := ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))).obj
          (higherDirectImage (ZModCoeff.{u} ℓ) (pullback.snd j O.ι) q
            (constantZModModule (pullback j O.ι) ℓ))) := by
  have hpt (p : Spec (.of Ω)) : p = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  obtain ⟨O, hyO, hO⟩ := exists_hasDivisorComplementDirectImages_of_isEtaleLimitOfSmoothSurfaces
    aZ hZ iD j hj ℓ hℓ _ (hy ⟨IsLocalRing.closedPoint Ω, rfl⟩)
  have hj' : Set.range (pullback.snd j O.ι ≫ O.ι) = Set.range O.ι ∩ Set.range j := by
    rw [Pullback.range_snd_comp, Set.inter_comm]
  obtain ⟨D', i', _, hi', hdi⟩ := hO O O.ι (by rw [Opens.range_ι]) _ _ hj'
  have hyO' : Set.range ybar ⊆ Set.range O.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Opens.range_ι, hpt p]
    exact hyO
  let ybar' : Spec (.of Ω) ⟶ O := IsOpenImmersion.lift O.ι ybar hyO'
  have hybar' : ybar' ≫ O.ι = ybar := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨s, hs⟩ : ∃ s : Spec (.of Ω) ⟶ D', s ≫ i' = ybar' := by
    refine exists_comp_eq_of_mem_range i' ybar' ?_
    have : O.ι (ybar' (IsLocalRing.closedPoint Ω)) ∈ Set.range (i' ≫ O.ι) := by
      rw [hi', ← Scheme.Hom.comp_apply, hybar']
      exact ⟨hyO' ⟨_, rfl⟩, hy ⟨_, rfl⟩⟩
    obtain ⟨d, hd⟩ := this
    exact ⟨d, O.ι.isOpenEmbedding.injective hd⟩
  refine ⟨O, D', i', inferInstance, s, hdi, fun q ↦ ?_⟩
  obtain ⟨e₁⟩ := nonempty_addEquiv_sheafH_constantZMod_sheafFiber j ybar ℓ q
  obtain ⟨e₂⟩ := nonempty_iso_upperStar_higherDirectImage_constantZModModule
    (IsPullback.of_hasPullback j O.ι) ℓ q
    (isIso_baseChangeHomologyMap_of_etale _ (IsPullback.of_hasPullback j O.ι) q _)
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hyb : (s ≫ i') ≫ O.ι = ybar := by rw [hs, hybar']
  obtain ⟨e₃⟩ : Nonempty (((pointSmallEtale ybar).sheafFiber
      (A := ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))).obj
        (higherDirectImage (ZModCoeff.{u} ℓ) j q (constantZModModule U ℓ)) ≃+
      ((pointSmallEtale (s ≫ i')).sheafFiber (A := ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))).obj
        (higherDirectImage (ZModCoeff.{u} ℓ) (pullback.snd j O.ι) q
          (constantZModModule (pullback j O.ι) ℓ))) := by
    rw [← hyb]
    exact ⟨((((upperStarCompSheafFiberIso (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) O.ι
      (s ≫ i')).app _).symm ≪≫
        (pointSmallEtale (s ≫ i')).sheafFiber.mapIso e₂).toLinearEquiv.toAddEquiv)⟩
  exact ⟨e₁.trans e₃⟩

include hZ hj hℓ hy in
/-- Blueprint `lemma-punctured-surface-punctured-curve--1`: for a geometric point `ybar` on a
regular divisor `D` of an étale limit of smooth surfaces, `H^q(S - D_S, ℤ/ℓ) = 0` for `q ≥ 2`, where
`S = Z_(ybar)`. -/
theorem subsingleton_sheafH_pullback_strictLocalizationToBase (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H ((pullback j (strictLocalizationToBase ybar)).constantZMod ℓ) q) := by
  obtain ⟨O, D', i', _, s, hdi, he⟩ :=
    exists_hasDivisorComplementDirectImages_addEquiv_sheafH aZ hZ iD j hj hℓ ybar hy
  obtain ⟨e⟩ := he q
  have := hdi.subsingleton_sheafFiber (s ≫ i') q hq
  exact e.injective.subsingleton

include hZ hj hℓ hy in
/-- Blueprint `lemma-punctured-surface-punctured-curve--1`: for a geometric point `ybar` on a
regular divisor `D` of an étale limit of smooth surfaces, `H⁰(S - D_S, ℤ/ℓ)` and
`H¹(S - D_S, ℤ/ℓ) ≅ 𝔽_ℓ(-1)` are free of rank one over `𝔽_ℓ`, where `S = Z_(ybar)`. -/
theorem nonempty_addEquiv_sheafH_pullback_strictLocalizationToBase (q : ℕ) (hq : q ≤ 1) :
    Nonempty (Sheaf.H ((pullback j (strictLocalizationToBase ybar)).constantZMod ℓ) q ≃+
      ZMod ℓ) := by
  obtain ⟨O, D', i', _, s, hdi, he⟩ :=
    exists_hasDivisorComplementDirectImages_addEquiv_sheafH aZ hZ iD j hj hℓ ybar hy
  obtain ⟨e⟩ := he q
  interval_cases q
  · obtain ⟨e'⟩ := hdi.nonempty_addEquiv_sheafFiber_zero (s ≫ i')
    exact ⟨e.trans e'⟩
  · obtain ⟨e'⟩ := hdi.nonempty_addEquiv_sheafFiber_one s
    exact ⟨e.trans e'⟩

end AlgebraicGeometry.Scheme
