/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DivisorComplementDirectImageGerm
public import WeilConjectures.SixFunctors.Etale.EtaleAffineLimitBaseChange
public import WeilConjectures.TraceFormula.TransverseBoundary.Basic
public import WeilConjectures.TraceFormula.TransverseBoundary.LocalPurity.Chart

/-!
# Direct images from the complement of a regular divisor of an étale limit of surfaces

Let `Z` be an étale limit with affine transition maps of smooth surfaces over an algebraically
closed field `k` (`AlgebraicGeometry.Scheme.IsEtaleLimitOfSmoothSurfaces`), `i : D ⟶ Z` a regular
divisor with `D` regular and `j : U ⟶ Z` its open complement. For a prime `ℓ` invertible in `k`,
every point `y` of `D` has an open neighbourhood `O` in `Z` such that for every open `O'` of `Z`
inside `O` (given by an open immersion), with `j' : U ∩ O' ⟶ O'`,

`R⁰j'_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j'_* ℤ/ℓ ≅ i'_* ℤ/ℓ` and `R^q j'_* ℤ/ℓ = 0` for `q ≥ 2`,

for a closed immersion `i'` with the same support as `D ∩ O'` (blueprint
`lemma-punctured-surface-punctured-curve--1`, *the surface*).

*Local chart.* A local equation of `D` at `y` comes from a function `t` on an open `V` of some
stage `Zᵢ` of the limit, whose germ at the image of `y` lies in `𝔪 \ 𝔪²`
(`AlgebraicGeometry.Scheme.exists_isLimit_chart`). Purity on the smooth surface `Zᵢ` computes the
direct images from the complement of `V(t)` near the image of `y`
(`AlgebraicGeometry.Etale.exists_hasDivisorComplementDirectImages_of_germ`), on an open `X₀`. The
inverse image `O` of `X₀` in `Z` is the limit of the inverse images of `X₀` in the later stages,
which are étale over `X₀`, and the direct images commute with base change along `O ⟶ X₀`
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_of_etale`) and along the open
immersions `O' ⟶ O`.

## Main statements

- `Scheme.exists_hasDivisorComplementDirectImages_of_isEtaleLimitOfSmoothSurfaces`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.Etale

/-- **Direct images from the complement of a regular divisor** (blueprint
`lemma-punctured-surface-punctured-curve--1`, *the surface*). Let `Z` be an étale limit of smooth
surfaces over an algebraically closed field `k`, `i : D ⟶ Z` a regular divisor with `D` regular
and `j : U ⟶ Z` its open complement. Every point `y` of `D` has an open neighbourhood `O` such
that for every open immersion `f : O' ⟶ Z` with image in `O` and every open immersion
`j' : U' ⟶ O'` onto `f⁻¹(U)`, there is a closed immersion `i'` onto `f⁻¹(D)` with

`R⁰j'_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j'_* ℤ/ℓ ≅ i'_* ℤ/ℓ` and `R^q j'_* ℤ/ℓ = 0` for `q ≥ 2`. -/
theorem exists_hasDivisorComplementDirectImages_of_isEtaleLimitOfSmoothSurfaces {k : Type u}
    [Field k] [IsAlgClosed k] {Z D U : Scheme.{u}} (aZ : Z ⟶ Spec (.of k))
    (hZ : IsEtaleLimitOfSmoothSurfaces aZ) [IsLocallyNoetherian Z] (iD : D ⟶ Z)
    [IsRegular Z] [IsRegularImmersion 1 iD] [IsRegular D] (j : U ⟶ Z) [IsOpenImmersion j]
    (hj : Set.range j = (Set.range iD)ᶜ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (y : Z)
    (hy : y ∈ Set.range iD) :
    ∃ O : Z.Opens, y ∈ O ∧ ∀ (O' : Scheme.{u}) (f : O' ⟶ Z) [IsOpenImmersion f],
      Set.range f ⊆ O → ∀ (U' : Scheme.{u}) (j' : U' ⟶ O') [IsOpenImmersion j'],
        Set.range (j' ≫ f) = Set.range f ∩ Set.range j →
        ∃ (D' : Scheme.{u}) (i' : D' ⟶ O') (_ : IsClosedImmersion i'),
          Set.range (i' ≫ f) = Set.range f ∩ Set.range iD ∧
            HasDivisorComplementDirectImages ℓ j' i' := by
  obtain ⟨I, _, _, E, a, c, hc, e, -, -, hsm, het⟩ := hZ
  have : ∀ {i i' : I} (φ : i ⟶ i'), IsAffineHom (E.map φ) := fun φ ↦ (het φ).2
  let c' : Cone E := c.extend e.inv
  have hc' : IsLimit c' := hc.ofIsoLimit (Cone.extendIso c e)
  have : IsLocallyNoetherian c'.pt := inferInstanceAs (IsLocallyNoetherian Z)
  have : IsRegular c'.pt := inferInstanceAs (IsRegular Z)
  obtain ⟨i, V, t, hyV, hD, ht, ht2⟩ := exists_isLimit_chart E c' hc' iD y hy
  have : Smooth (a i) := (hsm i).smooth
  have : IsLocallyNoetherian (E.obj i) := LocallyOfFiniteType.isLocallyNoetherian (a i)
  obtain ⟨X₀, hX₀V, hyX₀, D₀, i₀, _, hi₀, hj₀⟩ :=
    exists_hasDivisorComplementDirectImages_of_germ (a i) V t _ hyV ht ht2 ℓ hℓ
  let π : Z ⟶ E.obj i := c'.π.app i
  refine ⟨π ⁻¹ᵁ X₀, hyX₀, fun O' f _ hf U' j' _ hj' ↦ ?_⟩
  -- the chart `p : O' ⟶ X₀`
  let γ : O' ⟶ π ⁻¹ᵁ X₀ :=
    IsOpenImmersion.lift (π ⁻¹ᵁ X₀).ι f (by rwa [Scheme.Opens.range_ι])
  have hγ : γ ≫ (π ⁻¹ᵁ X₀).ι = f := IsOpenImmersion.lift_fac _ _ _
  let p : O' ⟶ X₀ := γ ≫ (π ∣_ X₀)
  have hp (z : O') : X₀.ι (p z) = π (f z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hγ]
  -- `f⁻¹(D)` is the inverse image of the zero locus of `t`
  have hmem (z : O') : f z ∈ Set.range iD ↔ X₀.ι (p z) ∉ (E.obj i).basicOpen t := by
    rw [hp]
    exact hD (f z) (hX₀V ((hp z) ▸ (p z).2))
  let U₀ : X₀.toScheme.Opens := X₀.ι ⁻¹ᵁ (E.obj i).basicOpen t
  have hU₀ : Set.range (U₀.ι ≫ X₀.ι) = (X₀ : Set (E.obj i)) ∩ (E.obj i).basicOpen t := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨(U₀.ι v).2, v.2⟩
    · rintro ⟨hw, hwt⟩
      exact ⟨⟨⟨w, hw⟩, hwt⟩, rfl⟩
  have hdi := hj₀ U₀ U₀.ι hU₀
  -- the cartesian square of `j'` and `U₀ ⟶ X₀` along `p`
  have hrange : j'.opensRange = p ⁻¹ᵁ U₀.ι.opensRange := by
    ext z
    rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_preimage,
      Scheme.Opens.opensRange_ι]
    have hz : z ∈ Set.range j' ↔ f z ∈ Set.range j := by
      constructor
      · rintro ⟨w, rfl⟩
        have : f (j' w) ∈ Set.range (j' ≫ f) := ⟨w, rfl⟩
        rw [hj'] at this
        exact this.2
      · intro h
        have : f z ∈ Set.range (j' ≫ f) := by
          rw [hj']
          exact ⟨⟨z, rfl⟩, h⟩
        obtain ⟨w, hw⟩ := this
        exact ⟨w, f.isOpenEmbedding.injective hw⟩
    rw [← Set.mem_range, hz, hj, Set.mem_compl_iff, hmem, not_not]
    rfl
  let e' : U' ⟶ U₀ := IsOpenImmersion.lift U₀.ι (j' ≫ p) (by
    rintro _ ⟨w, rfl⟩
    have : j' w ∈ (j'.opensRange : Set O') := ⟨w, rfl⟩
    rw [hrange] at this
    simpa using this)
  have sq : IsPullback e' j' U₀.ι p :=
    IsOpenImmersion.isPullback e' j' U₀.ι p (IsOpenImmersion.lift_fac _ _ _).symm hrange.symm
  have sq₂ := IsPullback.of_hasPullback U₀.ι (π ∣_ X₀)
  have sq₁ := IsPullback.of_right' sq sq₂
  have : IsTorsionSheafOfInvertibleOrder X₀ (constantZModModule U₀ ℓ) :=
    IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero (ZModCoeff.{u} ℓ) ℓ (NeZero.ne ℓ)
      (by ext; simp) (AffineSpace.isUnit_natCast_of_ne_zero (X₀.ι ≫ a i) hℓ) _
  have H (q : ℕ) : IsIso (baseChangeHomologyMap (ZModCoeff.{u} ℓ) sq q
      (constantZModModule U₀ ℓ)) :=
    isIso_baseChangeHomologyMap_of_etale_restriction _ sq₂ sq₁ sq (sq₂.lift_fst _ _ _) rfl q _
      (isIso_baseChangeHomologyMap_of_isLimit_of_etale _ E (fun φ ↦ (het φ).1) c' hc' i X₀
        U₀.ι sq₂ q _)
  refine ⟨_, _, inferInstance, ?_, hdi.of_isPullback p sq H⟩
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨w, rfl⟩
    refine ⟨⟨pullback.snd i₀ p w, rfl⟩, ?_⟩
    have hw : p (pullback.snd i₀ p w) = i₀ (pullback.fst i₀ p w) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rw [Scheme.Hom.comp_apply, hmem, hw]
    have : (i₀ ≫ X₀.ι) (pullback.fst i₀ p w) ∈ Set.range (i₀ ≫ X₀.ι) := ⟨_, rfl⟩
    rw [hi₀] at this
    exact this.2
  · rintro ⟨⟨z, rfl⟩, hz⟩
    have hz' : X₀.ι (p z) ∈ Set.range (i₀ ≫ X₀.ι) := by
      rw [hi₀]
      exact ⟨(p z).2, (hmem z).1 hz⟩
    obtain ⟨d, hd⟩ := hz'
    have hd' : i₀ d = p z := X₀.ι.isOpenEmbedding.injective hd
    have : z ∈ Set.range (pullback.snd i₀ p) := by
      rw [Scheme.Pullback.range_snd]
      exact ⟨d, hd'⟩
    obtain ⟨w, rfl⟩ := this
    exact ⟨w, rfl⟩

end AlgebraicGeometry.Scheme
