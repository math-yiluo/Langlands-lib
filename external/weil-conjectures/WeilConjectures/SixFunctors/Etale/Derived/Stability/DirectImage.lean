/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProperNoetherian
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SepClosedPoint
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImageTorAmplitudeNoetherian
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionObjectConstantProjection
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionAbelianDirectImageVanishing
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorStalk
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Stability of `Dctf`: direct image and internal hom

For torsion coefficients `Λ` with invertible exponent and schemes of finite type over a field,
this file proves that the direct image `Rf_*`, the compactly supported direct image `Rf_!`
preserve the bounded constructible complexes, with the shifts of the Tor amplitude recorded by
the blueprint, and the local tools for the internal hom; the stability of `Dctf` under the
internal hom is in `WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom`.

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-! ### Torsion coefficients with invertible exponent

The statements of this section are the ones of `sk-thm-sf-direct-image-tor-amplitude`,
`sk-thm-sf-hom-ctf`, `theorem-f-shriek-finite-coefficients` (ii)–(iv) and
`proposition-six-operations-dctf` (iii), (v), (vi) whose content is a bound on étale cohomological
dimension, a constructibility theorem for direct images or purity. They are made in the setting
of `definition-constructible-sheaves--6`: the coefficients are a finite ring `Λ` whose exponent is
invertible on the schemes in sight, and the schemes are of finite type over a field `k`. Neither
hypothesis can be dropped: for `Λ = 𝔽_p` on `𝔸¹` over `𝔽̄_p`, `H¹(𝔸¹, 𝔽_p)` is infinite
(Artin–Schreier), so `Rf_*` of the constant sheaf along `𝔸¹ ⟶ Spec 𝔽̄_p` is not constructible; and
over a general Noetherian base étale cohomology need not vanish above twice the dimension. -/

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-! #### Direct image -/

omit [Finite Λ] in
/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility.

Let `f : X ⟶ Y` be a morphism of finite-type `k`-schemes, let `Λ` be a noetherian ring and `J` an
ideal of `Λ` with `Λ ⧸ J` finite, and let `K` be a bounded constructible complex of étale sheaves
of `Λ`-modules on `X` killed by `J`, where `J` contains an integer `N` invertible on `Y`. Then
`Rf_* K` is bounded constructible on `Y_ét`. For a finite `Λ` one may take `J = 0`; the case of an
infinite `Λ` is used at the integral stage `Λ = 𝒪_E`, for the reductions modulo `Iⁿ⁺¹`. This is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_smul_eq_zero`.

Each hypothesis is needed. Without torsion the statement fails, `H³(ℙ¹, ℤ)` containing
`ℚ_ℓ/ℤ_ℓ`; and for `N = p` on `𝔸¹` over `𝔽̄_p`, `H¹(𝔸¹, 𝔽_p)` is infinite (Artin–Schreier). -/
theorem boundedConstructible_rightDerivedLowerStar [IsNoetherianRing Λ] (J : Ideal Λ)
    [Finite (Λ ⧸ J)] {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (N : ℕ)
    [NeZero N] (hNJ : (N : Λ) ∈ J) (hNY : IsUnit (N : Γ(Y, ⊤))) (hJ : ∀ r ∈ J, r • 𝟙 K = 0)
    (hbc : boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) Y ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  have : QuasiCompact f := by
    subst hf
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    have : IsNoetherian Y := {}
    exact QuasiCompact.of_comp f aY
  have : HasInvertibleExponent (Λ ⧸ J) X :=
    ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), by
      rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
      exact hNJ, by simpa using hNY.map f.appTop.hom⟩
  exact boundedConstructible_rightDerivedLowerStar_of_smul_eq_zero J f aX aY hf hbc hJ

/-- Blueprint `sk-thm-sf-direct-image-tor-amplitude`: Direct image with finite Tor amplitude.

Let `f : X ⟶ Y` be a morphism of finite-type `k`-schemes with `dim X ≤ d`, let `Λ` be a finite
ring and let `K` be a complex of étale sheaves of `Λ`-modules on `X` of Tor amplitude in
`[a, b]`. Then `Rf_* K` has Tor amplitude in `[a, b + 2d]`. The shift `2d` is the uniform
vanishing of `Rᵖf_*` above twice the dimension of the source.

This is `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_finite`: by the
projection formula for finitely generated constant coefficients, `Rf_* K ⊗ᴸ κ_Y ≅ Rf_*(K ⊗ᴸ κ_X)`
for the residue ring `κ` of `Λ`, which has homology in `[a, b + 2d]`, and the residue test
concludes. The remaining hypotheses of the blueprint statement (`f` separated, `K` bounded
constructible and killed by an integer `N` invertible on `Y`) are kept for the callers but are
not needed. For coefficients which are not finite, see
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing`. -/
theorem torAmplitudeIn_rightDerivedLowerStar
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [IsSeparated f] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (N : ℕ)
    [NeZero N] (_hN : N • 𝟙 K = 0) (_hNY : IsUnit (N : Γ(Y, ⊤)))
    (_hbc : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  torAmplitudeIn_rightDerivedLowerStar_of_finite Λ aX aY f hf d hd a b hta

omit [Finite Λ] in
/-- The Tor amplitude bound of blueprint `sk-thm-sf-direct-image-tor-amplitude` for Noetherian
coefficients which need not be finite.

Let `f : X ⟶ Y` be a separated morphism of finite-type `k`-schemes with `dim X ≤ d`, let `Λ` be a
Noetherian ring, and let `K` be a bounded constructible complex of étale sheaves of `Λ`-modules
on `X` of Tor amplitude in `[a, b]`, killed by an integer `N` invertible on `Y`. Then `Rf_* K` has
Tor amplitude in `[a, b + 2d]`. This is used at the integral coefficient stage, for the reductions
of an `𝒪_E`-complex modulo powers of the maximal ideal. For a finite ring `Λ` it is
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`; in general the residue test is
not available and the proof goes through the geometric stalks, using that the stalks of `Rf_* K`
are computed by a projection formula with arbitrary constant coefficients. -/
theorem torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing [IsNoetherianRing Λ]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [IsSeparated f] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (N : ℕ)
    [NeZero N] (hN : N • 𝟙 K = 0) (hNY : IsUnit (N : Γ(Y, ⊤)))
    (hbc : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  -- neither the invertibility of `N` on `Y` nor the constructibility of `K` is needed
  have _ := hNY
  have _ := hbc
  exact torAmplitudeIn_rightDerivedLowerStar_of_nsmul_id_eq_zero Λ aX aY f hf d hd a b N hN hta

omit [Finite Λ] in
/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility.

For a finite `Λ` whose exponent is invertible on `Y` and a morphism `f : X ⟶ Y` of finite-type
`k`-schemes, `Rf_*` preserves bounded constructibility. This is the finite-coefficient case of
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`, and is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`
once `f` is known to be quasi-compact. -/
theorem boundedConstructible_rightDerivedLowerStar_of_finite [Finite Λ] {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasInvertibleExponent Λ Y]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hbc : boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) Y ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  have : QuasiCompact f := by
    subst hf
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    have : IsNoetherian Y := {}
    exact QuasiCompact.of_comp f aY
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom f
  exact boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent Λ f aX aY hf K hbc

/-- Blueprint `proposition-six-operations-dctf`: Stability of the constructible finite-Tor
subcategories.

Clause (iii): `Rf_* : Dctf(X, Λ) ⥤ Dctf(Y, Λ)` is defined for every separated morphism of
finite-type `k`-schemes, for a finite `Λ` whose exponent is invertible on `Y`. It is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_finite` together with
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`, a finite-type `k`-scheme being
finite dimensional. -/
theorem constructibleFiniteTor_rightDerivedLowerStar {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [IsSeparated f] [HasInvertibleExponent Λ Y]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨hbc, a, b, hta⟩ := hK
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  obtain ⟨N, hN0, hNΛ, hNY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Y)
  have : NeZero N := ⟨hN0.ne'⟩
  have hN := nsmul_id_eq_zero_of_natCast_eq_zero hNΛ K
  have : IsNoetherianRing Λ := inferInstance
  exact ⟨boundedConstructible_rightDerivedLowerStar_of_finite Λ aX aY f hf hbc, a, b + 2 * (d : ℤ),
    torAmplitudeIn_rightDerivedLowerStar _ aX aY f hf d hd a b N hN hNY hbc hta⟩

/-- **Proper direct image with finite coefficients**, finite-Tor form: for a
proper morphism `f : X ⟶ Y` of finite-type `k`-schemes and a finite `Λ` whose exponent is
invertible on `Y`, `Rf_*` carries `Dctf(X, Λ)` into `Dctf(Y, Λ)`. Bounded constructibility is
proper finiteness
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`,
SGA 4 XIV 1.1), not the finiteness theorem for arbitrary `f`; the Tor amplitude bound is
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`. This is the proper leg of
`Rf_! = Rp_* ∘ j_!` in the notes' proof of the results from étale theory. -/
theorem constructibleFiniteTor_rightDerivedLowerStar_of_isProper {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [IsProper f]
    [HasInvertibleExponent Λ Y]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨hbc, a, b, hta⟩ := hK
  cases isEmpty_or_nonempty X with
  | inl hX =>
    have h0 : IsZero ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) :=
      (R((f)_*[ModuleCat.{u + 1} Λ])).map_isZero (isZero_derivedCategory_of_isEmpty _ X K)
    exact ⟨boundedConstructible_of_isZero Λ h0, a, b,
      _root_.DerivedCategory.torAmplitudeIn_of_isZero a b h0⟩
  | inr hX =>
    have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom f
    have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
    obtain ⟨N, hN0, hNΛ, hNY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Y)
    have : NeZero N := ⟨hN0.ne'⟩
    have hN := nsmul_id_eq_zero_of_natCast_eq_zero hNΛ K
    have : IsNoetherianRing Λ := inferInstance
    exact ⟨boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian aY f hbc, a,
      b + 2 * (d : ℤ), torAmplitudeIn_rightDerivedLowerStar _ aX aY f hf d hd a b N hN hNY hbc hta⟩

/-- Blueprint `proposition-six-operations-dctf`: Stability of the constructible finite-Tor
subcategories.

Clause (iv): `Rf_! : Dctf(X, Λ) ⥤ Dctf(Y, Λ)` is defined for every separated finite-type `f`
admitting a compactification, over a finite-type `k`-scheme `Y`, for a finite `Λ` whose exponent
is invertible on `Y`. For the chosen compactification `X ⟶[j] Z ⟶[g] Y` of `f`, `Rf_!` is
`Rg_* ∘ j_!`; extension by zero preserves `Dctf`
(`AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek`)
and so does the direct image along the proper `g`, by proper finiteness
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar_of_isProper`).

Some finiteness hypothesis on `Y` is needed: for `f : ⊔ₙ ℙⁿ_ℂ ⟶ ⊔ₙ Spec ℂ`, which is proper,
`Rf_! Λ` has `H²ⁿ ≠ 0` on the `n`-th point, so it is not bounded. -/
theorem constructibleFiniteTor_rightDerivedLowerShriek {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) := by
  let c := HasCompactification.compactification f
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨hbc, a, b, hta⟩ := hK
  have h := constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek Λ c.i a b
    ⟨⟨hbc, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta⟩, hta⟩
  exact constructibleFiniteTor_rightDerivedLowerStar_of_isProper Λ (c.g ≫ aY) aY c.g rfl
    ⟨h.1.1, a, b, h.2⟩

/-! #### Internal hom: local tools -/

omit [Finite Λ] in
/-- Constructibility of a sheaf of modules is local for a finite open cover of a scheme whose
underlying space is noetherian. -/
theorem _root_.AlgebraicGeometry.Scheme.isConstructibleSheaf_of_openCover :
    ∀ (n : ℕ) {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (U : Fin n → X.Opens) (_ : ∀ x, ∃ i, x ∈ U i)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    (∀ i, IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U i).ι).obj F)) →
      IsConstructibleSheaf F := by
  intro n
  induction n with
  | zero =>
    intro X _ U hU F _
    have : IsEmpty X := ⟨fun x ↦ by obtain ⟨i, -⟩ := hU x; exact i.elim0⟩
    exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)
  | succ n ih =>
    intro X _ U hU F h
    have : TopologicalSpace.NoetherianSpace (U 0) :=
      (U 0).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (U 0).ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    rw [Scheme.isConstructibleSheaf_iff_upperStar (U 0).ι (U 0).closedComplement (by simp)]
    refine ⟨h 0, ?_⟩
    let i := (U 0).closedComplement
    have : TopologicalSpace.NoetherianSpace _ := i.isClosedEmbedding.isInducing.noetherianSpace
    refine ih (fun k ↦ i ⁻¹ᵁ U k.succ) (fun z ↦ ?_) _ (fun k ↦ ?_)
    · have hz : i.base z ∉ U 0 := by
        have : i.base z ∈ Set.range i.base := ⟨z, rfl⟩
        rwa [(U 0).range_closedComplement] at this
      obtain ⟨k, hk⟩ := hU (i.base z)
      obtain ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ k |>.resolve_left (by rintro rfl; exact hz hk)
      exact ⟨k, hk⟩
    · have := h k.succ
      have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U k.succ).ι ⋙
          Etale.upperStar (ModuleCat.{u + 1} Λ) (i ∣_ U k.succ)).obj F) :=
        IsConstructibleSheaf.upperStar (i ∣_ U k.succ)
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U k.succ).ι).obj F)
      exact IsConstructibleSheaf.of_iso
        (((Etale.upperStarComp _ (i ∣_ U k.succ) (U k.succ).ι).app F).symm ≪≫
          eqToIso (by rw [morphismRestrict_ι]) ≪≫
          (Etale.upperStarComp _ (i ⁻¹ᵁ U k.succ).ι i).app F)

open ZeroObject in
omit [Finite Λ] in
/-- A bounded complex whose restrictions to the members of a finite open cover of a noetherian
space are bounded constructible is bounded constructible. -/
theorem boundedConstructible_of_openCover {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : ∀ i, boundedConstructible (ModuleCat.{u + 1} Λ) (U i)
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R)) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X R := by
  -- homology commutes with the restrictions
  have e (i : Fin n) (q : ℤ) :=
    ((((U i).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app R
  refine ⟨?_, fun q ↦ ?_⟩
  · choose c d hcd using fun i ↦
      (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).2 (h i).1
    -- a zero sheaf is detected on the cover
    have hz (q : ℤ) (hq : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R))) :
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj R) := by
      have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
        (ι := ULift.{u} (Fin n)) (fun i ↦ (U i.down).ι)
        (fun x ↦ by obtain ⟨i, hi⟩ := hU x; exact ⟨⟨i⟩, ⟨x, hi⟩, rfl⟩)
        (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0) (fun i ↦
          isIso_of_source_target_iso_zero _ ((hq i.down).of_iso (e i.down q)).isoZero
            (Functor.map_isZero _ (isZero_zero _)).isoZero)
      exact (isZero_zero _).of_iso
        (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0))
    refine (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded R).1
      ⟨-∑ i, |c i|, ∑ i, |d i|, ?_, ?_⟩
    · refine (_root_.DerivedCategory.isGE_iff R _).2 fun q hq ↦ hz q fun i ↦
        (_root_.DerivedCategory.isGE_iff _ (c i)).1 (hcd i).1 q ?_
      have := Finset.single_le_sum (f := fun i ↦ |c i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      have := neg_abs_le (c i)
      omega
    · refine (_root_.DerivedCategory.isLE_iff R _).2 fun q hq ↦ hz q fun i ↦
        (_root_.DerivedCategory.isLE_iff _ (d i)).1 (hcd i).2 q ?_
      have := Finset.single_le_sum (f := fun i ↦ |d i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      have := le_abs_self (d i)
      omega
  · refine Scheme.isConstructibleSheaf_of_openCover Λ n U hU _ fun i ↦ ?_
    have : IsConstructibleSheaf ((D(((U i).ι)^*[ModuleCat.{u + 1} Λ]) ⋙
        _root_.DerivedCategory.homologyFunctor _ q).obj R) := (h i).2 q
    exact IsConstructibleSheaf.of_iso (e i q).symm

omit [Finite Λ] in
/-- A complex of finite Tor amplitude with bounded constructible homology restricts to one along
a pullback. -/
lemma constructibleFiniteTor_mapDerivedCategory_upperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (D((f)^*[ModuleCat.{u + 1} Λ]).obj N) := by
  obtain ⟨hbc, c, d, hcd⟩ := hN
  exact ⟨hbc.mapDerivedCategory_upperStar f, c, d,
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app N)
      (torAmplitudeIn_leftDerivedUpperStar _ f c d hcd)⟩

end Torsion

end Etale

end AlgebraicGeometry
