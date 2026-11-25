/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.HomDevissage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability

/-!
# The preservation matrix of the six operations

For a finite coefficient ring `Λ` whose exponent is invertible on a field `k` and schemes of
finite type over `k`, this file collects which of the six operations preserve the bounded
constructible complexes `Dᵇc` and the constructible complexes of finite Tor amplitude `Dctf`
(blueprint `sk-rem-sf-matrix`), and the explicit intervals that come with them (blueprint
`proposition-six-operations-dctf`).

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_preservation`: `Lf^*`, `Rf_*` and `Rf_!`
  preserve `Dᵇc`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_preservation`: `Lf^*`, `⊗ᴸ`, `Rf_*`, `Rf_!`,
  `RHom`, `Rf^!` and `𝔻_X` preserve `Dctf`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_derivedHom_mapDerivedCategory`:
  on the pro-étale site, `RHom(ν^* K, ν^* M)` lies in `Dctf` for `K, M ∈ Dctf(X_ét)`.
- `AlgebraicGeometry.Etale.torAmplitudeIn_preservation`: the Tor-amplitude intervals of these
  operations.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom_of_field`
  (`proposition-six-operations-dctf--15`, in
  `WeilConjectures.SixFunctors.Etale.Derived.Stability.HomDevissage`): `RHom` preserves `Dctf`
  over an arbitrary field, by dévissage.

## Implementation notes

All statements are assembled from the individual stability theorems of
`WeilConjectures.SixFunctors.Etale.Derived.Stability` and of
`WeilConjectures.SixFunctors.ProEtale.Derived`; this file adds no new mathematics beyond
choosing the dimension bounds and the torsion exponent these theorems ask for.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]

omit [HasInvertibleExponent Λ (Spec (.of k))] in
include aX in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

For `X` of finite type over `k` and a finite `Λ` whose exponent is invertible on `X`, the
internal hom carries `Dctf(X, Λ) × Dctf(X, Λ)` into `Dctf(X, Λ)`, for two arbitrary objects.
This is the notes' proof (six operations on `Dctf`): by the generation theorem for
`Dctf(X, Λ)` it suffices to treat a first argument `Rg_* Rj_! P` supported on one stratum, where
the internal hom is computed by the tensor–Hom exchanges for `g` and `j`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom_of_field`). No Verdier duality is
used, and `k` need not be algebraically closed. -/
theorem constructibleFiniteTor_derivedHom [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) :=
  constructibleFiniteTor_derivedHom_of_field Λ aX hK hM

omit [Finite Λ] in
/-- A Tate twisting object `Λ_X(m)` is a constructible flat sheaf placed in degree `0`, every
fibre of which at a geometric point is free of rank one. -/
lemma exists_tateObject_iso_singleFunctor [HasTateTwist Λ] (X : Scheme.{u})
    [HasInvertibleExponent Λ X] (m : ℤ) :
    ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf L ∧
      ObjectProperty.flat L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (tateObject Λ X m ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj L) := by
  obtain ⟨L, hL, hfib, he⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) X m
  have := isConstructibleSheaf_and_flat_of_sheafFiber_iso Λ L hfib
  exact ⟨L, this.1, this.2, hfib, he⟩

/-- Blueprint `example-internal-hom-affine-line`: Status of the coefficient-only internal-Hom bound.

The sharp bound `[c - b, d - a]` of
`AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom_of_isDualizable` requires a site-perfect first
variable: for arbitrary bounded constructible first variables of finite Tor amplitude it is
false. Let `k` be algebraically closed, `Λ` a nonzero finite ring whose exponent is invertible on
`k`, and `s : V ⟶ 𝔸¹` the origin. Then `K = Rs_! Λ_V` and `M = Λ(1)[2]` have Tor amplitude in
`[0, 0]` and `[-2, -2]`, while `RHom(Rs_! Λ_V, Λ(1)[2]) ≅ Rs_* Rs^! Λ(1)[2] ≅ Rs_* Λ_V` is
concentrated in degree `0`, outside `[-2, -2]`; this is the blueprint's
`RHom(i_* Λ, Λ) = i_* Λ(-1)[-2]`, twisted by `Λ(1)[2]`. The identification `Rs^! Λ(1)[2] ≅ Λ_V`
is the normalisation of the twist (`AlgebraicGeometry.Etale.HasKummerClass.IsNormalized`), which
is why a normalized Tate twist datum is assumed, as in every statement comparing the twist with
geometry. The general finite-coefficient bound is the dimension-dependent
`AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`. -/
theorem not_forall_torAmplitudeIn_derivedHom [IsAlgClosed k] [Nontrivial Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] :
    ¬ ∀ (Z : Scheme.{u}) (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
      (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) Z K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b K →
          boundedConstructible (ModuleCat.{u + 1} Λ) Z M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) Z c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) Z (c - b) (d - a)
                (((RHom(Z)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  obtain ⟨_, rfl, _⟩ := HasTateTwist.IsNormalized.exists_hasKummerClass (Λ := Λ)
  intro h
  let B : Scheme.{u} := Spec (.of k)
  let aZ := 𝔸(ULift.{u} (Fin 1); B) ↘ B
  let s := 𝔸(ULift.{u} (Fin 1); B).zeroLocusSubschemeι {AffineSpace.coord B (ULift.up 0)}
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := HasInvertibleExponent.of_hom aZ
  have : HasInvertibleExponent Λ (𝔸(ULift.{u} (Fin 1); B).zeroLocusSubscheme
      {AffineSpace.coord B (ULift.up 0)}) := HasInvertibleExponent.of_hom (s ≫ aZ)
  -- the normalization of the twist: `Λ_V ≅ Rs^!(Λ(1)[2])`
  have := HasKummerClass.IsNormalized.isIso_supportedClassMap_kummerBoundary_coord (Λ := Λ) B
    (𝟙 B)
  let ι := asIso (supportedClassMap Λ s (shiftSupportedClass Λ s 2
    (kummerBoundary Λ (AffineSpace.coord B (ULift.up 0)))))
  -- the unit of `D(V_ét)` is bounded constructible of Tor amplitude `[0, 0]`
  have hU : boundedConstructible (ModuleCat.{u + 1} Λ) _
      (𝟙_ (_root_.DerivedCategory (Sheaf (𝔸(ULift.{u} (Fin 1); B).zeroLocusSubscheme
        {AffineSpace.coord B (ULift.up 0)}).smallEtaleTopology (ModuleCat.{u + 1} Λ)))) :=
    (boundedConstructible _ _).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (boundedConstructible_singleFunctor_obj _ 0)
  have hUt : torAmplitudeIn (ModuleCat.{u + 1} Λ) _ 0 0
      (𝟙_ (_root_.DerivedCategory (Sheaf (𝔸(ULift.{u} (Fin 1); B).zeroLocusSubscheme
        {AffineSpace.coord B (ULift.up 0)}).smallEtaleTopology (ModuleCat.{u + 1} Λ)))) :=
    (torAmplitudeIn _ _ 0 0).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))
  -- `K = Rs_! Λ_V` is bounded constructible of Tor amplitude `[0, 0]`
  have hK := constructibleFiniteTor_rightDerivedLowerShriek Λ aZ s ⟨hU, 0, 0, hUt⟩
  have hKt := torAmplitudeIn_rightDerivedLowerShriek_of_isClosedImmersion
    (ModuleCat.{u + 1} Λ) s (fun L ↦ hasProjectionFormula_of_finite Λ s _ L) hUt
  -- `M = Λ(1)[2]` is bounded constructible of Tor amplitude `[-2, -2]`
  obtain ⟨L₁, _, hL₁, -, ⟨e₁⟩⟩ := exists_tateObject_iso_singleFunctor Λ 𝔸(ULift.{u} (Fin 1); B) 1
  have hM : boundedConstructible (ModuleCat.{u + 1} Λ) _ ((tateObject Λ _ 1)⟦(2 : ℤ)⟧) :=
    (boundedConstructible _ _).le_shift 2 _
      ((boundedConstructible _ _).prop_of_iso e₁.symm (boundedConstructible_singleFunctor_obj _ 0))
  have hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) _ (0 - 2) (0 - 2)
      ((tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)⟦(2 : ℤ)⟧) :=
    DerivedCategory.torAmplitudeIn.shift ((torAmplitudeIn _ _ 0 0).prop_of_iso e₁.symm
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hL₁)) 2
  have h' := h _ aZ 0 0 (0 - 2) (0 - 2) _ _ hK.1 hKt hM hMt
  -- `RHom(Rs_! Λ_V, Λ(1)[2]) ≅ Rs_* RHom(Λ_V, Rs^! Λ(1)[2]) ≅ Rs_* Λ_V`
  obtain ⟨e₂⟩ := nonempty_iso_derivedHom_rightDerivedLowerShriek Λ s (𝟙_ _)
    ((tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)⟦(2 : ℤ)⟧)
  let e := e₂.symm ≪≫ (R((s)_*[ModuleCat.{u + 1} Λ])).mapIso
    ((MonoidalClosed.unitNatIso.app _).symm ≪≫ ι.symm)
  -- `Rs_* Λ_V` is concentrated in degree `-2`
  have hc := homologyConcentratedIn_of_iso _ e
    (_root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn h')
  -- hence so is `Λ_V ≅ s^* Rs_! Λ_V ≅ s^* Rs_* Λ_V`
  have hc' := homologyConcentratedIn_of_iso _
    ((D((s)^*[ModuleCat.{u + 1} Λ])).mapIso
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) s).app _).symm ≪≫
      (mapDerivedCategoryUpperStarRightDerivedLowerShriekIso (ModuleCat.{u + 1} Λ) s).app _)
    (((s)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hc)
  -- but `Λ_V` is a nonzero sheaf placed in degree `0`
  obtain ⟨L₀, _, _, hfib, ⟨e₀⟩⟩ := exists_tateObject_iso_singleFunctor Λ
    (𝔸(ULift.{u} (Fin 1); B).zeroLocusSubscheme {AffineSpace.coord B (ULift.up 0)}) 0
  let e₄ := (HasTateTwist.twistObjectZeroIso (Λ := Λ) _).symm ≪≫ e₀
  have : _root_.DerivedCategory.TStructure.t.IsLE
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀) (0 - 2 - 0) :=
    have : _root_.DerivedCategory.TStructure.t.IsLE (constantComplex Λ _) (0 - 2 - 0) := hc'.2
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e₄ _
  have hz : IsZero ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀) :=
    _root_.DerivedCategory.TStructure.t.isZero _ (0 - 2 - 0) 0
  have hz' : IsZero L₀ := IsZero.of_full_of_faithful_of_isZero
    (_root_.DerivedCategory.singleFunctor _ 0) L₀ hz
  let x₀ := (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) B
    (s := {AffineSpace.coord B (ULift.up 0)}) (by rw [Set.range_unique]; rfl)).hom
  obtain ⟨f⟩ := hfib k x₀
  have := (pointSmallEtale x₀).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  exact not_subsingleton Λ
    (ModuleCat.isZero_of_iff_subsingleton.1 ((Functor.map_isZero _ hz').of_iso f.symm))

variable (f : X ⟶ Y) (hf : f ≫ aY = aX)

include hf

omit [QuasiCompact aX] in
/-- Blueprint `sk-rem-sf-matrix`: The preservation matrix, bounded constructible cells.

For a finite `Λ` whose exponent is invertible on `k` and a morphism `f : X ⟶ Y` of schemes of
finite type over `k`, the operations `Lf^* : Dᵇc(Y) ⥤ Dᵇc(X)`, `Rf_* : Dᵇc(X) ⥤ Dᵇc(Y)` and
`Rf_! : Dᵇc(X) ⥤ Dᵇc(Y)` are defined, with no further hypothesis (the compactly supported direct
image being defined for `f` admitting a compactification). -/
theorem boundedConstructible_preservation [QuasiCompact f] [HasCompactification f] :
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
        boundedConstructible (ModuleCat.{u + 1} Λ) X
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  exact ⟨fun K hK ↦ boundedConstructible_leftDerivedUpperStar _ f hK,
    fun K hK ↦ boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent Λ f aX aY hf
      K hK,
    fun K hK ↦ boundedConstructible_rightDerivedLowerShriek Λ f aX aY hf K hK⟩

/-- Blueprint `proposition-six-operations-dctf`: The preservation matrix, constructible finite-Tor
cells.

For a finite `Λ` whose exponent is invertible on `k` and a separated morphism `f : X ⟶ Y` of
schemes of finite type over `k`, with `X` separated over `k`, the following operations preserve
the constructible complexes of finite Tor amplitude:
`Lf^* : Dctf(Y) ⥤ Dctf(X)`, `- ⊗ᴸ - : Dctf(X) × Dctf(X) ⥤ Dctf(X)`, `Rf_* : Dctf(X) ⥤ Dctf(Y)`,
`Rf_! : Dctf(X) ⥤ Dctf(Y)`, `RHom(-, -) : Dctf(X) × Dctf(X) ⥤ Dctf(X)` for two arbitrary
objects, `Rf^! : Dctf(Y) ⥤ Dctf(X)` for every such `f` (no admissibility hypothesis), and the
Verdier dual `𝔻_X : Dctf(X) ⥤ Dctf(X)`. The pro-étale internal-Hom cell is
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_derivedHom_mapDerivedCategory`.
-/
theorem constructibleFiniteTor_preservation [QuasiCompact f] [HasCompactification f]
    [IsSeparated aX] [HasCompactification aX] [IsAlgClosed k] :
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((R(f)^![Λ]).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((verdierDual Λ aX).obj (op K))) := by
  have : HasInvertibleExponent Λ Y := .of_hom aY
  have : IsSeparated f := by
    have : IsSeparated (f ≫ aY) := hf ▸ inferInstance
    exact IsSeparated.of_comp f aY
  exact ⟨fun K hK ↦ constructibleFiniteTor_leftDerivedUpperStar _ f hK,
    fun K M hK hM ↦ constructibleFiniteTor_tensor Λ X hK hM,
    fun K hK ↦ constructibleFiniteTor_rightDerivedLowerStar Λ aX aY f hf hK,
    fun K hK ↦ constructibleFiniteTor_rightDerivedLowerShriek Λ aY f hK,
    fun K M hK hM ↦ have : HasInvertibleExponent Λ X := .of_hom aX
      constructibleFiniteTor_derivedHom Λ aX hK hM,
    fun K hK ↦ constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hK,
    fun K hK ↦ constructibleFiniteTor_verdierDual Λ aX hK⟩

/-- Blueprint `proposition-six-operations-dctf`: Preservation results and their actual hypotheses.

For a finite `Λ` whose exponent is invertible on `k` and a separated morphism `f : X ⟶ Y` of
schemes of finite type over `k`, with `X` separated over `k`, the finite-coefficient preservation
results come with these intervals:

1. `Lf^*` preserves Tor amplitude in `[a, b]` (`proposition-six-operations-dctf--1`), and the
   derived tensor product of objects of Tor amplitude `[a, b]` and `[c, d]` has Tor amplitude
   in `[a + c, b + d]` (`proposition-six-operations-dctf--14`);
2. on the pro-étale site, if `dim X ≤ d`, the direct image `Rf_*` carries a bounded constructible
   complex of Tor amplitude `[a, b]` to a bounded constructible complex of Tor amplitude
   `[a, b + 2d]` (`proposition-six-operations-dctf--2`);
3. if `dim X ≤ m`, the internal hom `RHom(K, M)` of bounded constructible `K, M` of Tor
   amplitude `[a, b]` and `[c, d]` has Tor amplitude in `[c - b - 2m, d - a + 2m]`, and in the
   sharper interval `[c - b, d - a]` when `K` is dualizable (`proposition-six-operations-dctf--15`);
4. `Rf^!` sends `D_c^[a, b]` with Tor amplitude in `[a, b]` into `D_c^[a - 2D, b + 2 dim Y + 1]`
   with the same Tor bound, for a constant `D` depending only on `f`
   (`theorem-f-shriek-finite-coefficients--1`); if `dim X ≤ d` the Verdier dual `𝔻_X` sends Tor
   amplitude `[a, b]` to `[-b - 2d, -a]` (`lemma-verdier-duality-preserves-constructibility--1`),
   and it preserves `Dctf(X)` and is an involution on it (`theorem-verdier-biduality`).

The pro-étale and boundary entries are
`AlgebraicGeometry.ProEtale.DerivedCategory.preservationMatrix_of_isAlgClosure`, and the
integral entries (item 5) are `AlgebraicGeometry.Etale.preservationMatrix_integral`. -/
theorem torAmplitudeIn_preservation [QuasiCompact f] [HasCompactification f]
    [IsSeparated aX] [HasCompactification aX] [IsAlgClosed k] :
    (∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a + c) (b + d)
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
    (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))),
      ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
              ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) ∧
            ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
              ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K)) ∧
    (∀ m : ℕ, topologicalKrullDim X ≤ (m : WithBot ℕ∞) → ∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          boundedConstructible (ModuleCat.{u + 1} Λ) X M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
                (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K → IsDualizable K →
          boundedConstructible (ModuleCat.{u + 1} Λ) X M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
                (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∃ D : ℕ, ∀ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * d + 1)
          ((R(f)^![Λ]).obj K)) ∧
    (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * (d : ℤ)) (-a)
            ((verdierDual Λ aX).obj (op K))) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            ((verdierDual Λ aX).obj (op K)) ∧
          Nonempty (K ≅ (verdierDual Λ aX).obj
            (op ((verdierDual Λ aX).obj (op K))))) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  have : HasInvertibleExponent Λ Y := .of_hom aY
  have : IsSeparated f := by
    have : IsSeparated (f ≫ aY) := hf ▸ inferInstance
    exact IsSeparated.of_comp f aY
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ aY) := hf ▸ inferInstance
    exact locallyOfFiniteType_of_comp f aY
  -- the exponent `n` of `Λ`, invertible in `k`
  obtain ⟨n, hn, hΛ, hu⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Spec (.of k))
  have hnk : (n : k) ≠ 0 := by
    simpa using (hu.map (Scheme.ΓSpecIso (.of k)).hom.hom).ne_zero
  have hnΛ (M : ModuleCat.{u + 1} Λ) : n • 𝟙 M = 0 := by
    ext x
    simp [← Nat.cast_smul_eq_nsmul Λ, hΛ]
  refine ⟨fun a b K hK ↦ torAmplitudeIn_leftDerivedUpperStar _ f a b hK,
    fun a b c d K M hK hM ↦ torAmplitudeIn_tensor _ X a b c d hK hM,
    fun d hd a b K hK hKt ↦
      ⟨ProEtale.boundedConstructible_rightDerivedLowerStar _ n hnk hnΛ aY f hK,
        ProEtale.torAmplitudeIn_rightDerivedLowerStar _ n hnk hnΛ aY f d hd a b hK hKt⟩,
    fun m hm a b c d K M hK hKt hM hMt ↦
      torAmplitudeIn_derivedHom Λ aX m hm a b c d hK hKt hM hMt,
    fun a b c d K M hK hKt hKd hM hMt ↦
      torAmplitudeIn_derivedHom_of_isDualizable Λ aX a b c d hK hKt hKd hM hMt,
    exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le Λ aY f,
    fun d hd a b K hK hKt ↦ torAmplitudeIn_verdierDual Λ aX d hd a b hK hKt,
    fun K hK ↦ ⟨constructibleFiniteTor_verdierDual Λ aX hK,
      nonempty_iso_verdierDual_verdierDual Λ aX hK⟩⟩

end Etale

namespace ProEtale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `proposition-six-operations-dctf`: The preservation matrix, the pro-étale internal-Hom
cell.

Let `X` be of finite type over an algebraic closure `k` of `𝔽_p` and `Λ` a finite ring whose
exponent is invertible on `X`. For a pulled-back pair `ν^* K, ν^* M` with `K, M ∈ Dctf(X_ét, Λ)`,
the pro-étale internal hom `RHom(ν^* K, ν^* M)` lies in `Dctf(X_proét, Λ)`: it is
`ν^* RHom(K, M)` (`proposition-six-operations-dctf--15`), and `RHom(K, M) ∈ Dctf(X_ét, Λ)`. -/
theorem constructibleFiniteTor_derivedHom_mapDerivedCategory {k : Type u} [Field k] {p : ℕ}
    [Fact p.Prime] [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
        (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)) := by
  have : IsAlgClosed k := ‹IsAlgClosure (ZMod p) k›.isAlgClosed
  obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_derivedHom Λ (p := p) aX hK hM.1
  exact (constructibleFiniteTor _ X).prop_of_iso e
    (constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_derivedHom Λ aX hK hM))

/-- Blueprint `proposition-six-operations-dctf--15`: The pro-étale internal Hom for a
site-perfect first variable.

Let `X` be of finite type over an algebraic closure `k` of `𝔽_p` and `Λ` a finite ring whose
exponent is invertible on `X`. Let `K', M' ∈ Dᵇc(X_ét, Λ)` have Tor amplitude in `[a, b]` and
`[c, d]`, with `K'` site-perfect (dualizable). Then `RHom(ν^* K', ν^* M')` is bounded
constructible with Tor amplitude in `[c - b, d - a]`: it is `ν^* RHom(K', M')`
(`proposition-six-operations-dctf--15`), and `RHom(K', M')` has these properties on the étale
site (`proposition-six-operations-dctf--15`), which `ν^*` preserves
(`corollary-finite-tor-amplitude-under-comparison--1`). -/
theorem boundedConstructible_derivedHom_mapDerivedCategory_of_isDualizable {k : Type u}
    [Field k] {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasInvertibleExponent Λ X] {a b c d : ℤ}
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hKd : IsDualizable K)
    (hM : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
        (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
          (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
            (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
        (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
          (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
            (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)) := by
  have : IsAlgClosed k := ‹IsAlgClosure (ZMod p) k›.isAlgClosed
  obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_derivedHom Λ (p := p) aX ⟨hK, a, b, hKt⟩ hM
  exact ⟨(boundedConstructible _ X).prop_of_iso e
      (boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
        (Etale.boundedConstructible_derivedHom Λ aX a b c d hK hKt hM hMt)),
    (torAmplitudeIn _ X _ _).prop_of_iso e (torAmplitudeIn_mapDerivedCategory Λ
      (Etale.torAmplitudeIn_derivedHom_of_isDualizable Λ aX a b c d hK hKt hKd hM hMt))⟩

/-- Blueprint `proposition-six-operations-dctf`: Preservation results and their actual hypotheses,
the entries over `k = 𝔽̄_p`.

Let `X` be separated of finite type over an algebraic closure `k` of `𝔽_p` and `Λ` a finite ring
whose exponent is invertible on `k`.

* Item 3, pro-étale: for `K', M' ∈ Dᵇc(X_ét, Λ)` of Tor amplitude `[a, b]` and `[c, d]` with
  `K'` site-perfect, `RHom(ν^* K', ν^* M')` is bounded constructible of Tor amplitude
  `[c - b, d - a]` (`proposition-six-operations-dctf--15`); for a general first variable
  this sharp bound fails (`AlgebraicGeometry.Etale.not_forall_torAmplitudeIn_derivedHom`).
* Item 4, closed-boundary exchange: for a closed immersion `i : Z ⟶ X` and `L ∈ Dctf(X, Λ)`,
  `i^* 𝔻_X L ≅ 𝔻_Z Ri^! L` (`corollary-verdier-exchange-formulas--7`).
* Item 3, status: for a general constructible first variable of finite Tor amplitude the
  sharp bound `[c - b, d - a]` is false (`example-internal-hom-affine-line`); the counterexample
  uses the normalisation of the Tate twist, whence the normalized Tate twist datum. -/
theorem preservationMatrix_of_isAlgClosure {k : Type u} [Field k] {p : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k] [HasInvertibleExponent Λ (Spec (.of k))]
    [Nontrivial Λ] [Etale.HasTateTwist Λ] [Etale.HasTateTwist.IsNormalized Λ]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aX] [HasCompactification aX] :
    (∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K → IsDualizable K →
          Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M →
            Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              boundedConstructible (ModuleCat.{u + 1} Λ) X
                  (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
                    (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
                      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)) ∧
                torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
                  (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
                    (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
                      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M))) ∧
    (∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i]
      [HasCompactification (i ≫ aX)]
      (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X L →
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).leftDerivedFunctor.obj
            ((Etale.verdierDual Λ aX).obj (op L)) ≅
          (Etale.verdierDual Λ (i ≫ aX)).obj
            (op ((Etale.rightDerivedUpperShriek Λ i).obj L)))) ∧
    ¬ ∀ (Z : Scheme.{u}) (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
      (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z K →
        Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b K →
          Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z M →
            Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Z c d M →
              Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Z (c - b) (d - a)
                (((Etale.derivedHom (ModuleCat.{u + 1} Λ) Z).obj (op K)).obj M) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  have : IsAlgClosed k := ‹IsAlgClosure (ZMod p) k›.isAlgClosed
  exact ⟨fun a b c d K M hK hKt hKd hM hMt ↦
      boundedConstructible_derivedHom_mapDerivedCategory_of_isDualizable Λ (p := p) aX hK hKt
        hKd hM hMt,
    fun i _ _ _ L hL ↦ Etale.nonempty_iso_leftDerivedUpperStar_verdierDual Λ aX i hL,
    Etale.not_forall_torAmplitudeIn_derivedHom Λ⟩

end ProEtale.DerivedCategory

end AlgebraicGeometry
