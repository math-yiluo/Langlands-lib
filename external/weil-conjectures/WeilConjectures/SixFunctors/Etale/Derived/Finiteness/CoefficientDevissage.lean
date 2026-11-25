/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension
public import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.ConstructibleSheaf.OfForget
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage

/-!
# Dévissage of the coefficients for constant direct images

Let `f : X ⟶ S` be a morphism of schemes and `Λ` a finite ring whose exponent is invertible
on `S`. If every higher direct image `Rᵠf_* 𝔽_ℓ` of the constant sheaf `𝔽_ℓ`, for `ℓ` a prime
invertible on `S`, is constructible, then so is every higher direct image `Rᵠf_* M` of the
constant sheaf with value a finite `Λ`-module `M`
(`Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf_of_zmod`).
This is the dévissage step of the blueprint proof of
`proposition-proper-direct-image-finite-coefficients`.

The proof first changes the coefficients from `Λ` to `ℤ/N`, `N` the characteristic of `Λ`, by
restriction of scalars: it commutes with constant sheaves, with the derived direct image and
with homology, and for finite rings it preserves and reflects constructibility
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_restrictScalars_iff_of_finite`), constructibility
only depending on the underlying sheaf of sets. A finite `ℤ/N`-module is then filtered with
successive quotients `ℤ/ℓ`, `ℓ ∣ N` prime, and the higher direct images of an extension are
handled by the long exact sequence, i.e. by the triangulated subcategory of complexes with
constructible homology sheaves.

## Main statements

- `AlgebraicGeometry.Scheme.isConstructibleSheaf_restrictScalars_iff_of_finite`
- `AlgebraicGeometry.Etale.restrictScalarsHomologyRightDerivedLowerStarIso`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_constantSheaf_restrictScalars_iff`
- `Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf_of_zmod`
-/

@[expose] public section

universe v u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace ModuleCat

variable {R S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Restriction of scalars is a left adjoint (stated without raising the universe of the
modules, unlike the instance of `Mathlib`). -/
instance isLeftAdjoint_restrictScalars : (restrictScalars.{v} φ).IsLeftAdjoint :=
  (restrictCoextendScalarsAdj.{v, v, v} φ).isLeftAdjoint

/-- Restriction of scalars is a right adjoint without raising the universe of the modules
(`ModuleCat.isRightAdjoint_restrictScalars`), registered as an instance. -/
instance : (restrictScalars.{v} φ).IsRightAdjoint :=
  isRightAdjoint_restrictScalars.{v, v} φ

end ModuleCat

namespace AlgebraicGeometry

namespace Scheme

variable {Y : Scheme.{u}} {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ']

/-- **The underlying sheaf of sets of a finite locally constant sheaf of modules over a finite
ring is finite locally constant**: forgetting the module structure preserves constant sheaves
and stalks. -/
theorem IsFiniteLocallyConstantSheaf.forget [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [h : IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := h.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · have := h𝒰 i
    exact inferInstanceAs (((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
      (F.over _)).IsConstant _)
  · have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    have hfg := h.isFinitelyGenerated_sheafFiber Ω s
    rw [ModuleCat.isFinitelyGenerated_iff] at hfg
    have : Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :=
      Module.finite_of_finite Λ
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    exact @Finite.of_equiv _ _ this (((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F).symm.toEquiv

/-- **Finite local constancy under restriction of scalars between finite rings.** For a
morphism `φ : Λ →+* Λ'` of finite rings, a sheaf of `Λ'`-modules is finite locally constant if
and only if its restriction of scalars to `Λ` is: both conditions only depend on the underlying
sheaf of sets. -/
theorem isFiniteLocallyConstantSheaf_restrictScalars_iff [Finite Λ] [Finite Λ'] (φ : Λ →+* Λ')
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars Y.smallEtaleTopology φ).obj G) ↔
      IsFiniteLocallyConstantSheaf G :=
  ⟨fun _ ↦ IsFiniteLocallyConstantSheaf.of_forget G
      (IsFiniteLocallyConstantSheaf.forget ((Sheaf.restrictScalars _ φ).obj G)),
    fun _ ↦ IsFiniteLocallyConstantSheaf.of_forget _ (IsFiniteLocallyConstantSheaf.forget G)⟩

/-- **Constructibility under restriction of scalars between finite rings.** For a morphism
`φ : Λ →+* Λ'` of finite rings, a sheaf of `Λ'`-modules is constructible if and only if its
restriction of scalars to `Λ` is: pullback to the strata commutes with restriction of scalars
(`AlgebraicGeometry.Etale.isIso_upperStarRestrictScalars`). -/
theorem isConstructibleSheaf_restrictScalars_iff_of_finite [Finite Λ] [Finite Λ']
    (φ : Λ →+* Λ') (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    IsConstructibleSheaf ((Sheaf.restrictScalars Y.smallEtaleTopology φ).obj G) ↔
      IsConstructibleSheaf G := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, fun i ↦ ?_⟩
    have := hS i
    rw [← isFiniteLocallyConstantSheaf_restrictScalars_iff φ]
    exact IsFiniteLocallyConstantSheaf.of_iso
      (F := (Etale.upperStar _ (S.immersion i)).obj ((Sheaf.restrictScalars _ φ).obj G))
      (asIso ((Etale.upperStarRestrictScalars φ (S.immersion i)).app G))
  · rintro ⟨S, hS⟩
    refine ⟨S, fun i ↦ ?_⟩
    have := (isFiniteLocallyConstantSheaf_restrictScalars_iff φ _).2 (hS i)
    exact IsFiniteLocallyConstantSheaf.of_iso
      (F := (Sheaf.restrictScalars _ φ).obj ((Etale.upperStar _ (S.immersion i)).obj G))
      (asIso ((Etale.upperStarRestrictScalars φ (S.immersion i)).app G)).symm

end Scheme

namespace Etale

open Scheme _root_.DerivedCategory

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ']

/-- **Restriction of scalars commutes with the higher direct images.** For `φ : Λ →+* Λ'`, a
morphism `f : X ⟶ S` and a sheaf `F` of `Λ'`-modules on `X`, the restriction of scalars of
`Rᵠf_* F` is `Rᵠf_*` of the restriction of scalars of `F`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`). -/
noncomputable def restrictScalarsHomologyRightDerivedLowerStarIso (φ : Λ →+* Λ')
    {X S : Scheme.{u}} (f : X ⟶ S) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    (q : ℤ) :
    (Sheaf.restrictScalars S.smallEtaleTopology φ).obj ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ'])).obj ((singleFunctor _ 0).obj F))) ≅
    (homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
      ((singleFunctor _ 0).obj ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F))) :=
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  (Sheaf.restrictScalars S.smallEtaleTopology φ).mapIso ((homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlusCompatibility.app K).symm) ≪≫
    ((Sheaf.restrictScalars S.smallEtaleTopology φ).mapDerivedCategoryPlusHomologyFunctorIso
      q).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((rightDerivedLowerStarRestrictScalars φ f).app K)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.mapIso
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusSingleFunctor
          0).app F)) ≪≫
    (homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _)

/-- **Change of coefficients for constant higher direct images.** For a morphism `φ : Λ →+* Λ'`
of finite rings, a morphism `f : X ⟶ S` and a `Λ'`-module `M`, the higher direct image
`Rᵠf_* M` of the constant sheaf `M` is constructible if and only if the one of the constant
sheaf of `Λ`-modules `M` is: restriction of scalars commutes with constant sheaves
(`CategoryTheory.constantCommuteCompose`) and higher direct images
(`AlgebraicGeometry.Etale.restrictScalarsHomologyRightDerivedLowerStarIso`), and preserves and
reflects constructibility. -/
theorem isConstructibleSheaf_homology_constantSheaf_restrictScalars_iff
    [Finite Λ] [Finite Λ'] (φ : Λ →+* Λ') {X S : Scheme.{u}} (f : X ⟶ S)
    (M : ModuleCat.{u + 1} Λ') (q : ℤ) :
    IsConstructibleSheaf ((homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
      ((singleFunctor _ 0).obj ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        ((ModuleCat.restrictScalars.{u + 1} φ).obj M))))) ↔
    IsConstructibleSheaf ((homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} Λ'])).obj
      ((singleFunctor _ 0).obj ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj
        M)))) := by
  rw [← Scheme.isConstructibleSheaf_restrictScalars_iff_of_finite φ]
  let e : _ ≅ (homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
      ((singleFunctor _ 0).obj ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        ((ModuleCat.restrictScalars.{u + 1} φ).obj M)))) :=
    restrictScalarsHomologyRightDerivedLowerStarIso φ f
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj M) q ≪≫
      (homologyFunctor _ q).mapIso ((R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((singleFunctor _ 0).mapIso ((constantCommuteCompose X.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1} φ)).app M)))
  exact ⟨fun _ ↦ IsConstructibleSheaf.of_iso e.symm, fun _ ↦ IsConstructibleSheaf.of_iso e⟩

/-- **Constant direct images of an extension.** For a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of finite modules over a finite ring `Λ`, if all the higher direct images
of the constant sheaves `M₁` and `M₃` along `f` are constructible, so are those of `M₂`: the
sequence of constant sheaves is exact (`AlgebraicGeometry.Scheme.constantEtaleSheaf_shortExact`),
so that `Rf_*` gives a distinguished triangle, and the complexes with constructible homology
sheaves form a triangulated subcategory. -/
theorem constructibleHomology_rightDerivedLowerStar_constantSheaf_of_shortExact [Finite Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) {M : ShortComplex (ModuleCat.{u + 1} Λ)}
    [Finite M.X₁] [Finite M.X₂] [Finite M.X₃] (hM : M.ShortExact)
    (h₁ : Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M.X₁))))
    (h₃ : Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M.X₃)))) :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M.X₂))) :=
  (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).ext_of_isTriangulatedClosed₂
    _ ((R((f)_*[ModuleCat.{u + 1} Λ])).map_distinguished _
      (Scheme.constantEtaleSheaf_shortExact X Λ M hM).singleTriangle_distinguished) h₁ h₃

/-- **A cyclic submodule of prime order.** For an element `x` of prime additive order `ℓ` of a
module `M` over `ℤ/N`, the map `a ↦ a • x` is an injective linear map from `ℤ/ℓ`, viewed as a
`ℤ/N`-module by restriction of scalars along any ring map `ψ : ℤ/N →+* ℤ/ℓ`. -/
lemma exists_injective_linearMap_restrictScalars_of_addOrderOf {N ℓ : ℕ} [NeZero N]
    [Fact ℓ.Prime] (ψ : ULift.{u + 1} (ZMod N) →+* ULift.{u + 1} (ZMod ℓ))
    (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) {x : M} (hx : addOrderOf x = ℓ) :
    ∃ g : (ModuleCat.restrictScalars.{u + 1} ψ).obj (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))
      →ₗ[ULift.{u + 1} (ZMod N)] M, Function.Injective g := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let g₀ : ULift.{u + 1} (ZMod ℓ) →+ M :=
    { toFun a := a.down.val • x
      map_zero' := by simp
      map_add' a b := by
        have h := mod_addOrderOf_nsmul x (a.down.val + b.down.val)
        rw [hx] at h
        rw [ULift.add_down, ZMod.val_add, h, add_nsmul] }
  have hcast (r : ULift.{u + 1} (ZMod N)) : r = ((r.down.val : ℕ) : ULift.{u + 1} (ZMod N)) :=
    ULift.ext (by rw [ULift.down_natCast, ZMod.natCast_zmod_val])
  refine ⟨{ toFun := g₀, map_add' := g₀.map_add, map_smul' := fun r a ↦ ?_ }, ?_⟩
  · rw [RingHom.id_apply, hcast r, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact g₀.map_nsmul _ a
  · refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
    have ha' : (ULift.down a).val • x = 0 := ha
    have h₁ := addOrderOf_dvd_of_nsmul_eq_zero ha'
    rw [hx] at h₁
    exact ULift.ext ((ZMod.val_eq_zero _).1
      (Nat.eq_zero_of_dvd_of_lt h₁ (ZMod.val_lt (ULift.down a))))

/-- **Dévissage of the coefficients over `ℤ/N`.** Let `f : X ⟶ S` be a morphism and `N ≠ 0`. If
for every prime `ℓ ∣ N` all the higher direct images `Rᵠf_* 𝔽_ℓ` of the constant sheaf `𝔽_ℓ`
are constructible, then for every finite `ℤ/N`-module `M` all the higher direct images
`Rᵠf_* M` are constructible: by induction on the cardinality of `M`, along the extension of
`M / (ℤ/ℓ) x` by `(ℤ/ℓ) x` for an element `x` of prime order `ℓ` (Cauchy's theorem). -/
theorem constructibleHomology_rightDerivedLowerStar_constantSheaf_zmod {X S : Scheme.{u}}
    (f : X ⟶ S) (N : ℕ) [NeZero N]
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ N →
      Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) S
        ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj ((singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))))
    (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) [Finite M] :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) S
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N)))).obj
          M))) := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card M = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  by_cases h1 : n = 1
  · subst h1
    have : Subsingleton M := (Nat.card_eq_one_iff_unique.1 hn).1
    exact ObjectProperty.prop_of_isZero _ (Functor.map_isZero _ (Functor.map_isZero _
      (Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton M))))
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' ℓ (hn ▸ hℓn)
  have hℓN : ℓ ∣ N := by
    rw [← hx]
    refine addOrderOf_dvd_of_nsmul_eq_zero ?_
    rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (ZMod N))]
    have : ((N : ℕ) : ULift.{u + 1} (ZMod N)) = 0 :=
      ULift.ext (by rw [ULift.down_natCast, ZMod.natCast_self, ULift.zero_down])
    rw [this, zero_smul]
  let ψ : ULift.{u + 1} (ZMod N) →+* ULift.{u + 1} (ZMod ℓ) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom hℓN (ZMod ℓ)).comp ULift.ringEquiv.toRingHom)
  obtain ⟨g, hg⟩ := exists_injective_linearMap_restrictScalars_of_addOrderOf ψ M hx
  let T := ModuleCat.shortComplexOfCompEqZero g (LinearMap.range g).mkQ
    (LinearMap.ext fun a ↦ (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self g a))
  have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
    (LinearMap.exact_iff.2 (Submodule.ker_mkQ _)) hg (Submodule.mkQ_surjective _)
  have : Finite (M ⧸ LinearMap.range g) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have : Finite T.X₁ := inferInstanceAs (Finite (ULift.{u + 1} (ZMod ℓ)))
  have : Finite T.X₂ := inferInstanceAs (Finite M)
  have : Finite T.X₃ := inferInstanceAs (Finite (M ⧸ LinearMap.range g))
  have hcard : Nat.card (M ⧸ LinearMap.range g) < n := by
    have h₂ : Nat.card (LinearMap.range g) = ℓ := by
      have h₃ : Nat.card (ULift.{u + 1} (ZMod ℓ)) = ℓ := by simp
      exact (Nat.card_congr (LinearEquiv.ofInjective g hg).toEquiv).symm.trans h₃
    have h₄ := Submodule.card_eq_card_quotient_mul_card (LinearMap.range g)
    have h₅ : 0 < Nat.card (M ⧸ LinearMap.range g) := Nat.card_pos
    rw [h₂, hn] at h₄
    nlinarith [hℓ.two_le]
  refine constructibleHomology_rightDerivedLowerStar_constantSheaf_of_shortExact f hT
    (fun q ↦ ?_) (ih _ hcard (ModuleCat.of _ (M ⧸ LinearMap.range g)) rfl)
  exact (isConstructibleSheaf_homology_constantSheaf_restrictScalars_iff ψ f _ q).2 (h ℓ hℓN q)

/-- **Dévissage of the coefficients for constant direct images.** This is the dévissage step of
the blueprint proof of `proposition-proper-direct-image-finite-coefficients`.

Let `f : X ⟶ S` be a morphism of schemes and `Λ` a finite ring whose exponent is invertible on
`S`. Suppose that for every prime `ℓ` invertible on `S` every higher direct image `Rᵠf_* 𝔽_ℓ`
of the constant sheaf `𝔽_ℓ` is constructible. Then for every finite `Λ`-module `M` every higher
direct image `Rᵠf_* M` of the constant sheaf `M` is constructible. Indeed, restriction of
scalars along `ℤ/N →+* Λ`, `N` the characteristic of `Λ`, reduces this to a finite `ℤ/N`-module
(`AlgebraicGeometry.Etale.isConstructibleSheaf_homology_constantSheaf_restrictScalars_iff`), which
has a filtration with successive quotients `𝔽_ℓ` for primes `ℓ ∣ N`
(`AlgebraicGeometry.Etale.constructibleHomology_rightDerivedLowerStar_constantSheaf_zmod`). -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf_of_zmod
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    [HasInvertibleExponent Λ S]
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime] [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] (q : ℤ),
      IsConstructibleSheaf ((homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
          ((singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))))
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  obtain ⟨n, -, hnΛ, hnu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  have : NeZero (ringChar Λ) := ⟨CharP.char_ne_zero_of_finite Λ (ringChar Λ)⟩
  let φ : ULift.{u + 1} (ZMod (ringChar Λ)) →+* Λ :=
    (ZMod.castHom dvd_rfl Λ).comp ULift.ringEquiv.toRingHom
  have : Finite ((ModuleCat.restrictScalars.{u + 1} φ).obj M) := inferInstanceAs (Finite M)
  refine (isConstructibleSheaf_homology_constantSheaf_restrictScalars_iff
    φ f M q).1 (constructibleHomology_rightDerivedLowerStar_constantSheaf_zmod f _
      (fun ℓ _ hℓN q ↦ ?_) _ q)
  have : HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S := by
    obtain ⟨k, hk⟩ := hℓN.trans (ringChar.dvd hnΛ)
    refine ⟨ℓ, (Fact.out : ℓ.Prime).pos, ULift.ext (by simp), ?_⟩
    rw [hk, Nat.cast_mul] at hnu
    exact isUnit_of_mul_isUnit_left hnu
  exact h ℓ q
end Etale

end AlgebraicGeometry
