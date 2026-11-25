/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralQuotient

/-!
# The derived (Push) comparison along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a subfield with ring of integers `𝒪_E`, `n` a natural number and
`f : X ⟶ Y` a morphism of schemes. We show that the comparison
`𝒪_E ⧸ ℓⁿ ⊗ᴸ Rf_* K ⟶ Rf_*(𝒪_E ⧸ ℓⁿ ⊗ᴸ K)` is an isomorphism for every bounded below
`K ∈ D(𝒪_{E,X})`
(`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_integersModPow_app`).

This is the instance `ϖ = ℓⁿ` of
`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_app_of_shortExact`: the
multiplication by the constant `ℓⁿ ∈ 𝒪_E` on `𝒪_{E,X}` is `ℓⁿ • 𝟙`
(`ProEtale.padicIntegersRegularEnd_natCast_pow_hom`), so that
`0 ⟶ 𝒪_{E,X} --ℓⁿ--> 𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X ⟶ 0` is short exact
(`ProEtale.shortExact_padicIntegersRegularEnd_integersModPow`, from
`ProEtale.shortExact_integersModPowReduction`), and `ℓⁿ ≠ 0` in `E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  (n : ℕ)

/-- The multiplication by the constant `ℓⁿ ∈ 𝒪_E` on `𝒪̲_E` is `ℓⁿ • 𝟙`. -/
lemma Profinite.padicIntegersRingObjMulLeft_natCast_pow :
    Profinite.padicIntegersRingObjMulLeft.{u} ℓ E ((ℓ : PadicAlgCl.integers ℓ E) ^ n) =
      (ℓ : ℤ) ^ n • 𝟙 (Profinite.padicIntegersRingObj.{u} ℓ E) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ext S a
  refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
  rw [Profinite.padicIntegersRingObjMulLeft_hom_app_apply,
    Profinite.zsmul_id_padicIntegersRingObj_hom_app_apply]
  simp [zsmul_eq_mul]

/-- **The multiplication by the constant `ℓⁿ ∈ 𝒪_E` on `𝒪_{E,X}` is `ℓⁿ • 𝟙`.** -/
lemma padicIntegersRegularEnd_natCast_pow_hom :
    (padicIntegersRegularEndOfAlgebra X ℓ E ((ℓ : PadicAlgCl.integers ℓ E) ^ n)).hom =
      (ℓ : ℤ) ^ n • 𝟙 (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  rw [padicIntegersRegularEnd_hom, padicIntegersMulLeft,
    Profinite.padicIntegersRingObjMulLeft_natCast_pow, Functor.map_zsmul,
    CategoryTheory.Functor.map_id]

/-- `ℓⁿ` vanishes in `(𝒪_E ⧸ ℓⁿ)_X`, with `ℓⁿ` seen as an endomorphism of the regular
`𝒪_{E,X}`-module. -/
lemma padicIntegersRegularEnd_hom_comp_integersModPowReduction :
    (padicIntegersRegularEndOfAlgebra X ℓ E ((ℓ : PadicAlgCl.integers ℓ E) ^ n)).hom ≫
      coefficientMap (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) X = 0 := by
  rw [padicIntegersRegularEnd_natCast_pow_hom]
  exact zsmul_id_comp_integersModPowReduction X ℓ E n

/-- **`0 ⟶ 𝒪_{E,X} --ℓⁿ--> 𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X ⟶ 0` is short exact**, with `ℓⁿ` seen as an
endomorphism of the regular `𝒪_{E,X}`-module. -/
lemma shortExact_padicIntegersRegularEnd_integersModPow :
    (ShortComplex.mk _ _
      (padicIntegersRegularEnd_hom_comp_integersModPowReduction X ℓ E n)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk
      (S₁ := ShortComplex.mk _ _ (zsmul_id_comp_integersModPowReduction X ℓ E n))
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [padicIntegersRegularEnd_natCast_pow_hom]) (by simp))
    (shortExact_integersModPowReduction X ℓ E n)

namespace CondensedRing

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The derived (Push) comparison for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`**: for every morphism of schemes
`f : X ⟶ Y` and every bounded below `K ∈ D(𝒪_{E,X})`, the comparison
`𝒪_E ⧸ ℓⁿ ⊗ᴸ Rf_* K ⟶ Rf_*(𝒪_E ⧸ ℓⁿ ⊗ᴸ K)` is an isomorphism. -/
theorem isIso_derivedUpperStarExtendScalarsPushHom_integersModPow_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (m : ℤ) [K.IsGE m] :
    IsIso ((derivedUpperStarExtendScalarsPushHom
      (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) f).app K) :=
  isIso_derivedUpperStarExtendScalarsPushHom_app_of_shortExact ℓ E f _
    ((ℓ : PadicAlgCl.integers ℓ E) ^ n)
    (fun Z ↦ padicIntegersRegularEnd_hom_comp_integersModPowReduction Z ℓ E n)
    (fun Z ↦ shortExact_padicIntegersRegularEnd_integersModPow Z ℓ E n)
    (by
      push_cast
      exact pow_ne_zero n (Profinite.natCast_ne_zero_of_algebra ℓ E)) K m

end CondensedRing

end AlgebraicGeometry.ProEtale
