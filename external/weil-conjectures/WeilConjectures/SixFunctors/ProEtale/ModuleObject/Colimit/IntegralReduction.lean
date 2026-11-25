/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangle
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.IntegersModPow
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull

/-!

# Reduction of `𝒪_E`-coefficients modulo `ℓⁿ`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a subfield with ring of integers `𝒪_E`, `n` a natural number and
`X` a scheme. The reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` of condensed rings
(`Profinite.padicIntegersRingObjToIntegersModPow`) pulls back to the morphism of coefficient
ring objects `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` on `X_proét` (`ProEtale.integersModPowReduction`), one of
the coefficient changes of the blueprint (`proposition-six-operations-change-coefficients`,
coefficient maps `𝒪_E → A` to finite rings). Its derived extension of scalars is the *reduction
modulo `ℓⁿ`*
```
K ↦ K ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ = L(Ext) K : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{(𝒪_E ⧸ ℓⁿ)_X}).
```
This file proves:

* `ProEtale.shortExact_integersModPowReduction`: the sequence
  `0 ⟶ 𝒪_{E,X} --ℓⁿ--> 𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X ⟶ 0` of abelian sheaves on `X_proét` is short
  exact: it is the inverse image along the exact functor `p_X^*` of the corresponding short
  exact sequence of condensed abelian groups
  (`Profinite.shortExact_padicIntegersRingObjToIntegersModPow`).
* `ProEtale.exists_distinguished_integersModPowReduction`: **the reduction triangle**: for every
  `K ∈ D(Mod_{𝒪_{E,X}})` there is a distinguished triangle
  `K --ℓⁿ--> K ⟶ K ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ ⟶ K[1]`, the reduction being regarded as a complex of
  `𝒪_{E,X}`-modules: `𝒪_E ⧸ ℓⁿ` has the flat resolution `𝒪_E --ℓⁿ--> 𝒪_E`
  (`Mod.exists_distinguished_zsmul_derivedExtendScalars`).
* `ProEtale.integersModPowReductionUpperStarIso`: the reduction commutes with the derived
  pullback along any morphism of schemes `f`,
  `Lf^* ⋙ (- ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ) ≅ (- ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ) ⋙ Lf^*`. The reduction is not flat, so
  `ProEtale.CondensedRing.derivedPullIso` does not apply; this is the instance of
  `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso`, which uses that the pullbacks of
  module objects are exact.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The inverse image `p^*` from condensed abelian groups to abelian sheaves on `(Spec ℤ)_proét`
is left exact: it is a left Kan extension along the representably flat functor
`S ↦ Spec LC(S, ℤ)` followed by sheafification. -/
instance preservesFiniteLimits_pointUpperStar : PreservesFiniteLimits pointUpperStar.{u} := by
  unfold pointUpperStar Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

/-- The inverse image `p_X^* = π_X^* ∘ p^*` from condensed abelian groups to abelian sheaves on
`X_proét` is left exact. -/
instance preservesFiniteLimits_upperStarFromPoint (X : Scheme.{u}) :
    PreservesFiniteLimits (upperStarFromPoint X) := by
  unfold upperStarFromPoint
  infer_instance

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  (n : ℕ)

/-- The reduction `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` of coefficient ring objects on `X_proét`: the
pullback along `p_X` of the reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` of condensed rings. -/
noncomputable abbrev integersModPowReduction :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X ⟶
      condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X :=
  coefficientMap (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) X

/-- `ℓⁿ` vanishes in `(𝒪_E ⧸ ℓⁿ)_X`. -/
lemma zsmul_id_comp_integersModPowReduction :
    ((ℓ : ℤ) ^ n • 𝟙 (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) ≫
      integersModPowReduction X ℓ E n = 0 := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, ← Functor.map_comp,
    Profinite.zsmul_id_comp_padicIntegersRingObjToIntegersModPow, Functor.map_zero]

/-- **`0 ⟶ 𝒪_{E,X} --ℓⁿ--> 𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X ⟶ 0` is short exact**: it is the inverse image
along the exact functor `p_X^*` of the short exact sequence
`0 ⟶ 𝒪̲_E --ℓⁿ--> 𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲ ⟶ 0` of condensed abelian groups. -/
lemma shortExact_integersModPowReduction :
    (ShortComplex.mk _ _ (zsmul_id_comp_integersModPowReduction X ℓ E n)).ShortExact := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  refine ShortComplex.shortExact_of_iso ?_
    ((Profinite.shortExact_padicIntegersRingObjToIntegersModPow.{u} ℓ E n).map_of_exact
      (upperStarFromPoint X))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp)

/-- **The reduction triangle**: for every `K ∈ D(Mod_{𝒪_{E,X}})` there is a distinguished
triangle `K --ℓⁿ--> K ⟶ K ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ ⟶ K[1]` in `D(Mod_{𝒪_{E,X}})`, where the reduction
`K ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ = L(Ext) K` is regarded as a complex of `𝒪_{E,X}`-modules by restriction of
scalars. -/
theorem exists_distinguished_integersModPowReduction
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    ∃ (g : K ⟶ D(Mod.comap (integersModPowReduction X ℓ E n)).obj
        (L(Mod.extendScalars (integersModPowReduction X ℓ E n)).obj K))
      (h : D(Mod.comap (integersModPowReduction X ℓ E n)).obj
        (L(Mod.extendScalars (integersModPowReduction X ℓ E n)).obj K) ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk ((ℓ : ℤ) ^ n • 𝟙 K) g h ∈ distTriang _ :=
  Mod.exists_distinguished_zsmul_derivedExtendScalars _
    (zsmul_id_comp_integersModPowReduction X ℓ E n) (shortExact_integersModPowReduction X ℓ E n) K

open CondensedRing

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The reduction modulo `ℓⁿ` commutes with the derived pullback**:
`Lf^* ⋙ (- ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ) ≅ (- ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ) ⋙ Lf^*`, the instance of (Pull) for the
non-flat coefficient change `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso`). -/
noncomputable def integersModPowReductionUpperStarIso :
    L((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧) ⋙
        L(Mod.extendScalars (integersModPowReduction X ℓ E n)) ≅
      L(Mod.extendScalars (integersModPowReduction Y ℓ E n)) ⋙
        L((f)^*⟦Profinite.integersModPowRingObj ℓ E n⟧) :=
  CondensedRing.derivedUpperStarExtendScalarsIso
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) f

end AlgebraicGeometry.ProEtale
