/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapRingObjMap
public import WeilConjectures.NumberTheory.Padics.IntegersModPowResidueField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFiniteCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndConstructible
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp

/-!
# The derived reduction to the residue field preserves boundedness

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`, and `X` a scheme. For a generator `ϖ` of the maximal ideal of `𝒪_E`, the sequence
`0 ⟶ 𝒪_{E,X} --ϖ--> 𝒪_{E,X} ⟶ 𝔽_{E,X} ⟶ 0` is short exact, so that the derived reduction
`K ↦ K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` sits in a triangle `K --ϖ--> K ⟶ K ⊗ᴸ 𝔽_E ⟶ K[1]` and preserves
bounded complexes (`ProEtale.bounded_derivedExtendScalars_padicIntegersToResidueField`). For
`n ≥ 1` the residue map factors through `𝒪_E ⧸ ℓⁿ`, so that the reduction to `𝔽_E` of the
reduction `K ⊗ᴸ 𝒪_E ⧸ ℓⁿ` modulo `ℓⁿ` of a bounded complex `K` is bounded
(`ProEtale.bounded_derivedExtendScalars_integersModPowToResidueField`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- For `n ≥ 1`, the residue map `𝒪̲_E ⟶ 𝔽̲_E` factors through the reduction
`𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`. -/
lemma padicIntegersRingObjToIntegersModPow_comp_continuousMapRingObjMap (n : ℕ) [NeZero n] :
    padicIntegersRingObjToIntegersModPow.{u} ℓ E n ≫
        continuousMapRingObjMap (PadicAlgCl.integersModPowToResidueField ℓ E n)
          continuous_of_discreteTopology =
      padicIntegersRingObjToResidueField ℓ E := by
  rw [padicIntegersRingObjToIntegersModPow, continuousMapRingObjMap, ← Functor.map_comp]
  rfl

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- **The derived reduction to the residue field preserves boundedness**: if
`K ∈ D(Mod_{𝒪_{E,X}})` is bounded, so is `K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}`. By the reduction triangle
`K --ϖ--> K ⟶ K ⊗ᴸ 𝔽_E ⟶ K[1]` for a uniformizer `ϖ`, its restriction of scalars to `𝒪_{E,X}` is
bounded, and restriction of scalars is exact and faithful. -/
theorem bounded_derivedExtendScalars_padicIntegersToResidueField
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hK : DerivedCategory.TStructure.t.bounded K) :
    DerivedCategory.TStructure.t.bounded
      ((Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E)
        X)).leftDerivedFunctor.obj K) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  obtain ⟨_, _, _, hT⟩ := Mod.exists_distinguished_regularEndSMul_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K
  let φ := coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E) X
  have h₃ : DerivedCategory.TStructure.t.bounded
      ((Mod.comap φ).mapDerivedCategory.obj ((Mod.extendScalars φ).leftDerivedFunctor.obj K)) :=
    DerivedCategory.TStructure.t.bounded.ext_of_isTriangulatedClosed₃ _ hT hK hK
  rw [← DerivedCategory.exists_homologyConcentratedIn_iff_bounded] at h₃ ⊢
  obtain ⟨a, b, hab⟩ := h₃
  exact ⟨a, b,
    (Mod.comap φ).homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj hab⟩

/-- For `n ≥ 1`, the reduction to the residue field `𝔽_E` of the reduction `K ⊗ᴸ 𝒪_E ⧸ ℓⁿ` of a
bounded complex `K ∈ D(Mod_{𝒪_{E,X}})` is bounded: it is `K ⊗ᴸ 𝔽_E`
(`CategoryTheory.Mod.derivedExtendScalarsCompIso`). -/
theorem bounded_derivedExtendScalars_integersModPowToResidueField (n : ℕ) [NeZero n]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hK : DerivedCategory.TStructure.t.bounded K) :
    DerivedCategory.TStructure.t.bounded
      ((Mod.extendScalars (coefficientMap (Profinite.continuousMapRingObjMap.{u}
        (PadicAlgCl.integersModPowToResidueField ℓ E n) continuous_of_discreteTopology)
          X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj K)) := by
  refine DerivedCategory.TStructure.t.bounded.prop_of_iso
    ((Mod.derivedExtendScalarsCompIso _ _ _ ?_).app K)
    (bounded_derivedExtendScalars_padicIntegersToResidueField X ℓ E K hK)
  rw [← Functor.map_comp,
    Profinite.padicIntegersRingObjToIntegersModPow_comp_continuousMapRingObjMap]

end AlgebraicGeometry.ProEtale
