/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat

/-!
# Flatness of `E_X` over `𝒪_{E,X}` for a field `E` embedded in `ℚ̄_ℓ`

Let `E` be a field with an embedding `E → ℚ̄_ℓ`, with the norm restricted from `ℚ̄_ℓ`
(`PadicAlgCl.normedFieldOfAlgebra`) and ring of integers `𝒪_E = PadicAlgCl.integers ℓ E`. This
file provides, for such `E`, the inclusion `𝒪̲_E ⟶ E̲ = C(-, E)` of condensed rings
(`Profinite.padicIntegersRingObjToSubfieldRingObj`), its pullback `𝒪_{E,X} ⟶ E_X` to `X_proét`
(`ProEtale.padicIntegersToSubfieldRingObj`), and the flatness of `E_X` over `𝒪_{E,X}`
(`ProEtale.preservesFiniteLimits_extendScalars_padicIntegersToSubfieldRingObj`).

For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` these are
`ProEtale.padicIntegersRingObjToContinuousMapRingObj`, `ProEtale.padicIntegersToPadicSubfield`
and `ProEtale.preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield`. The proof is the
same: `E̲` is the sequential colimit of the multiplications by `ℓ` on `𝒪̲_E`
(`Profinite.isColimitPadicIntegersRingObjToSubfieldSmulSequenceCocone`), since every continuous
map from a profinite set to `E` is `ℓ⁻ᵐ` times a continuous map to `𝒪_E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace Profinite

open AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The inclusion `𝒪̲_E ⟶ E̲ = C(-, E)` of ring objects of condensed abelian groups, for a field
`E` with an embedding `E → ℚ̄_ℓ` and the topology restricted from `ℚ̄_ℓ`: the abelian sheaf
morphism underlying `Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing`. -/
noncomputable def padicIntegersRingObjToSubfieldRingObj :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    padicIntegersRingObj.{u} ℓ E ⟶ continuousMapRingObj E :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ E)

instance :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    IsMonHom (padicIntegersRingObjToSubfieldRingObj.{u} ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (padicIntegersCondensedRingToPadicSubfieldCondensedRing.{u} ℓ E)))

lemma padicIntegersRingObjToSubfieldRingObj_hom_app_apply (S : Profinite.{u}ᵒᵖ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    ∀ a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E),
      (padicIntegersRingObjToSubfieldRingObj ℓ E).hom.app S a =
        ULift.up ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(PadicAlgCl.integers ℓ E, E)).comp a.down) :=
  fun _ ↦ rfl

/-- The map `c_k = ℓ⁻ᵏ φ : 𝒪̲_E ⟶ E̲`, where `φ` is the inclusion. -/
noncomputable def padicIntegersRingObjToSubfieldRingObjInvPow (k : ℕ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    padicIntegersRingObj.{u} ℓ E ⟶ continuousMapRingObj E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  padicIntegersRingObjToSubfieldRingObj ℓ E ≫ continuousMapRingObjMulLeft E ((ℓ : E)⁻¹ ^ k)

lemma padicIntegersRingObjToSubfieldRingObjInvPow_zero :
    padicIntegersRingObjToSubfieldRingObjInvPow.{u} ℓ E 0 =
      padicIntegersRingObjToSubfieldRingObj ℓ E := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  rw [padicIntegersRingObjToSubfieldRingObjInvPow, pow_zero, continuousMapRingObjMulLeft_one,
    Category.comp_id]

/-- The prime `ℓ` is nonzero in `E`, which has characteristic zero, being a subfield of `ℚ̄_ℓ`. -/
lemma natCast_ne_zero_of_algebra : (ℓ : E) ≠ 0 :=
  have : CharZero E := (algebraMap E (PadicAlgCl ℓ)).charZero
  Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero

lemma nsmul_padicIntegersRingObjToSubfieldRingObjInvPow_succ (k : ℕ) :
    ℓ • padicIntegersRingObjToSubfieldRingObjInvPow.{u} ℓ E (k + 1) =
      padicIntegersRingObjToSubfieldRingObjInvPow ℓ E k := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  rw [padicIntegersRingObjToSubfieldRingObjInvPow, padicIntegersRingObjToSubfieldRingObjInvPow,
    ← Preadditive.comp_nsmul, nsmul_continuousMapRingObjMulLeft, pow_succ', ← _root_.mul_assoc,
    mul_inv_cancel₀ (natCast_ne_zero_of_algebra ℓ E), _root_.one_mul]

/-- **`E̲ = colim(𝒪̲_E --ℓ--> 𝒪̲_E --ℓ--> ⋯)`**: the maps `ℓ⁻ᵏ φ : 𝒪̲_E ⟶ E̲` exhibit the condensed
abelian group `E̲` as the sequential colimit of the multiplications by `ℓ` on `𝒪̲_E`. Sectionwise,
every continuous map from a profinite set to `E` is `ℓ⁻ᵐ` times a continuous map to `𝒪_E`
(`PadicAlgCl.exists_norm_pow_mul_le_one`), and the maps `ℓ⁻ᵏ φ` are injective. -/
noncomputable def isColimitPadicIntegersRingObjToSubfieldSmulSequenceCocone :
    IsColimit (Mod.smulSequenceCocone ℓ
      (padicIntegersRingObjToSubfieldRingObjInvPow.{u} ℓ E)
      (nsmul_padicIntegersRingObjToSubfieldRingObjInvPow_succ ℓ E)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  have hℓ := natCast_ne_zero_of_algebra ℓ E
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (sheafToPresheaf _ _) ?_
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨x⟩ := x
    have hι : Continuous (algebraMap E (PadicAlgCl ℓ)) :=
      (AddMonoidHomClass.isometry_of_norm (algebraMap E (PadicAlgCl ℓ)) fun _ ↦ rfl).continuous
    obtain ⟨m, hm⟩ := PadicAlgCl.exists_norm_pow_mul_le_one
      ((⟨algebraMap E (PadicAlgCl ℓ), hι⟩ : C(E, PadicAlgCl ℓ)).comp x)
    have hmem (s : S.unop) : (ℓ : E) ^ m * x s ∈ PadicAlgCl.integers ℓ E := by
      rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, map_mul, map_pow,
        map_natCast]
      exact hm s
    refine ⟨m, ULift.up ⟨fun s ↦ ⟨_, hmem s⟩, (continuous_const.mul x.continuous).subtype_mk _⟩,
      ULift.ext (ContinuousMap.ext fun s ↦ ?_)⟩
    have key : (ℓ : E)⁻¹ ^ m * ((ℓ : E) ^ m * x s) = x s := by
      rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hℓ, one_pow, _root_.one_mul]
    exact key.symm
  · intro k x y h
    refine ⟨k, 𝟙 k, ?_⟩
    rw [CategoryTheory.Functor.map_id]
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    have hk : (ℓ : E)⁻¹ ^ k ≠ 0 := pow_ne_zero _ (inv_ne_zero hℓ)
    have h' (s : S.unop) :
        (ℓ : E)⁻¹ ^ k * (x s : E) = (ℓ : E)⁻¹ ^ k * (y s : E) :=
      congrArg (fun z : ULift.{u + 1} C(S.unop, E) ↦ z.down s) h
    obtain rfl : x = y := ContinuousMap.ext fun s ↦ Subtype.ext (mul_left_cancel₀ hk (h' s))
    rfl

end Profinite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The inclusion `𝒪_{E,X} ⟶ E_X` of coefficient ring objects on `X_proét`, for a field `E` with
an embedding `E → ℚ̄_ℓ`: the pullback along `p_X` of the inclusion `𝒪̲_E ⟶ E̲`. -/
noncomputable abbrev padicIntegersToSubfieldRingObj :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj E) X :=
  (upperStarFromPoint X).map (Profinite.padicIntegersRingObjToSubfieldRingObj ℓ E)

/-- **Flatness of `E_X` over `𝒪_{E,X}`**: the extension of scalars along the inclusion
`𝒪_{E,X} ⟶ E_X` is exact, `E_X` being the sequential colimit of the multiplications by `ℓ` on
`𝒪_{E,X}`. -/
instance preservesFiniteLimits_extendScalars_padicIntegersToSubfieldRingObj :
    PreservesFiniteLimits (Mod.extendScalars (padicIntegersToSubfieldRingObj X ℓ E)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  have := AB5OfSize_of_univLE.{0, 0} (Sheaf (ProEt.topology X) Ab.{u + 1})
  exact Mod.preservesFiniteLimits_extendScalars_of_isColimit _
    (Mod.isColimitSmulSequenceCoconeMap (upperStarFromPoint X) _
      (Profinite.isColimitPadicIntegersRingObjToSubfieldSmulSequenceCocone ℓ E))
    (by rw [Profinite.padicIntegersRingObjToSubfieldRingObjInvPow_zero])

end AlgebraicGeometry.ProEtale
