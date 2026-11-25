/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import WeilConjectures.NumberTheory.Padics.IntegersNoetherian

/-!
# Rings of integers in a finite extension of `ℓ`-adic fields

Let `E ⊆ E'` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`. The inclusion `E ⟶ E'` restricts to
a ring map `𝒪_E ⟶ 𝒪_{E'}` between the rings of integers, which makes `𝒪_{E'}` a finite free
`𝒪_E`-module. This is what makes the extension of scalars `𝒪_E ⟶ 𝒪_{E'}` between the integral
coefficient stages of the `ℓ`-adic formalism well behaved.

## Main definitions

- `PadicAlgCl.integersMap l E E'`: the ring map `𝒪_E ⟶ 𝒪_{E'}`.

## Main results

- `PadicAlgCl.finite_integersMap`: `𝒪_{E'}` is a finite `𝒪_E`-module. The coordinates in an
  `E`-basis of `E'` are continuous, hence bounded on the unit ball `𝒪_{E'}`, so for some `N` the
  map `x ↦ (ℓ^N c_i(x))_i` embeds `𝒪_{E'}` into `𝒪_E^n`, and `𝒪_E` is Noetherian.
-/

@[expose] public section

universe w u

open NNReal

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E E' : Type w) [Field E] [Field E'] [Algebra E (PadicAlgCl l)]
  [Algebra E' (PadicAlgCl l)] [Algebra E E'] [IsScalarTower E E' (PadicAlgCl l)]

lemma norm_algebraMap_algebraMap (x : E) :
    ‖algebraMap E' (PadicAlgCl l) (algebraMap E E' x)‖ = ‖algebraMap E (PadicAlgCl l) x‖ := by
  rw [← IsScalarTower.algebraMap_apply]

/-- The ring map `𝒪_E ⟶ 𝒪_{E'}` between the rings of integers of fields `E ⊆ E'` inside
`ℚ̄_ℓ`, the restriction of the inclusion `E ⟶ E'`. -/
noncomputable def integersMap : integers l E →+* integers l E' where
  toFun x := ⟨algebraMap E E' x, by
    rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, norm_algebraMap_algebraMap,
      ← coe_nnnorm, NNReal.coe_le_coe]
    exact x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

@[simp]
lemma coe_integersMap (x : integers l E) : (integersMap l E E' x : E') = algebraMap E E' x :=
  rfl

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E']

omit [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E'] in
include l in
/-- The inclusion `E ⟶ E'` of extensions of `ℚ_ℓ` inside `ℚ̄_ℓ` is `ℚ_ℓ`-linear. -/
lemma isScalarTower_of_algebra : IsScalarTower ℚ_[l] E E' :=
  IsScalarTower.of_algebraMap_eq fun x ↦ (algebraMap E' (PadicAlgCl l)).injective (by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply E E' (PadicAlgCl l),
      ← IsScalarTower.algebraMap_apply])

/-- **`𝒪_{E'}` is a finite `𝒪_E`-module.** The coordinates in an `E`-basis of `E'` are continuous
linear maps, hence bounded on `𝒪_{E'}`; multiplying them by a power `ℓ^N` embeds `𝒪_{E'}` into
`𝒪_E^n`, a Noetherian `𝒪_E`-module. -/
theorem finite_integersMap :
    letI := (integersMap l E E').toAlgebra
    Module.Finite (integers l E) (integers l E') := by
  let := (integersMap l E E').toAlgebra
  have := isScalarTower_of_algebra l E E'
  have : FiniteDimensional E E' := Module.Finite.right ℚ_[l] E E'
  let nE : NormedField E := normedFieldOfAlgebra l E
  let nE' : NormedField E' := normedFieldOfAlgebra l E'
  have hnorm (x : E) : ‖x‖ = ‖algebraMap E (PadicAlgCl l) x‖ := rfl
  have hnorm' (x : E') : ‖x‖ = ‖algebraMap E' (PadicAlgCl l) x‖ := rfl
  have hl0 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  -- `ℓ` has norm `ℓ⁻¹` in `E`
  have hl : ‖algebraMap ℚ_[l] E l‖ = (l : ℝ)⁻¹ := by
    rw [hnorm, ← IsScalarTower.algebraMap_apply]
    change ‖((l : ℚ_[l]) : PadicAlgCl l)‖ = _
    rw [PadicAlgCl.norm_extends, Padic.norm_p]
  let : NontriviallyNormedField E := .ofNormNeOne ⟨algebraMap ℚ_[l] E l,
    (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero),
    by rw [hl]; exact (inv_lt_one_of_one_lt₀ hl0).ne⟩
  let : NormedSpace E E' :=
    { norm_smul_le a x := by
        rw [hnorm', hnorm, hnorm', Algebra.smul_def, map_mul, norm_mul,
          norm_algebraMap_algebraMap] }
  have : CompleteSpace E := completeSpace_ofAlgebra l E
  let b := Module.finBasis E E'
  -- the coordinates are bounded
  let C : ℝ := 1 + ∑ i, ‖LinearMap.toContinuousLinearMap (b.coord i)‖
  have hC (i : Fin (Module.finrank E E')) (x : E') : ‖b.coord i x‖ ≤ C * ‖x‖ := by
    have h₁ := (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm x
    have h₂ : ‖LinearMap.toContinuousLinearMap (b.coord i)‖ ≤ C := by
      have := Finset.single_le_sum (f := fun i ↦ ‖LinearMap.toContinuousLinearMap (b.coord i)‖)
        (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
      simp only [C]
      linarith
    calc ‖b.coord i x‖ = ‖LinearMap.toContinuousLinearMap (b.coord i) x‖ := rfl
      _ ≤ _ := h₁
      _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right h₂ (norm_nonneg _)
  have hCpos : 0 < C := by positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((l : ℝ)⁻¹) ^ N < C⁻¹ :=
    exists_pow_lt_of_lt_one (inv_pos.2 hCpos) (inv_lt_one_of_one_lt₀ hl0)
  let c : E := algebraMap ℚ_[l] E l ^ N
  have hc : ‖c‖ = ((l : ℝ)⁻¹) ^ N := by rw [norm_pow, hl]
  have hmem (i : Fin (Module.finrank E E')) (x : integers l E') :
      c * b.coord i x ∈ integers l E := by
    rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, ← hnorm, norm_mul, hc]
    have hx : ‖(x : E')‖ ≤ 1 := by
      rw [hnorm', ← coe_nnnorm, ← NNReal.coe_one, NNReal.coe_le_coe]
      exact x.2
    calc ((l : ℝ)⁻¹) ^ N * ‖b.coord i x‖ ≤ C⁻¹ * (C * ‖(x : E')‖) :=
          mul_le_mul hN.le (hC i x) (norm_nonneg _) (inv_pos.2 hCpos).le
      _ = ‖(x : E')‖ := by field_simp
      _ ≤ 1 := hx
  -- the embedding of `𝒪_{E'}` into `𝒪_E^n`
  let T : integers l E' →ₗ[integers l E] (Fin (Module.finrank E E') → integers l E) :=
    { toFun x i := ⟨c * b.coord i x, hmem i x⟩
      map_add' x y := by
        ext i
        simp [mul_add]
      map_smul' a x := by
        ext i
        change c * b.coord i (algebraMap E E' a * x) = (a : E) * (c * b.coord i x)
        rw [← Algebra.smul_def, map_smul, smul_eq_mul]
        ring }
  have hT : Function.Injective T := by
    intro x y hxy
    apply Subtype.ext
    apply b.ext_elem
    intro i
    have := congrArg (fun z ↦ (z i : E)) hxy
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk] at this
    have hc0 : c ≠ 0 := pow_ne_zero _
      ((map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
    simpa [Module.Basis.coord_apply] using mul_left_cancel₀ hc0 this
  have := isNoetherian_of_injective T hT
  infer_instance

section Shrink

variable [Small.{u + 1} E] [Small.{u + 1} E']

/-- The ring map `Shrink 𝒪_E ⟶ Shrink 𝒪_{E'}` between the universe `u + 1` copies of the rings
of integers, the coefficient rings of the integral stages of the `ℓ`-adic formalism. -/
noncomputable def integersShrinkMap :
    Shrink.{u + 1} (integers l E) →+* Shrink.{u + 1} (integers l E') :=
  (shrinkRingEquiv l E').toRingHom.comp
    ((integersMap l E E').comp (shrinkRingEquiv l E).symm.toRingHom)

/-- `Shrink 𝒪_{E'}` is a finite `Shrink 𝒪_E`-module. -/
theorem finite_integersShrinkMap :
    letI := (integersShrinkMap.{w, u} l E E').toAlgebra
    Module.Finite (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (integers l E')) := by
  let := (integersMap l E E').toAlgebra
  let := (integersShrinkMap.{w, u} l E E').toAlgebra
  have := finite_integersMap l E E'
  refine Module.Finite.of_equiv_equiv (shrinkRingEquiv l E) (shrinkRingEquiv l E') ?_
  ext x
  simp [integersShrinkMap, RingHom.algebraMap_toAlgebra]

/-- `Shrink 𝒪_{E'}` is a free `Shrink 𝒪_E`-module, being finite and torsion free over the
principal ideal domain `Shrink 𝒪_E`. -/
theorem free_integersShrinkMap :
    letI := (integersShrinkMap.{w, u} l E E').toAlgebra
    Module.Free (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (integers l E')) := by
  let := (integersShrinkMap.{w, u} l E E').toAlgebra
  have := finite_integersShrinkMap.{w, u} l E E'
  have : IsDomain (Shrink.{u + 1} (integers l E)) :=
    (shrinkRingEquiv.{w, u} l E).symm.toMulEquiv.isDomain _
  have : IsDomain (Shrink.{u + 1} (integers l E')) :=
    (shrinkRingEquiv.{w, u} l E').symm.toMulEquiv.isDomain _
  have : IsPrincipalIdealRing (Shrink.{u + 1} (integers l E)) :=
    IsPrincipalIdealRing.of_surjective (shrinkRingEquiv l E).toRingHom
      (shrinkRingEquiv l E).surjective
  have : Module.IsTorsionFree (Shrink.{u + 1} (integers l E))
      (Shrink.{u + 1} (integers l E')) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, RingHom.algebraMap_toAlgebra]
    intro x y h
    apply (shrinkRingEquiv l E).symm.injective
    apply Subtype.ext
    apply (algebraMap E E').injective
    have := congrArg (fun z ↦ (((shrinkRingEquiv l E').symm z : integers l E') : E')) h
    simpa [integersShrinkMap] using this
  exact Module.free_of_finite_type_torsion_free'

end Shrink

end PadicAlgCl
