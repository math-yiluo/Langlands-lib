/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.Extension

/-!
# The ring of integers `𝒪_E` as a subring of `ℚ̄_ℓ`

Let `E` be a subfield of `ℚ̄_ℓ = PadicAlgCl ℓ` with ring of integers
`𝒪_E = PadicAlgCl.integers ℓ E`, topologised as a subspace of `E` with the norm restricted from
`ℚ̄_ℓ` (`PadicAlgCl.normedFieldOfAlgebra`). This file provides:

- the `𝒪_E`-algebra structure of `ℚ̄_ℓ` (`PadicAlgCl.integersAlgebra`), which is faithful, with
  continuous structure map (`PadicAlgCl.continuous_algebraMap_integers`) taking values in `E`;
- the inclusion `κ : ℤ_ℓ → 𝒪_E` (`PadicAlgCl.integersPadicIntHom`) for `E` over `ℚ_ℓ`, continuous
  and compatible with `ℤ_ℓ ⊆ ℚ_ℓ ⊆ ℚ̄_ℓ` (`PadicAlgCl.algebraMap_integersPadicIntHom`);
- `𝒪_E` is a topological ring (`PadicAlgCl.isTopologicalRing_integers`), compact for `E` finite
  over `ℚ_ℓ` (`PadicAlgCl.compactSpace_integers`).

These are the coefficient hypotheses of
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_bijective_tensorSections` for `R = 𝒪_E`.
-/

@[expose] public section

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]

/-- `ℚ̄_ℓ` is an algebra over the ring of integers `𝒪_E` of a subfield `E ⊆ ℚ̄_ℓ`, through
`𝒪_E ⊆ E ⊆ ℚ̄_ℓ`. -/
noncomputable instance integersAlgebra : Algebra (integers l E) (PadicAlgCl l) :=
  ((algebraMap E (PadicAlgCl l)).comp (integers l E).subtype).toAlgebra

lemma algebraMap_integers_apply (x : integers l E) :
    algebraMap (integers l E) (PadicAlgCl l) x = algebraMap E (PadicAlgCl l) (x : E) :=
  rfl

instance faithfulSMul_integers : FaithfulSMul (integers l E) (PadicAlgCl l) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2
    ((algebraMap E (PadicAlgCl l)).injective.comp Subtype.val_injective)

lemma algebraMap_integers_mem (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (x : integers l E) :
    algebraMap (integers l E) (PadicAlgCl l) x ∈ E :=
  (x : E).2

/-- The structure map `𝒪_E → ℚ̄_ℓ` is continuous. -/
lemma continuous_algebraMap_integers :
    letI := normedFieldOfAlgebra l E
    Continuous (algebraMap (integers l E) (PadicAlgCl l)) :=
  letI := normedFieldOfAlgebra l E
  (continuous_induced_dom (f := algebraMap E (PadicAlgCl l))).comp continuous_subtype_val

/-- `𝒪_E` is a topological ring, as a subring of `E`. -/
lemma isTopologicalRing_integers :
    letI := normedFieldOfAlgebra l E
    IsTopologicalRing (integers l E) :=
  letI := normedFieldOfAlgebra l E
  inferInstanceAs (IsTopologicalRing (integers l E).toSubring)

/-- The algebra map `ℚ_ℓ → ℚ̄_ℓ` is continuous, being an isometry. -/
lemma continuous_algebraMap_padic :
    Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) :=
  (AddMonoidHomClass.isometry_iff_norm (algebraMap ℚ_[l] (PadicAlgCl l))).2
    (PadicAlgCl.norm_extends l) |>.continuous

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]

/-- The inclusion `κ : ℤ_ℓ → 𝒪_E` of the `ℓ`-adic integers in the ring of integers of an extension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable def integersPadicIntHom : ℤ_[l] →+* integers l E :=
  ((algebraMap ℚ_[l] E).comp PadicInt.Coe.ringHom).codRestrict (integers l E) fun z ↦ by
    change ‖algebraMap E (PadicAlgCl l) (algebraMap ℚ_[l] E z)‖₊ ≤ 1
    rw [← IsScalarTower.algebraMap_apply, ← NNReal.coe_le_coe, coe_nnnorm,
      PadicAlgCl.norm_extends]
    exact z.2

lemma algebraMap_integersPadicIntHom (z : ℤ_[l]) :
    algebraMap (integers l E) (PadicAlgCl l) (integersPadicIntHom l E z) =
      algebraMap ℚ_[l] (PadicAlgCl l) (PadicInt.Coe.ringHom z) :=
  (IsScalarTower.algebraMap_apply ℚ_[l] E (PadicAlgCl l) _).symm

/-- The inclusion `ℤ_ℓ → 𝒪_E` is continuous. -/
lemma continuous_integersPadicIntHom :
    letI := normedFieldOfAlgebra l E
    Continuous (integersPadicIntHom l E) := by
  let := normedFieldOfAlgebra l E
  refine Continuous.subtype_mk (continuous_induced_rng.2 ?_) _
  have : (algebraMap E (PadicAlgCl l)) ∘ (fun z : ℤ_[l] ↦ algebraMap ℚ_[l] E (z : ℚ_[l])) =
      (algebraMap ℚ_[l] (PadicAlgCl l)) ∘ (fun z : ℤ_[l] ↦ (z : ℚ_[l])) :=
    funext fun z ↦ (IsScalarTower.algebraMap_apply ℚ_[l] E (PadicAlgCl l) _).symm
  exact this ▸ (continuous_algebraMap_padic l).comp continuous_subtype_val

end PadicAlgCl

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]

/-- The ring of integers of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` is compact: it is the closed
unit ball of the finite-dimensional normed `ℚ_ℓ`-space `E`. -/
lemma compactSpace_integers [FiniteDimensional ℚ_[l] E] :
    letI := normedFieldOfAlgebra l E
    CompactSpace (integers l E) := by
  let := normedFieldOfAlgebra l E
  let : NormedSpace ℚ_[l] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl l) (c • x)‖ ≤ ‖c‖ * ‖algebraMap E (PadicAlgCl l) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  have : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
  have h : (integers l E : Set E) = Metric.closedBall 0 1 := by
    ext x
    rw [SetLike.mem_coe, mem_integers_iff, mem_closedBall_zero_iff, ← NNReal.coe_le_coe,
      coe_nnnorm]
    rfl
  exact isCompact_iff_compactSpace.1 (h ▸ isCompact_closedBall (0 : E) 1)

end PadicAlgCl
