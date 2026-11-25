/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.Analysis.Normed.Field.Krasner
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!

# Extensions of `ℚ_ℓ` inside `ℚ̄_ℓ` and their rings of integers

Let `E` be a field with an embedding `E → ℚ̄_ℓ = PadicAlgCl l`. This file restricts the
`ℓ`-adic norm and valuation of `ℚ̄_ℓ` to `E`, defines the ring of integers `𝒪_E` as the
valuation subring of the restricted valuation, and shows that `𝒪_E` is `𝔪_E`-adically
complete when `E` is a finite extension of `ℚ_ℓ`.

The valuation and topology of `E` are not separate data but are restricted from `ℚ̄_ℓ` along
the embedding. These structures are definitions rather than instances, since `ℓ` cannot be
recovered from `E`. The structure is phrased with `Valued`, pending the move of this part of
mathlib to `ValuativeRel`.

The ring of integers only uses the embedding `E → ℚ̄_ℓ`. The `ℚ_ℓ`-algebra structure, the
scalar tower and finiteness `[FiniteDimensional ℚ_[l] E]` are used for the completeness of
`𝒪_E` (`PadicAlgCl.isAdicComplete_integers`): through them the restricted valuation extends
the `ℓ`-adic one, and `E` becomes a nonarchimedean local field.

## Main definitions

- `PadicAlgCl.normedFieldOfAlgebra`, `PadicAlgCl.valuationOfAlgebra` and
  `PadicAlgCl.valuedOfAlgebra` : the norm, valuation and valued field structure of `E`,
  restricted from `ℚ̄_ℓ`.
- `PadicAlgCl.integers` : the ring of integers `𝒪_E`.
- `PadicAlgCl.shrinkRingEquiv` and `PadicAlgCl.maximalIdealShrink` : the identification of
  `𝒪_E` with its copy `Shrink.{u + 1} 𝒪_E`, and the maximal ideal `𝔪_E` read in that copy.

## Main results

- `PadicAlgCl.exists_isAlgebraic_mem_adjoin_simple` : every element of `ℚ̄_ℓ` lies in
  `ℚ_ℓ(b)` for some `b` algebraic over `ℚ`, so countably many finite extensions of `ℚ_ℓ` cover
  `ℚ̄_ℓ`.
- `PadicAlgCl.isClosed_intermediateField` : a finite extension of `ℚ_ℓ` is closed in `ℚ̄_ℓ`.
- `PadicAlgCl.completeSpace_ofAlgebra` : a finite extension of `ℚ_ℓ` is complete for the
  restricted norm.
- `PadicAlgCl.isAdicComplete_integers` and `PadicAlgCl.isAdicComplete_maximalIdealShrink` :
  if `E` is finite over `ℚ_ℓ`, then `𝒪_E` and its copy `Shrink 𝒪_E` are `𝔪_E`-adically
  complete.
- `PadicAlgCl.isPrincipal_maximalIdeal_integers` and `PadicAlgCl.isPrincipal_maximalIdealShrink` :
  if `E` is finite over `ℚ_ℓ`, then `𝔪_E` is principal, in `𝒪_E` and in its copy `Shrink 𝒪_E`.

-/

@[expose] public section

universe w u

open NNReal

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime]

open Polynomial IntermediateField in
/-- Every element `x` of `ℚ̄_ℓ` lies in `ℚ_ℓ(b)` for some `b` algebraic over `ℚ`.

By the continuity of roots, a monic polynomial over `ℚ` whose coefficients are close enough to
those of the minimal polynomial of `x` over `ℚ_ℓ` has a root `b` closer to `x` than any other
conjugate of `x`, and then `x ∈ ℚ_ℓ(b)` by Krasner's lemma. Since `ℚ̄` is countable, this
covers `ℚ̄_ℓ` by countably many finite extensions of `ℚ_ℓ`. -/
theorem exists_isAlgebraic_mem_adjoin_simple (x : PadicAlgCl l) :
    ∃ b : PadicAlgCl l, IsAlgebraic ℚ b ∧ x ∈ ℚ_[l]⟮b⟯ := by
  classical
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  set f := minpoly ℚ_[l] x
  have fmon : f.Monic := minpoly.monic hx
  have fa0 : f.aeval x = 0 := minpoly.aeval _ _
  have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hx).ne'
  -- `δ` is a lower bound for the distance from `x` to its other conjugates
  let S : Finset (PadicAlgCl l) := {y ∈ (f.rootSet (PadicAlgCl l)).toFinset | y ≠ x}
  let δ : ℝ := if hS : S.Nonempty then Finset.min' (S.image fun y ↦ ‖x - y‖)
      (Finset.image_nonempty.mpr hS) else 1
  have norm_sub_le : ∀ y : PadicAlgCl l, IsConjRoot ℚ_[l] x y → x ≠ y → δ ≤ ‖x - y‖ := by
    intro y conj ne
    have hyS : y ∈ S := by
      simp only [Finset.mem_filter, Set.mem_toFinset, S]
      exact ⟨(isConjRoot_iff_mem_minpoly_rootSet hx).mp conj, ne.symm⟩
    have hS : S.Nonempty := ⟨y, hyS⟩
    simp only [hS, ↓reduceDIte, δ]
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hyS)
  have δpos : 0 < δ := by
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · simp only [Finset.lt_min'_iff, Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro y hy
      simp only [Finset.mem_filter, Set.mem_toFinset, S] at hy
      rw [norm_pos_iff, sub_ne_zero]
      exact hy.2.symm
    · exact one_pos
  -- approximate `f` by a monic polynomial `g` over `ℚ` and pick a root `b` of `g` near `x`
  have hε : 0 < (δ / (max ‖x‖ 1)) ^ f.natDegree / (f.natDegree + 1) := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
      (Padic.denseRange_ratCast l) fmon hε
  obtain ⟨b, hb, hxb⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff
      (IsAlgClosed.splits _)
  have hxb : ‖x - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hxb
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖x‖ 1) > 0).ne'] using hxb
    · simp [fnatdeg0]
    · positivity
  rw [mem_aroots] at hb
  refine ⟨b, ⟨g, gmon.ne_zero, by simpa [aeval_map_algebraMap] using hb.2⟩, ?_⟩
  exact IsKrasner.krasner (minpoly.irreducible hx).separable (IsAlgClosed.splits _)
    (Algebra.IsIntegral.isIntegral b) fun y h1 h2 ↦ hxb.trans_le (norm_sub_le y h1 h2)

/-- A finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` is closed, being a finite-dimensional subspace
over the complete field `ℚ_ℓ`. -/
theorem isClosed_intermediateField (E : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] E] : IsClosed (E : Set (PadicAlgCl l)) :=
  Submodule.closed_of_finiteDimensional E.toSubalgebra.toSubmodule

variable (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]

/-- The normed field structure on a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`, restricted from
the `ℓ`-adic norm of `PadicAlgCl l` along the embedding `E → PadicAlgCl l`. Its topology is
the subspace topology of `E` in `PadicAlgCl l`. -/
@[reducible]
noncomputable def normedFieldOfAlgebra : NormedField E :=
  NormedField.induced E (PadicAlgCl l) (algebraMap E (PadicAlgCl l))
    (algebraMap E (PadicAlgCl l)).injective

/-- The `ℓ`-adic valuation on a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`, restricted from the
valuation of `PadicAlgCl l` along the embedding `E → PadicAlgCl l`. -/
noncomputable def valuationOfAlgebra : Valuation E ℝ≥0 :=
  (Valued.v : Valuation (PadicAlgCl l) ℝ≥0).comap (algebraMap E (PadicAlgCl l))

variable {l E} in
lemma valuationOfAlgebra_apply (x : E) :
    valuationOfAlgebra l E x = ‖algebraMap E (PadicAlgCl l) x‖₊ := rfl

lemma isUltrametricDist_ofAlgebra :
    letI := normedFieldOfAlgebra l E
    IsUltrametricDist E := by
  let := normedFieldOfAlgebra l E
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y ↦ by
    have := PadicAlgCl.isNonarchimedean l (algebraMap E (PadicAlgCl l) x)
      (algebraMap E (PadicAlgCl l) y)
    rwa [← map_add] at this

/-- The valued field structure on a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`, restricted from
`PadicAlgCl l`: its valuation is `PadicAlgCl.valuationOfAlgebra` and its uniformity that of
`PadicAlgCl.normedFieldOfAlgebra`.

It is not an instance, since `ℓ` cannot be recovered from `E`. -/
@[reducible]
noncomputable def valuedOfAlgebra : Valued E ℝ≥0 :=
  letI := normedFieldOfAlgebra l E
  haveI := isUltrametricDist_ofAlgebra l E
  NormedField.toValued

lemma valuedOfAlgebra_v : (valuedOfAlgebra l E).v = valuationOfAlgebra l E := rfl


/-- The ring of integers `𝒪_E` of a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`: the valuation
subring of the valuation `PadicAlgCl.valuationOfAlgebra` restricted from `PadicAlgCl l`. -/
noncomputable def integers : ValuationSubring E :=
  (valuationOfAlgebra l E).valuationSubring

lemma mem_integers_iff (x : E) :
    x ∈ integers l E ↔ ‖algebraMap E (PadicAlgCl l) x‖₊ ≤ 1 := Iff.rfl

/-- The identification of the ring of integers `𝒪_E` with its copy `Shrink 𝒪_E` in the
universe `u + 1`, where the coefficient ring of a sheaf on a `u`-site has to live. -/
noncomputable def shrinkRingEquiv [Small.{u + 1} E] :
    integers l E ≃+* Shrink.{u + 1} (integers l E) :=
  (Shrink.ringEquiv (integers l E)).symm

/-- The maximal ideal `𝔪_E` of the ring of integers `𝒪_E`, read inside the universe `u + 1`
copy `Shrink 𝒪_E` along `PadicAlgCl.shrinkRingEquiv`. This is the ideal with respect to which
the objects of `D(J, 𝒪_E)` are asked to be derived complete. -/
noncomputable def maximalIdealShrink [Small.{u + 1} E] : Ideal (Shrink.{u + 1} (integers l E)) :=
  (IsLocalRing.maximalIdeal (integers l E)).map (shrinkRingEquiv l E)

section Complete

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]

lemma valuationOfAlgebra_algebraMap (x : ℚ_[l]) :
    valuationOfAlgebra l E (algebraMap ℚ_[l] E x) = ‖x‖₊ := by
  rw [valuationOfAlgebra_apply, ← IsScalarTower.algebraMap_apply]
  exact NNReal.eq (PadicAlgCl.norm_extends l x)

/-- A finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` is complete for the norm restricted from
`ℚ̄_ℓ`, being a finite-dimensional normed space over the complete field `ℚ_ℓ`. -/
theorem completeSpace_ofAlgebra [FiniteDimensional ℚ_[l] E] :
    letI := normedFieldOfAlgebra l E
    CompleteSpace E := by
  let := normedFieldOfAlgebra l E
  let : NormedSpace ℚ_[l] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl l) (c • x)‖ ≤ ‖c‖ * ‖algebraMap E (PadicAlgCl l) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact FiniteDimensional.complete ℚ_[l] E

open ValuativeRel in
/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, then `E`, with the valuative relation
and the topology restricted from `PadicAlgCl l`, is a nonarchimedean local field (it is locally
compact, being a finite-dimensional normed space over `ℚ_ℓ`), whose ring of integers `𝒪[E]` is
`PadicAlgCl.integers l E`. This is how mathlib's results on local fields are transported to
`PadicAlgCl.integers l E`. -/
theorem isNonarchimedeanLocalField_and_integer_eq [FiniteDimensional ℚ_[l] E] :
    letI := normedFieldOfAlgebra l E
    letI : ValuativeRel E := .ofValuation (valuationOfAlgebra l E)
    IsNonarchimedeanLocalField E ∧ 𝒪[E] = (integers l E).toSubring := by
  let w := valuationOfAlgebra l E
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  let : ValuativeRel E := .ofValuation w
  have : w.Compatible := .ofValuation w
  let : NormedSpace ℚ_[l] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl l) (c • x)‖ ≤ ‖c‖ * ‖algebraMap E (PadicAlgCl l) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  have : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
  have : w.IsNontrivial := ⟨algebraMap ℚ_[l] E l, by
    rw [valuationOfAlgebra_algebraMap]
    refine ⟨by simp [(Fact.out : l.Prime).ne_zero], fun h ↦ ?_⟩
    have := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) h
    simp [Padic.norm_p, (Fact.out : l.Prime).one_lt.ne'] at this⟩
  have : IsNontrivial E := (isNontrivial_iff_isNontrivial w).mpr inferInstance
  have : IsValuativeTopology E := by
    refine IsValuativeTopology.of_mem_nhds_zero_iff_vle w fun {s} ↦ ?_
    have hnorm (z : E) : ‖z‖ = (w z : ℝ) := rfl
    rw [Metric.mem_nhds_iff]
    constructor
    · rintro ⟨ε, hε, hs⟩
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ((l : ℝ)⁻¹) ^ n < ε :=
        exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
      let x : E := algebraMap ℚ_[l] E ((l : ℚ_[l]) ^ n)
      have hx : (w x : ℝ) = ((l : ℝ)⁻¹) ^ n := by
        simp only [w, x]
        rw [valuationOfAlgebra_algebraMap]
        simp [Padic.norm_p]
      have hx0 : w.restrict x ≠ 0 :=
        ((Valuation.restrict_pos_iff w x).mpr (NNReal.coe_pos.mp (hx ▸ by positivity))).ne'
      refine ⟨Units.mk0 _ hx0, fun z hz ↦ hs ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
      rw [mem_ball_zero_iff, hnorm]
      exact (NNReal.coe_lt_coe.mpr hz).trans_eq hx |>.trans hn
    · rintro ⟨γ, hγ⟩
      refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding (f := MonoidWithZeroHom.ofClass w) γ.val,
        ?_, fun z hz ↦ hγ ?_⟩
      · exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr γ.ne_zero))
      rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, ← NNReal.coe_lt_coe,
        ← hnorm]
      simpa using hz
  refine ⟨{}, ?_⟩
  ext x
  exact (isEquiv (valuation E) w).le_one_iff_le_one

open ValuativeRel in
/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, its ring of integers is
`𝔪_E`-adically complete: this is mathlib's `IsAdicComplete 𝓂[E] 𝒪[E]`, transported along
`PadicAlgCl.isNonarchimedeanLocalField_and_integer_eq`. -/
instance isAdicComplete_integers [FiniteDimensional ℚ_[l] E] :
    IsAdicComplete (IsLocalRing.maximalIdeal (integers l E)) (integers l E) := by
  let := normedFieldOfAlgebra l E
  let : ValuativeRel E := .ofValuation (valuationOfAlgebra l E)
  obtain ⟨_, heq⟩ := isNonarchimedeanLocalField_and_integer_eq l E
  let e : 𝒪[E] ≃+* integers l E := RingEquiv.subringCongr heq
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
  exact (IsAdicComplete.congr_ringEquiv _ e).mpr inferInstance

open ValuativeRel in
/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, its ring of integers is a principal
ideal ring, being a discrete valuation ring. -/
instance isPrincipalIdealRing_integers [FiniteDimensional ℚ_[l] E] :
    IsPrincipalIdealRing (integers l E) := by
  let := normedFieldOfAlgebra l E
  let : ValuativeRel E := .ofValuation (valuationOfAlgebra l E)
  obtain ⟨_, heq⟩ := isNonarchimedeanLocalField_and_integer_eq l E
  exact IsPrincipalIdealRing.of_surjective (RingEquiv.subringCongr heq).toRingHom
    (RingEquiv.subringCongr heq).surjective

open ValuativeRel in
/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, the residue field of its ring of
integers is finite. -/
instance finite_residueField_integers [FiniteDimensional ℚ_[l] E] :
    Finite (IsLocalRing.ResidueField (integers l E)) := by
  let := normedFieldOfAlgebra l E
  let : ValuativeRel E := .ofValuation (valuationOfAlgebra l E)
  obtain ⟨_, heq⟩ := isNonarchimedeanLocalField_and_integer_eq l E
  let e : 𝒪[E] ≃+* integers l E := RingEquiv.subringCongr heq
  exact .of_equiv _ (IsLocalRing.ResidueField.mapEquiv e).toEquiv

/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, the quotients `𝒪_E / 𝔪_Eⁿ` of its
ring of integers are finite. -/
instance finite_quotient_maximalIdeal_pow [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Finite (integers l E ⧸ IsLocalRing.maximalIdeal (integers l E) ^ n) :=
  have : Finite (integers l E ⧸ IsLocalRing.maximalIdeal (integers l E)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (integers l E)))
  Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, the maximal ideal `𝔪_E` of its ring
of integers is principal, generated by a uniformizer. -/
lemma isPrincipal_maximalIdeal_integers [FiniteDimensional ℚ_[l] E] :
    (IsLocalRing.maximalIdeal (integers l E)).IsPrincipal :=
  IsPrincipalIdealRing.principal _

/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, the universe `u + 1` copy of its ring
of integers is `𝔪_E`-adically complete. Through `Ideal.isLimitQuotPowCone` this says that
the coefficient ring is the limit of the tower `n ↦ 𝒪_E / 𝔪_Eⁿ` of its reductions. -/
instance isAdicComplete_maximalIdealShrink [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E] :
    IsAdicComplete (maximalIdealShrink l E) (Shrink.{u + 1} (integers l E)) :=
  (IsAdicComplete.congr_ringEquiv _ (shrinkRingEquiv l E)).mpr inferInstance

/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, the maximal ideal `𝔪_E`, read in the
universe `u + 1` copy `Shrink 𝒪_E`, is principal. -/
lemma isPrincipal_maximalIdealShrink [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E] :
    (maximalIdealShrink l E).IsPrincipal := by
  obtain ⟨ϖ, hϖ⟩ := isPrincipal_maximalIdeal_integers l E
  rw [maximalIdealShrink, hϖ, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]
  exact ⟨shrinkRingEquiv l E ϖ, rfl⟩

/-- The maximal ideal of the ring of integers of an extension of `ℚ_ℓ` inside `ℚ̄_ℓ` is nonzero:
it contains `ℓ`. -/
lemma maximalIdeal_integers_ne_bot : IsLocalRing.maximalIdeal (integers l E) ≠ ⊥ := by
  have hl : ‖(l : ℚ_[l])‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  let x : integers l E := ⟨algebraMap ℚ_[l] E l, by
    change valuationOfAlgebra l E _ ≤ 1
    rw [valuationOfAlgebra_algebraMap]
    exact hl.le⟩
  have hx : x ∈ IsLocalRing.maximalIdeal (integers l E) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨⟨_, y, h, -⟩, rfl⟩
    have hy : valuationOfAlgebra l E (y : E) ≤ 1 := y.2
    have h' : valuationOfAlgebra l E ((x : E) * (y : E)) = 1 := by
      simpa using congrArg (fun z : integers l E ↦ valuationOfAlgebra l E (z : E)) h
    rw [map_mul] at h'
    change valuationOfAlgebra l E (algebraMap ℚ_[l] E l) * _ = 1 at h'
    rw [valuationOfAlgebra_algebraMap] at h'
    have : ‖(l : ℚ_[l])‖₊ * valuationOfAlgebra l E (y : E) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' hy) hl
    exact this.ne h'
  intro h
  rw [h, Ideal.mem_bot] at hx
  have : (algebraMap ℚ_[l] E l) = 0 := congrArg Subtype.val hx
  rw [map_eq_zero_iff _ (algebraMap ℚ_[l] E).injective] at this
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)

/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, the maximal ideal `𝔪_E`, read in the
universe `u + 1` copy `Shrink 𝒪_E`, is generated by a nonzerodivisor (a uniformizer). -/
lemma exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span [FiniteDimensional ℚ_[l] E]
    [Small.{u + 1} E] :
    ∃ ϖ ∈ nonZeroDivisors (Shrink.{u + 1} (integers l E)),
      maximalIdealShrink l E = Ideal.span {ϖ} := by
  have := (shrinkRingEquiv.{w, u} l E).symm.injective.noZeroDivisors _ (map_zero _) (map_mul _)
  obtain ⟨ϖ, hϖ⟩ := isPrincipal_maximalIdealShrink.{w, u} l E
  refine ⟨ϖ, mem_nonZeroDivisors_of_ne_zero fun h ↦ maximalIdeal_integers_ne_bot l E ?_, ?_⟩
  · have hb : maximalIdealShrink.{w, u} l E = ⊥ := by
      rw [hϖ, h, Submodule.span_singleton_eq_bot.2 rfl]
    rw [maximalIdealShrink, Ideal.map_eq_bot_iff_of_injective (shrinkRingEquiv l E).injective]
      at hb
    exact hb
  · rw [hϖ]

end Complete

end PadicAlgCl
