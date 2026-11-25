/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.GradedAlgebra.PowersAlgebra

/-!
# The graded algebra `k[a₀ t, …, aₙ t]`

Let `K` be a commutative `k`-algebra and `a : ι → K` a family of elements. The graded algebra
`⊕ₙ Vⁿ tⁿ` attached to the span `V` of the `aᵢ` (see `Submodule.powersAlgebra`) is generated
by the linear forms `aᵢ t`; if `ι` is finite it is a standard graded `k`-algebra.

If `a i₀ = 1`, then `a i₀ t = t`, and the degree-zero part of the localization of `⊕ₙ Vⁿ tⁿ` at
`t` embeds into `K` by `c tⁿ / tⁿ ↦ c`; this sends `(aᵢ t) / t` to `aᵢ`. Geometrically, `K` is
the coordinate ring of an affine chart of a closed subscheme of projective space, and this
identifies it with the corresponding chart of `Proj (⊕ₙ Vⁿ tⁿ)`.

## Main definitions

- `Submodule.powersLinearForm k a i` — the linear form `aᵢ t` of `⊕ₙ Vⁿ tⁿ`.
- `Submodule.powersAwayEval a h` — for `a i₀ = 1`, the injective `k`-algebra map
  `(⊕ₙ Vⁿ tⁿ)_(t) → K`, `c tⁿ / tⁿ ↦ c`.

## Main statements

- `Submodule.adjoin_range_powersLinearForm` — the linear forms `aᵢ t` generate `⊕ₙ Vⁿ tⁿ`.
- `Submodule.powersAwayEval_injective` — the map `(⊕ₙ Vⁿ tⁿ)_(t) → K` is injective.
-/

@[expose] public section

open Polynomial HomogeneousLocalization

namespace Submodule

variable (k : Type*) {K ι : Type*} [Field k] [CommRing K] [Algebra k K] (a : ι → K)

lemma mem_span_range_pow_one (i : ι) : a i ∈ span k (Set.range a) ^ 1 := by
  rw [pow_one]
  exact subset_span ⟨i, rfl⟩

/-- The linear form `aᵢ t` of the graded algebra `⊕ₙ Vⁿ tⁿ`, where `V` is spanned by the
`aᵢ`. -/
noncomputable def powersLinearForm (i : ι) : (span k (Set.range a)).powersAlgebra :=
  powersMonomial (d := 1) (a i) (mem_span_range_pow_one k a i)

lemma powersLinearForm_mem (i : ι) :
    powersLinearForm k a i ∈ (span k (Set.range a)).powersGrading 1 :=
  powersMonomial_mem _ _

/-- The degree-one part of `⊕ₙ Vⁿ tⁿ` is spanned by the linear forms `aᵢ t`. -/
lemma powersGrading_one_le_span :
    (span k (Set.range a)).powersGrading 1 ≤ span k (Set.range (powersLinearForm k a)) := by
  intro F hF
  obtain ⟨c, hc, rfl⟩ := mem_powersGrading_iff_exists.mp hF
  have hc' : c ∈ span k (Set.range a) := by simpa using hc
  induction hc' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact subset_span ⟨i, rfl⟩
  | zero =>
    convert zero_mem (span k (Set.range (powersLinearForm k a)))
    exact Subtype.ext (by simp)
  | add x y hx hy ihx ihy =>
    have hx1 : x ∈ span k (Set.range a) ^ 1 := by simpa using hx
    have hy1 : y ∈ span k (Set.range a) ^ 1 := by simpa using hy
    convert add_mem (ihx hx1 (powersMonomial_mem _ _)) (ihy hy1 (powersMonomial_mem _ _))
    exact Subtype.ext (by simp)
  | smul r x hx ih =>
    have hx1 : x ∈ span k (Set.range a) ^ 1 := by simpa using hx
    convert smul_mem _ r (ih hx1 (powersMonomial_mem _ _))
    exact Subtype.ext (by
      rw [SetLike.val_smul, coe_powersMonomial, coe_powersMonomial, smul_monomial])

/-- The linear forms `aᵢ t` generate `⊕ₙ Vⁿ tⁿ` as a `k`-algebra. -/
lemma adjoin_range_powersLinearForm [Finite ι] :
    Algebra.adjoin k (Set.range (powersLinearForm k a)) = ⊤ := by
  have := isStandard_powersGrading (V := span k (Set.range a)) (fg_span (Set.finite_range a))
  refine eq_top_iff.mpr ?_
  rw [← GradedAlgebra.IsStandard.adjoin_one (𝒜 := (span k (Set.range a)).powersGrading)]
  refine Algebra.adjoin_le fun F hF ↦ ?_
  have hF' := powersGrading_one_le_span k a hF
  exact (span_le (p := Subalgebra.toSubmodule
    (Algebra.adjoin k (Set.range (powersLinearForm k a))))).mpr Algebra.subset_adjoin hF'

section Away

variable {k} (V : Submodule k K)

/-- Evaluation at `t = 1` on `⊕ₙ Vⁿ tⁿ ⊆ K[t]`. -/
noncomputable def powersEvalOne : V.powersAlgebra →+* K :=
  (evalRingHom (1 : K)).comp (V.powersAlgebra.val : V.powersAlgebra →+* K[X])

variable {V} in
lemma powersEvalOne_of_mem {n : ℕ} {F : V.powersAlgebra} (hF : F ∈ V.powersGrading n) :
    powersEvalOne V F = (F : K[X]).coeff n := by
  obtain ⟨c, hc, rfl⟩ := mem_powersGrading_iff_exists.mp hF
  simp [powersEvalOne]

variable (k) {a} {i₀ : ι} (h : a i₀ = 1)

include h in
lemma isUnit_powersEvalOne_powersLinearForm :
    IsUnit (powersEvalOne (span k (Set.range a)) (powersLinearForm k a i₀)) := by
  rw [powersEvalOne_of_mem (powersLinearForm_mem k a i₀)]
  simp [powersLinearForm, h]

include h in
/-- The ring map underlying `Submodule.powersAwayEval`. -/
noncomputable def powersAwayEvalRingHom :
    Away (span k (Set.range a)).powersGrading (powersLinearForm k a i₀) →+* K :=
  (IsLocalization.Away.lift (powersLinearForm k a i₀)
      (isUnit_powersEvalOne_powersLinearForm k h)).comp
    (algebraMap _ (Localization.Away (powersLinearForm k a i₀)))

lemma powersAwayEvalRingHom_mk' (n : ℕ) (F : (span k (Set.range a)).powersAlgebra)
    (hF : F ∈ (span k (Set.range a)).powersGrading (n • 1)) :
    IsLocalization.Away.lift (powersLinearForm k a i₀)
      (isUnit_powersEvalOne_powersLinearForm k h)
      (Localization.mk F ⟨powersLinearForm k a i₀ ^ n, n, rfl⟩ :
        Localization.Away (powersLinearForm k a i₀)) = (F : K[X]).coeff n := by
  rw [Localization.mk_eq_mk', IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [map_pow]
  rw [powersEvalOne_of_mem (powersLinearForm_mem k a i₀),
    powersEvalOne_of_mem (n := n) (by simpa using hF)]
  simp [powersLinearForm, h]

lemma powersAwayEvalRingHom_mk (n : ℕ) (F : (span k (Set.range a)).powersAlgebra)
    (hF : F ∈ (span k (Set.range a)).powersGrading (n • 1)) :
    powersAwayEvalRingHom k h (Away.mk _ (powersLinearForm_mem k a i₀) n F hF) =
      (F : K[X]).coeff n :=
  powersAwayEvalRingHom_mk' k h n F hF

lemma powersAwayEvalRingHom_algebraMap (c : k) :
    powersAwayEvalRingHom k h (algebraMap k _ c) = algebraMap k K c := by
  have h0 : algebraMap k (span k (Set.range a)).powersAlgebra c ∈
      (span k (Set.range a)).powersGrading (0 • 1) := by
    rw [zero_smul]
    exact SetLike.algebraMap_mem_graded _ c
  have : algebraMap k (Away (span k (Set.range a)).powersGrading (powersLinearForm k a i₀)) c =
      Away.mk _ (powersLinearForm_mem k a i₀) 0 _ h0 := by
    ext
    simp only [val_algebraMap, Away.val_mk]
    exact (Localization.mk_one_eq_algebraMap _).symm
  rw [this, powersAwayEvalRingHom_mk]
  simp [Polynomial.algebraMap_apply]

/-- For `a i₀ = 1`, the `k`-algebra map `(⊕ₙ Vⁿ tⁿ)_(t) → K`, `c tⁿ / tⁿ ↦ c`, from the
degree-zero part of the localization at `t = a i₀ t`. -/
noncomputable def powersAwayEval :
    Away (span k (Set.range a)).powersGrading (powersLinearForm k a i₀) →ₐ[k] K :=
  { powersAwayEvalRingHom k h with commutes' := powersAwayEvalRingHom_algebraMap k h }

lemma powersAwayEval_mk (n : ℕ) (F : (span k (Set.range a)).powersAlgebra)
    (hF : F ∈ (span k (Set.range a)).powersGrading (n • 1)) :
    powersAwayEval k h (Away.mk _ (powersLinearForm_mem k a i₀) n F hF) = (F : K[X]).coeff n :=
  powersAwayEvalRingHom_mk k h n F hF

lemma powersAwayEval_powersLinearForm (i : ι) :
    powersAwayEval k h (Away.mk _ (powersLinearForm_mem k a i₀) 1 (powersLinearForm k a i)
      (by simpa using powersLinearForm_mem k a i)) = a i := by
  rw [powersAwayEval_mk]
  simp [powersLinearForm]

lemma powersAwayEval_injective : Function.Injective (powersAwayEval k h) := by
  apply (injective_iff_map_eq_zero (powersAwayEval k h).toRingHom).mpr
  intro z hz
  change powersAwayEval k h z = 0 at hz
  obtain ⟨n, F, hF, rfl⟩ := Away.mk_surjective _ (powersLinearForm_mem k a i₀) z
  rw [powersAwayEval_mk] at hz
  have hF0 : F = 0 := by
    refine Subtype.ext (Polynomial.ext fun e ↦ ?_)
    rcases eq_or_ne e n with rfl | he
    · simpa using hz
    · simpa using (mem_powersGrading_iff.mp (by simpa using hF)) e he
  subst hF0
  exact Away.mk_zero _ _ _ _

end Away

end Submodule
