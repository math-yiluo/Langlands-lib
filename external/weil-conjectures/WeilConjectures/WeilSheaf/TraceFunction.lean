/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PointCount
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseRank
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.StalkConstantTwist
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.StalkIso
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.StalkUpperStarCharpoly
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace

/-!
# Computations of trace functions

The trace function `t_{F,n}(y)` of a Weil sheaf at an `𝔽_{qⁿ}`-rational point `y` over a closed
point `x` of degree `d` is the trace of `F_x^{n/d}` on the stalk at `x`
(`AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_frobeniusEnd_stalk_pow`). This file
computes it for constant twists, direct sums and duals, and bounds it for sheaves with upper
weight bounds.

## Main results

- `AlgebraicGeometry.WeilSheaf.traceFunction_constantTwist`: `t_{F ⊗ 𝓑_b, n} = bⁿ t_{F, n}`.
- `AlgebraicGeometry.WeilSheaf.traceFunction_biprod`: additivity in direct sums.
- `AlgebraicGeometry.WeilSheaf.map_traceFunction_dual`: for `F` punctually pure of weight `0`,
  the trace function of the dual is the complex conjugate.
- `AlgebraicGeometry.WeilSheaf.norm_map_traceFunction_le`: the bound
  `|ι t_{F,n}(y)| ≤ dim F_x · q^{nw/2}` for weights at most `w`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- The image of a rational point with values in a finite field is a point with finite residue
field: its residue field embeds into the finite field. -/
theorem Scheme.Hom.base_mem_finitePoints_of_fieldPoints {X : Scheme.{u}} {k : Type u}
    [Field k] (f : X.Hom (Spec (.of k))) (K : Type u) [Field K] [Algebra k K] [Finite K]
    (p : f.fieldPoints K) (z : Spec (.of K)) : p.1.base z ∈ X.finitePoints := by
  have hz : p.1.base default = p.1.base z := congrArg p.1.base (Subsingleton.elim _ _)
  obtain ⟨φ, -⟩ := (f.exists_fieldPoints_base_eq_iff K (p.1.base z)).1 ⟨p, hz⟩
  exact X.mem_finitePoints.mpr (Finite.of_injective _ φ.hom.injective)

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The closed point under an `𝔽_{qⁿ}`-rational point. -/
noncomputable def finitePointOfFieldPoint {n : ℕ}
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    X.finitePoints :=
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  ⟨_, (X ↘ Spec (CommRingCat.of k₀)).base_mem_finitePoints_of_fieldPoints _ y
    (IsLocalRing.closedPoint _)⟩

/-- The degree of the closed point under an `𝔽_{qⁿ}`-rational point divides `n`. -/
theorem degreeOver_finitePointOfFieldPoint_dvd {n : ℕ}
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (X ↘ Spec (CommRingCat.of k₀)).degreeOver (finitePointOfFieldPoint y).1 ∣ n :=
  (X ↘ Spec (CommRingCat.of k₀)).degreeOver_dvd_of_fieldPoints n y

variable (F G : WeilSheaf k₀ l X)

/-- The trace function at `y` is the trace of the `n / d`-th power of the local Frobenius at
the closed point under `y`, of degree `d`. -/
theorem traceFunction_eq_trace (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    F.traceFunction n y = LinearMap.trace (PadicAlgCl l) _
      ((F.stalk (finitePointOfFieldPoint y)).frobeniusEnd ^
        (n / (X ↘ Spec (CommRingCat.of k₀)).degreeOver (finitePointOfFieldPoint y).1)) :=
  F.traceFunction_eq_trace_frobeniusEnd_stalk_pow n y _ rfl

/-- The trace function of the constant twist `F ⊗ 𝓑_b` is `bⁿ` times that of `F`: at a closed
point of degree `d` the twist multiplies the local Frobenius by `b^d`. -/
theorem traceFunction_constantTwist (b : (PadicAlgCl l)ˣ) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (F.constantTwist b).traceFunction n y = (b : PadicAlgCl l) ^ n * F.traceFunction n y := by
  rw [traceFunction_eq_trace, traceFunction_eq_trace]
  obtain ⟨e⟩ := F.nonempty_equiv_stalk_constantTwist b (finitePointOfFieldPoint y)
  rw [← e.trace_frobeniusEnd_pow, FrobeniusModule.trace_frobeniusEnd_rescale_pow _
    (pow_ne_zero _ b.ne_zero), ← pow_mul,
    Nat.mul_div_cancel' (degreeOver_finitePointOfFieldPoint_dvd y)]

/-- The trace function of a direct sum is the sum of the trace functions. -/
theorem traceFunction_biprod (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (F ⊞ G).traceFunction n y = F.traceFunction n y + G.traceFunction n y := by
  rw [traceFunction_eq_trace, traceFunction_eq_trace, traceFunction_eq_trace]
  obtain ⟨e⟩ := nonempty_equiv_stalk_biprod F G (finitePointOfFieldPoint y)
  rw [← e.trace_frobeniusEnd_pow, FrobeniusModule.trace_frobeniusEnd_prod_pow]

variable {F} in
/-- For a lisse sheaf `F` punctually `ι`-pure of weight `0`, the trace function of the dual
`F^∨` is the complex conjugate of that of `F`: the local eigenvalues of the dual are the inverses
of those of `F`, which have absolute value `1`. -/
theorem map_traceFunction_dual {ι : PadicAlgCl l →+* ℂ} (hF : F.IsLisse)
    (h : F.IsPunctuallyPureOfWeight ι 0) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ι ((F.dual hF).traceFunction n y) = (starRingEnd ℂ) (ι (F.traceFunction n y)) := by
  rw [traceFunction_eq_trace, traceFunction_eq_trace]
  obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF (finitePointOfFieldPoint y)
  rw [← e.trace_frobeniusEnd_pow]
  exact (h _).map_trace_frobeniusEnd_dual_pow _

variable {F} in
/-- If `F` has weights at most `w`, then `|ι t_{F,n}(y)| ≤ dim F_x · q^{nw/2}`, `x` the closed
point under `y`: the trace of `F_x^{n/d}` is a sum of `dim F_x` eigenvalue powers, each of
absolute value at most `(q^{dw/2})^{n/d} = q^{nw/2}`. -/
theorem norm_map_traceFunction_le {ι : PadicAlgCl l →+* ℂ} {w : ℝ} (h : F.HasWeightsAtMost ι w)
    (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ‖ι (F.traceFunction n y)‖ ≤
      Module.finrank (PadicAlgCl l) (F.stalk (finitePointOfFieldPoint y)).carrier *
        ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n := by
  rw [traceFunction_eq_trace]
  refine ((h _).norm_map_trace_frobeniusEnd_pow_le _).trans_eq ?_
  obtain ⟨c, hc⟩ := degreeOver_finitePointOfFieldPoint_dvd y
  set d := (X ↘ Spec (CommRingCat.of k₀)).degreeOver (finitePointOfFieldPoint y).1
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  congr 1
  rcases Nat.eq_zero_or_pos d with hd | hd
  · rw [hd, zero_mul] at hc
    rw [hd, Nat.div_zero, pow_zero]
    conv_rhs => rw [hc, pow_zero]
  · rw [show n / d = c by rw [hc, Nat.mul_div_cancel_left _ hd]]
    conv_rhs => rw [hc]
    rw [Scheme.Hom.residueCard, Nat.cast_pow,
      ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), ← Real.rpow_mul hq, ← Real.rpow_mul hq]
    congr 1
    push_cast
    ring

variable {F} in
/-- **The rank of a lisse Weil sheaf is bounded**: on a `k₀`-scheme quasi-compact over `k₀`, the
stalks of a lisse Weil sheaf have bounded dimension, the geometric fiber being quasi-compact
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_forall_finrank_le`). -/
theorem IsLisse.exists_forall_finrank_stalk_le [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (hF : F.IsLisse) :
    ∃ N : ℕ, ∀ x : X.finitePoints, Module.finrank (PadicAlgCl l) (F.stalk x).carrier ≤ N := by
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure := by
    unfold Scheme.Hom.geometricFiberToAlgebraicClosure Scheme.Hom.geometricFiber
    infer_instance
  have : CompactSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    QuasiCompact.compactSpace_of_compactSpace
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  obtain ⟨N, hN⟩ := ProEtale.IsAdicLisseSheaf.exists_forall_finrank_le hF
  exact ⟨N, fun x ↦ hN _ _⟩

/-- Isomorphic Weil sheaves have the same trace function. -/
theorem traceFunction_eq_of_iso {F G : WeilSheaf k₀ l X} (e : F ≅ G) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    F.traceFunction n y = G.traceFunction n y := by
  rw [traceFunction_eq_trace, traceFunction_eq_trace]
  obtain ⟨e'⟩ := nonempty_equiv_stalkAt_of_iso _ _
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (X ↘ Spec (CommRingCat.of k₀)) (finitePointOfFieldPoint y)) e
  exact (e'.trace_frobeniusEnd_pow _).symm

end WeilSheaf

end AlgebraicGeometry
