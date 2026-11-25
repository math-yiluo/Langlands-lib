/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroQbar
public import WeilConjectures.TraceFormula.CurveSupportedPairing
public import WeilConjectures.TraceFormula.GraphPieces
public import WeilConjectures.TraceFormula.LocalTermPoint
public import WeilConjectures.TraceFormula.PieceAdditivity
public import WeilConjectures.TraceFormula.PointNormalization
public import WeilConjectures.TraceFormula.ProperCompatibility

/-!

# The Frobenius local term on a smooth curve

Let `X` be smooth of relative dimension one over `s = Spec k`, with the model Frobenius `Φ` of a
model `X₀` over a finite field, let `m ≥ 1`, `v : LΦ_m^* K ⟶ K` an arbitrary (not necessarily
invertible) map and `x` a rational point fixed by `Φ_m`. For an open and closed subscheme `B` of
the fixed locus of the graph correspondence `(𝟙, Φ_m)` with underlying set `{x}`, the local term
of `v` along `B` is the trace of the stalk map `v_x` (blueprint
`proposition-frobenius-local-term-curve`, `proposition-frobenius-local-term-curve--1`):
```
LT_B(v) = tr(v_x | K_x).
```
This file follows the route of blueprint `remark-outline-local-computation` (SGA 5, III B, §§2–4),
without nearby cycles and without Varshavsky's contracting theorem.

* The open–closed filtration `K^U = j_! Lj^* K ⟶ K ⟶ K^Z = Rx_* Lx^* K` at `x` and filtered
  trace-class additivity (`Correspondence.traceClass_ofGraph_eq_add`, blueprint
  `proposition-additivity-trace-classes`) split the local term into the local terms of the closed
  piece and of the open piece. The closed piece is the proper pushforward of the point
  correspondence `v_x`, whose local term is `tr(v_x)` by proper pushforward compatibility (blueprint
  `theorem-proper-pushforward-lefschetz-verdier`) and the point case (blueprint
  `lemma-local-terms-point`). Hence the local term is `tr(v_x)` as soon as the open piece
  contributes zero (`Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_localTerm_eq_zero`).
* The open piece has zero stalk at `x`, and on a smooth curve the local term of a coefficient
  with zero stalk at `x` vanishes (blueprint `lemma-vanishing-local-term-zero-stalk--2`,
  `Correspondence.localTerm_traceClass_frobeniusGraph_eq_zero_of_smooth`): the local term is the
  integral of the evaluation of the supported restriction `ρ_P` from the Frobenius graph to the
  diagonal (blueprint `lemma-local-term-restriction-map`,
  `Correspondence.localTerm_traceClass_frobeniusGraph_eq_zero_of_supportedRestriction`), and the
  stalk of `ρ_P` at `x` vanishes when `K_x = 0` (blueprint `lemma-vanishing-local-term-zero-stalk`,
  `Correspondence.upperStar_map_supportedRestriction_frobeniusGraph_eq_zero`).
* If `X` has a single point, the open piece is zero and the local term is `tr(v_x)` for every
  endomorphism (`Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_subsingleton`).

## Coefficients

The blueprint carries out the local calculation with a finite `ℓ`-primary coefficient ring `A`,
on the classical étale models. The trace classes of this chapter are only defined with
coefficients `ℚ̄_ℓ`; the statements here are the `ℚ̄_ℓ`-forms. The vanishing of the supported
restriction is a vanishing of a morphism before any trace is taken, and the `ℚ̄_ℓ`-form follows
from the finite forms by the integral models of blueprint
`lemma-integral-models-rational-frobenius-correspondences`: a morphism of perfect `𝒪_E`-complexes
whose reductions modulo every `π_E^n` vanish is zero, since
`Hom(P, Q) ⊗ 𝒪_E/π_E^n ↪ Hom(P, Q ⊗ 𝒪_E/π_E^n)`.

## Main statements

- `ProEtale.CondensedRing.Correspondence.localTerm_traceClass_frobeniusGraph_eq_trace_of_smooth`:
  the Frobenius local term on a smooth curve (blueprint `proposition-frobenius-local-term-curve`).
- `ProEtale.CondensedRing.Correspondence.localTerm_traceClass_frobeniusGraph_eq_zero_of_smooth`:
  the Frobenius local vanishing on a smooth curve (blueprint
  `lemma-vanishing-local-term-zero-stalk--2`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

/-! ### Reduction to the open piece -/

/-- **The local term at a fixed point modulo the open piece** (blueprint
`proposition-frobenius-local-term-curve`, proof: the open–closed filtration at `x`, filtered
trace-class additivity `proposition-additivity-trace-classes`, proper pushforward
`theorem-proper-pushforward-lefschetz-verdier` and the point case `lemma-local-terms-point`): let
`x` be a rational point fixed by `h` and `B` an open and closed subscheme of the fixed locus of the
graph correspondence `(𝟙, h)`, proper over `s`, with underlying set `{x}`. If the trace class of the
open piece `u^U = [j]_! (v|_U)` on `K^U = j_! Lj^* K` has local term zero along `B`, the local term
of `v` along `B` is the trace of the stalk map `v_x`. -/
theorem localTerm_traceClass_ofGraph_eq_trace_of_localTerm_eq_zero (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (F : (ofGraph K h v).FixedLocus) (x : RationalPoint X) (hx : x ≫ h = x)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x ((Category.comp_id x).trans hx.symm)).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)]
    (hU : (F.traceClassWithCoeff _ (graphOpenPieceCoeff K v hx ≫
      (boundedConstructibleUpperShriekId ℓ X).inv.app _)).localTerm j = 0) :
    ((ofGraph K h v).traceClass F).localTerm j = .of (trace (graphStalkMap K h v x hx)) := by
  rw [traceClass_ofGraph_eq_add K v hx F, BorelMooreSection.localTerm_add, hU, add_zero]
  refine (localTerm_traceClass_eq_integral_of_restrict_eq
    (F.withCoeff _ (graphClosedPieceCoeff K v hx)) ((Category.comp_id x).trans hx.symm)
    j hB _ fun e _ he ↦ ?_).trans (integral_traceClass_ofEnd (graphStalkMap K h v x hx))
  let P := graphClosedPieceDiagram K v hx
  let Fc := fixedLocusOfEnd (graphStalkMap K h v x hx)
  let Fb : P.pushforward.FixedLocus := F.withCoeff _ (graphClosedPieceCoeff K v hx)
  have : IsProper (e ≫ j).left := by
    rw [Over.comp_left]
    infer_instance
  have hfix : P.fixMap Fc Fb = e ≫ j := by
    rw [he]
    refine Fb.hom_ext ?_
    rw [P.fixMap_ι]
    exact (Category.id_comp x).trans (F.liftPoint_ι x _).symm
  have hZ := P.traceClassPushforward_eq Fc Fb
  rw [ProperPushforwardDiagram.traceClassPushforward, BorelMooreSection.pushforward_congr hfix,
    ← BorelMooreSection.pushforward_comp] at hZ
  refine (congrArg (BorelMooreSection.restrict j) hZ.symm).trans ?_
  rw [BorelMooreSection.restrict_pushforward_self]

/-- **The local term on a one-point scheme**: if `X` has a single point, the open piece at a
fixed rational point `x` is zero, and the local term of the graph correspondence `(𝟙, h)` along
an open and closed subscheme `B` of the fixed locus with underlying set `{x}` is the trace of the
stalk map `v_x`. -/
theorem localTerm_traceClass_ofGraph_eq_trace_of_subsingleton [Subsingleton X.left] (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (F : (ofGraph K h v).FixedLocus) (x : RationalPoint X) (hx : x ≫ h = x)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x ((Category.comp_id x).trans hx.symm)).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)] :
    ((ofGraph K h v).traceClass F).localTerm j = .of (trace (graphStalkMap K h v x hx)) := by
  refine localTerm_traceClass_ofGraph_eq_trace_of_localTerm_eq_zero h v F x hx j hB ?_
  have hx' : Set.range x.left.base = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ ⟨(default : Spec (.of k)), Subsingleton.elim _ _⟩
  have hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj
      (pointOpenPiece K x)) :=
    isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ (pointComplι x) h
      ((isCompl_range_pointComplι x).disjoint.mono_right (hx' ▸ Set.subset_univ _)) _
  have h0 : F.traceClassWithCoeff _ (graphOpenPieceCoeff K v hx ≫
      (boundedConstructibleUpperShriekId ℓ X).inv.app _) = 0 :=
    traceClass_eq_zero_of_isZero _ _ hK
  rw [h0]
  simpa using BorelMooreSection.localTerm_add j 0 0

/-! ### The curve case -/

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- **Frobenius local vanishing on a smooth curve** (blueprint
`lemma-vanishing-local-term-zero-stalk--2`): let `X` be smooth of relative dimension one over the
algebraically closed field `k`, with the model Frobenius `Φ` of a model over a finite field,
`m ≥ 1`, `v : LΦ_m^* K ⟶ K` arbitrary and `x` a rational point fixed by `Φ_m` with `K_x = 0`. Then
the local term `LT_B(v)` of the graph correspondence `(𝟙, Φ_m)` along an open and closed subscheme
`B` of the fixed locus with underlying set `{x}` is zero. No invertibility of `v` is assumed.

The supported restriction vanishes at `x`
(`upperStar_map_supportedRestriction_frobeniusGraph_eq_zero`, blueprint
`lemma-vanishing-local-term-zero-stalk`), so its composite with evaluation and integration, which is
the local term
(`localTerm_traceClass_frobeniusGraph_eq_zero_of_supportedRestriction`, blueprint
`lemma-local-term-restriction-map`), is zero. -/
theorem localTerm_traceClass_frobeniusGraph_eq_zero_of_smooth [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x ((Category.comp_id x).trans hx.symm)).left.base (default : Spec (.of k))})
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :
    ((ofGraph K (frobeniusIterate Φ m) v).traceClass F).localTerm j = 0 :=
  localTerm_traceClass_frobeniusGraph_eq_zero_of_supportedRestriction hΦ hm v F _ j hB
    (upperStar_map_supportedRestriction_frobeniusGraph_eq_zero hΦ hm v F _ (by
      rw [FixedLocus.liftPoint_ι]
      exact hK))

/-- **The Frobenius local term on a smooth curve** (blueprint
`proposition-frobenius-local-term-curve`, `proposition-frobenius-local-term-curve--1`): let `X` be
smooth of relative dimension one over the algebraically closed field `k`, with the model Frobenius
`Φ` of a model over a finite field, `m ≥ 1`, `v : LΦ_m^* K ⟶ K` an arbitrary (not necessarily
invertible) map and `x` a rational point fixed by `Φ_m`. For an open and closed subscheme `B` of the
fixed locus of the graph correspondence `(𝟙, Φ_m)`, proper over `s`, with underlying set `{x}`, the
local term of `v` along `B` is the trace of the stalk map `v_x` on `K_x`. No local constancy of `K`
at `x` is assumed.

The open–closed filtration at `x` and filtered trace-class additivity reduce this to the point
and to the open piece (`localTerm_traceClass_ofGraph_eq_trace_of_localTerm_eq_zero`), whose stalk
at `x` vanishes, so that it contributes zero by the Frobenius local vanishing
(`localTerm_traceClass_frobeniusGraph_eq_zero_of_smooth`, blueprint
`lemma-vanishing-local-term-zero-stalk--2`). -/
theorem localTerm_traceClass_frobeniusGraph_eq_trace_of_smooth [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x ((Category.comp_id x).trans hx.symm)).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)] :
    ((ofGraph K (frobeniusIterate Φ m) v).traceClass F).localTerm j =
      .of (trace (graphStalkMap K (frobeniusIterate Φ m) v x hx)) :=
  localTerm_traceClass_ofGraph_eq_trace_of_localTerm_eq_zero _ v F x hx j hB
    (localTerm_traceClass_frobeniusGraph_eq_zero_of_smooth (K := pointOpenPiece K x) hΦ hm
      (graphOpenPieceCoeff K v hx) (F.withCoeff _ _) x hx j hB
      (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ (pointComplι x) x
        (isCompl_range_pointComplι x).disjoint _))

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
