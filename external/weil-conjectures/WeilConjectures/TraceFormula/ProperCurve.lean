/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FixedPointScheme
public import WeilConjectures.TraceFormula.FrobeniusCurveLocalTerm
public import WeilConjectures.TraceFormula.LefschetzVerdier
public import WeilConjectures.TraceFormula.StalkFrobeniusGraph

/-!

# The trace formula on a proper smooth curve

Let `X` be a proper smooth curve over an algebraically closed field `k`, with the model Frobenius
`Φ` of a model `X₀` over a finite field, and let `(K, φ)` be a Weil object for `Φ`. For `m ≥ 1`
the fixed scheme of `Φ_m` is the disjoint union of the points `x` fixed by `Φ_m`
(`ProEtale.CondensedRing.IsModelFrobenius.nonempty_isLimit_fixedPointsFork`), so it is a fixed
locus of the graph correspondence `c_m = (𝟙, Φ_m)` whose open and closed pieces are these points
(`ProEtale.CondensedRing.IsModelFrobenius.graphFixedLocus`). The Lefschetz–Verdier formula
(`ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_sum_localTerm`) and the local term
of the Frobenius correspondence at a fixed point then give the trace formula
```
tr(T_{c_m}(φ_m) | RΓ(X, K)) = ∑_{x ∈ X(k), Φ_m x = x} tr(F_{x,m} | K_x)
```
(`ProEtale.CondensedRing.WeilBoundedConstructible.trace_globalOperator_graph_eq_sum`), and the
same for the global Frobenius of the compactly supported cohomology of the Weil object
(`WeilBoundedConstructible.trace_globalOperator_eq_sum_of_smoothOfRelativeDimension_one`).
This is the curve case in Step 2 of the proof of blueprint
`theorem-trace-formula-frobenius-correspondence--1`, for the proper curve itself.

The local term at a fixed point `x` is the trace of the local Frobenius `F_{x,m}`, which is the
stalk map of `φ_m` at `x` (`WeilBoundedConstructible.stalkFrobenius_eq_graphStalkMap`). It is
taken from the curve route of SGA 5, III B (blueprint `corollary-contracting-local-terms-point`,
item 3, `proposition-frobenius-local-term-curve`, `lemma-vanishing-local-term-zero-stalk--2`:
`ProEtale.CondensedRing.Correspondence.localTerm_traceClass_frobeniusGraph_eq_trace_of_smooth`),
not from Varshavsky's theorem for contracting correspondences, so the trace formula does not
depend on nearby cycles.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [IsAlgClosed k]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X} {m : ℕ}

/-- **The fixed locus of the Frobenius graph** (blueprint `lemma-frobenius-fixed-scheme--1`): for
the model Frobenius `Φ` and `m ≥ 1`, the disjoint union `∐ Spec k` of the rational points fixed
by `Φ_m` is a fixed locus of the graph correspondence `c_m = (𝟙, Φ_m)` of a Weil object. -/
noncomputable def IsModelFrobenius.graphFixedLocus (hΦ : IsModelFrobenius Φ f₀ p) (hm : 1 ≤ m)
    [Finite (FixedPoint Φ m)] (K : WeilBoundedConstructible ℓ Φ) : (K.graph m).FixedLocus where
  F := sigmaPoint k (FixedPoint Φ m)
  ι := fixedPointsι Φ m
  w := fixedPointsι_comp Φ m
  isLimit := (hΦ.nonempty_isLimit_fixedPointsFork hm).some

/-- The point of the fixed locus `∐ Spec k` given by a fixed rational point `x` is the component
of `x`. -/
lemma IsModelFrobenius.fixedLocusPoint_graphFixedLocus (hΦ : IsModelFrobenius Φ f₀ p)
    (hm : 1 ≤ m) [Finite (FixedPoint Φ m)] (K : WeilBoundedConstructible ℓ Φ)
    (x : FixedPoint Φ m) :
    K.fixedLocusPoint m (hΦ.graphFixedLocus hm K) x.1 x.2 =
      sigmaPointι k (FixedPoint Φ m) x :=
  Fork.IsLimit.hom_ext (hΦ.graphFixedLocus hm K).isLimit
    (((hΦ.graphFixedLocus hm K).isLimit.fac _ WalkingParallelPair.zero).trans
      (sigmaPointι_fixedPointsι Φ m x).symm)

set_option linter.overlappingInstances false in
/-- **The trace formula on a proper smooth curve** (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Step 2, for a proper curve; from
`theorem-proper-pushforward-lefschetz-verdier`, `proposition-frobenius-local-term-curve--1` on
curves (`corollary-contracting-local-terms-point`, item 3) and `lemma-frobenius-fixed-scheme--1`):
for a proper smooth curve `X` with the model Frobenius `Φ`, a Weil object `(K, φ)` and `m ≥ 1`, the
trace of the global operator of the graph correspondence `c_m = (𝟙, Φ_m)` on `RΓ(X, K)` is the sum
over the rational points `x` fixed by `Φ_m` of the traces of the local Frobenius `F_{x,m}` on the
stalks `K_x`. -/
theorem WeilBoundedConstructible.trace_globalOperator_graph_eq_sum [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀]
    (hΦ : IsModelFrobenius Φ f₀ p) (K : WeilBoundedConstructible ℓ Φ) (hm : 1 ≤ m)
    [Fintype (FixedPoint Φ m)] [IsFinite (frobeniusIterate Φ m).left]
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        K.carrier)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        K.carrier)] :
    trace (K.graph m).globalOperator =
      ∑ x : FixedPoint Φ m, trace (K.stalkFrobenius m x.1 x.2) := by
  suffices h : End.of (trace (K.graph m).globalOperator) =
      ∑ x : FixedPoint Φ m, End.of (trace (K.stalkFrobenius m x.1 x.2)) by
    simpa only [End.sum_asHom] using congrArg End.asHom h
  let F := hΦ.graphFixedLocus hm K
  have : IsProper F.F.hom := inferInstanceAs (IsProper (sigmaPoint k (FixedPoint Φ m)).hom)
  rw [(K.graph m).trace_globalOperator_eq_sum_localTerm F (fun _ ↦ point k)
    (sigmaPointι k (FixedPoint Φ m)) (fun _ _ h ↦ disjoint_range_sigmaPointι k _ h)
    (iUnion_range_sigmaPointι k _)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hB : Set.range (sigmaPointι k (FixedPoint Φ m) x).left.base =
      {(K.fixedLocusPoint m F x.1 x.2).left.base (default : Spec (.of k))} := by
    rw [hΦ.fixedLocusPoint_graphFixedLocus hm K x]
    ext y
    refine ⟨?_, fun hy ↦ ⟨(default : Spec (.of k)), hy.symm⟩⟩
    rintro ⟨z, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim (α := Spec (.of k)) z default]
    rfl
  rw [K.stalkFrobenius_eq_graphStalkMap]
  exact Correspondence.localTerm_traceClass_frobeniusGraph_eq_trace_of_smooth hΦ hm
    (K.iterateStr m).hom F x.1 x.2 (sigmaPointι k _ x) hB

set_option linter.overlappingInstances false in
/-- **The trace formula on a proper smooth curve**, for the global Frobenius `F_{c,m}` of the
compactly supported cohomology of the Weil object (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Step 2, for a proper curve, with
`lemma-scheme-frobenius-geometric-frobenius--3`). -/
theorem WeilBoundedConstructible.trace_globalOperator_eq_sum_of_smoothOfRelativeDimension_one
    [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀]
    (hΦ : IsModelFrobenius Φ f₀ p) (K : WeilBoundedConstructible ℓ Φ) (hm : 1 ≤ m)
    [Fintype (FixedPoint Φ m)] [IsFinite (frobeniusIterate Φ m).left]
    [IsUniversalHomeomorphism (frobeniusIterate Φ m).left]
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        K.carrier)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        K.carrier)] :
    trace (K.globalOperator m) = ∑ x : FixedPoint Φ m, trace (K.stalkFrobenius m x.1 x.2) := by
  rw [K.globalOperator_eq_correspondenceGlobalOperator m]
  exact K.trace_globalOperator_graph_eq_sum hΦ hm

end AlgebraicGeometry.ProEtale.CondensedRing
