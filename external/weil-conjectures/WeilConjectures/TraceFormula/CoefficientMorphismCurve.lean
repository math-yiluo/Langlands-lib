/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CoefficientMorphismProper
public import WeilConjectures.TraceFormula.FrobeniusCurveLocalTerm

/-!

# The trace formula for Frobenius correspondences on proper curves and on points

For `X` with the model Frobenius `Φ` of a model over a finite field, the trace formula in degree
one (`ProEtale.CondensedRing.TraceFormulaHolds`) holds for every map `ψ : LΦ^* K ⟶ K` in two
cases:

* `X` is proper and smooth of relative dimension one
  (`ProEtale.CondensedRing.traceFormulaHolds_of_smoothOfRelativeDimension_one`): the
  Lefschetz–Verdier formula (blueprint `theorem-proper-pushforward-lefschetz-verdier`) writes the
  trace as the sum of the local terms at the fixed points, and the Frobenius local term on a curve
  (blueprint `proposition-frobenius-local-term-curve`) is the trace of the stalk map. This is the
  case of `ℙ¹` in the proof of blueprint `theorem-trace-formula-frobenius-correspondence`;
* `X` is empty or a point, that is `X ⟶ Spec k` is a closed immersion
  (`ProEtale.CondensedRing.traceFormulaHolds_of_isClosedImmersion`): the local term at the
  point is the trace of the stalk map, the open piece being zero.

Neither case uses Varshavsky's contracting theorem.

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

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X} {m : ℕ}

/-- The point of the fixed locus `∐ Spec k` given by a fixed rational point `x` has range the
singleton of the lift of `x`. -/
lemma range_sigmaPointι_eq_liftPoint [IsAlgClosed k] (hΦ : IsModelFrobenius Φ f₀ p)
    (hm : 1 ≤ m) [Finite (FixedPoint Φ m)] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K) (x : FixedPoint Φ m) :
    Set.range (sigmaPointι k (FixedPoint Φ m) x).left.base =
      {((Correspondence.ofGraphFixedLocus hΦ hm K v).liftPoint x.1
        ((Category.comp_id x.1).trans x.2.symm)).left.base (default : Spec (.of k))} := by
  rw [Correspondence.liftPoint_ofGraphFixedLocus hΦ hm K v x]
  ext y
  refine ⟨?_, fun hy ↦ ⟨(default : Spec (.of k)), hy.symm⟩⟩
  rintro ⟨z, rfl⟩
  rw [Set.mem_singleton_iff, Subsingleton.elim (α := Spec (.of k)) z default]
  rfl

set_option linter.overlappingInstances false in
/-- **The trace formula on a model with given local terms** (blueprint
`theorem-trace-formula-frobenius-correspondence`, the case of the affine line through `ℙ¹`): for a
proper `X` with the model Frobenius `Φ` and `m ≥ 1`, if the local term of every map
`v : LΦ_m^* K ⟶ K` at every fixed rational point `x` is the trace of the stalk map `v_x`, the
trace formula in degree one holds for `Φ_m`. The Lefschetz–Verdier formula (blueprint
`theorem-proper-pushforward-lefschetz-verdier`) writes the trace as the sum of the local terms over
the components `∐ Spec k` of the fixed locus. -/
theorem traceFormulaHolds_frobeniusIterate_of_localTerm [IsAlgClosed k] [IsProper X.hom]
    [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p) [IsProper Φ.left] (hm : 1 ≤ m)
    (hLT : ∀ (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
      (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (frobeniusIterate Φ m)).obj K ⟶ K) [Finite (FixedPoint Φ m)] (x : FixedPoint Φ m)
      [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x.1).obj K)],
      ((Correspondence.ofGraph K (frobeniusIterate Φ m) v).traceClass
          (Correspondence.ofGraphFixedLocus hΦ hm K v)).localTerm
          (sigmaPointι k (FixedPoint Φ m) x) =
        End.of (trace (Correspondence.graphStalkMap K (frobeniusIterate Φ m) v x.1 x.2))) :
    TraceFormulaHolds ℓ (frobeniusIterate Φ m) := by
  intro K v _ _ _
  let F := Correspondence.ofGraphFixedLocus hΦ hm K v
  have : IsProper F.F.hom := inferInstanceAs (IsProper (sigmaPoint k (FixedPoint Φ m)).hom)
  rw [← Correspondence.globalOperator_ofGraph]
  suffices h : End.of (trace (Correspondence.ofGraph K (frobeniusIterate Φ m) v).globalOperator) =
      ∑ x : FixedPoint Φ m,
        End.of (trace (Correspondence.graphStalkMap K (frobeniusIterate Φ m) v x.1 x.2)) by
    simpa only [End.sum_asHom] using congrArg End.asHom h
  rw [(Correspondence.ofGraph K (frobeniusIterate Φ m) v).trace_globalOperator_eq_sum_localTerm F
      (fun _ ↦ point k) (sigmaPointι k (FixedPoint Φ m))
      (fun _ _ h ↦ disjoint_range_sigmaPointι k _ h) (iUnion_range_sigmaPointι k _)]
  exact Finset.sum_congr rfl fun x _ ↦ hLT K v x

set_option linter.overlappingInstances false in
/-- **The trace formula on a proper smooth curve** (blueprint
`theorem-trace-formula-frobenius-correspondence`, the case of the affine line through `ℙ¹`; detailed
form `theorem-trace-formula-frobenius-correspondence--1`, Step 2): for `X` proper and smooth of
relative dimension one over `k` with the model Frobenius `Φ` of a model over a finite field, the
trace formula in degree one holds for `Φ_m`, `m ≥ 1`. The Lefschetz–Verdier formula (blueprint
`theorem-proper-pushforward-lefschetz-verdier`) writes the trace as the sum of the local terms at
the fixed points, and the Frobenius local term on a curve (blueprint
`proposition-frobenius-local-term-curve`,
`Correspondence.localTerm_traceClass_frobeniusGraph_eq_trace_of_smooth`) is the trace of the stalk
map. -/
theorem traceFormulaHolds_frobeniusIterate_of_smoothOfRelativeDimension_one [IsAlgClosed k]
    [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀]
    (hΦ : IsModelFrobenius Φ f₀ p) [IsProper Φ.left] (hm : 1 ≤ m) :
    TraceFormulaHolds ℓ (frobeniusIterate Φ m) :=
  traceFormulaHolds_frobeniusIterate_of_localTerm hΦ hm fun K v _ x _ ↦
    Correspondence.localTerm_traceClass_frobeniusGraph_eq_trace_of_smooth hΦ hm v
      (Correspondence.ofGraphFixedLocus hΦ hm K v) x.1 x.2 (B := point k)
      (sigmaPointι k (FixedPoint Φ m) x) (range_sigmaPointι_eq_liftPoint hΦ hm K v x)

set_option linter.overlappingInstances false in
/-- **The trace formula on a proper smooth curve**, degree one (blueprint
`theorem-trace-formula-frobenius-correspondence`, the case of `ℙ¹`). -/
theorem traceFormulaHolds_of_smoothOfRelativeDimension_one [IsAlgClosed k] [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    [IsProper Φ.left] : TraceFormulaHolds ℓ Φ := by
  have h := traceFormulaHolds_frobeniusIterate_of_smoothOfRelativeDimension_one (ℓ := ℓ) hΦ le_rfl
  rwa [traceFormulaHolds_congr (frobeniusIterate_one Φ)] at h

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- A scheme over `k` whose structure morphism is a closed immersion has at most one point. -/
lemma subsingleton_left_of_isClosedImmersion [IsClosedImmersion X.hom] : Subsingleton X.left :=
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  ⟨fun _ _ ↦ X.hom.isEmbedding.injective (Subsingleton.elim _ _)⟩

set_option linter.overlappingInstances false in
/-- **The trace formula on a point** (blueprint `theorem-trace-formula-frobenius-correspondence`,
finite schemes): if `X ⟶ Spec k` is a closed immersion, so that `X` is empty or a point, the trace
formula in degree one holds for the model Frobenius `Φ`. The Lefschetz–Verdier formula writes the
trace as the sum of the local terms, and the local term at the point is the trace of the stalk
map, the open piece being zero
(`Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_subsingleton`). -/
theorem traceFormulaHolds_of_isClosedImmersion [IsAlgClosed k] [IsClosedImmersion X.hom]
    [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p) [IsProper Φ.left] :
    TraceFormulaHolds ℓ Φ := by
  have := subsingleton_left_of_isClosedImmersion (X := X)
  have h := traceFormulaHolds_frobeniusIterate_of_localTerm (ℓ := ℓ) hΦ le_rfl fun K v _ x _ ↦
    Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_subsingleton _ v
      (Correspondence.ofGraphFixedLocus hΦ le_rfl K v) x.1 x.2 (B := point k)
      (sigmaPointι k (FixedPoint Φ 1) x) (range_sigmaPointι_eq_liftPoint hΦ le_rfl K v x)
  rwa [traceFormulaHolds_congr (frobeniusIterate_one Φ)] at h

end AlgebraicGeometry.ProEtale.CondensedRing
