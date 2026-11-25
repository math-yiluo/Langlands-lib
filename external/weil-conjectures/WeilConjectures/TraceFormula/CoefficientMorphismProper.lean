/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CoefficientMorphismBasic
public import WeilConjectures.TraceFormula.ContractingGraph
public import WeilConjectures.TraceFormula.ProperCurve

/-!

# The trace formula for Frobenius coefficient morphisms on a proper scheme

For a proper `X` with the model Frobenius `Φ` of a model over a finite field, the trace formula in
degree one holds for every map `ψ : LΦ^* K ⟶ K`
(`ProEtale.CondensedRing.traceFormulaHolds_of_isProper`): the fixed scheme of `Φ` is the disjoint
union of the fixed rational points, the Lefschetz–Verdier formula
(`ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_sum_localTerm`) writes the trace
as the sum of the local terms, and the graph of the model Frobenius is contracting at its fixed
points, so that each local term is the trace of the stalk map
(`ProEtale.CondensedRing.Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_isContractingAt`).
This is Step 2 of the proof of blueprint `theorem-trace-formula-frobenius-correspondence--1` (on
`ℙ¹`), for an arbitrary proper scheme.

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

omit [Finite k₀] [Algebra k₀ k] in
/-- The trace formula in degree one only depends on the endomorphism, not on the properness
instance. -/
lemma traceFormulaHolds_congr {Φ Φ' : X ⟶ X} (e : Φ = Φ') [IsProper Φ.left] [IsProper Φ'.left] :
    TraceFormulaHolds ℓ Φ ↔ TraceFormulaHolds ℓ Φ' := by
  subst e
  rfl

namespace Correspondence

/-- **The fixed locus of a Frobenius graph** (blueprint `lemma-frobenius-fixed-scheme--1`): for
the model Frobenius `Φ` and `m ≥ 1`, the disjoint union `∐ Spec k` of the rational points fixed
by `Φ_m` is a fixed locus of the graph correspondence `(𝟙, Φ_m)` with any coefficient map. -/
noncomputable def ofGraphFixedLocus [IsAlgClosed k] (hΦ : IsModelFrobenius Φ f₀ p) (hm : 1 ≤ m)
    [Finite (FixedPoint Φ m)] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K) :
    (ofGraph K (frobeniusIterate Φ m) v).FixedLocus where
  F := sigmaPoint k (FixedPoint Φ m)
  ι := fixedPointsι Φ m
  w := fixedPointsι_comp Φ m
  isLimit := (hΦ.nonempty_isLimit_fixedPointsFork hm).some

/-- The point of the fixed locus `∐ Spec k` given by a fixed rational point `x` is the component
of `x`. -/
lemma liftPoint_ofGraphFixedLocus [IsAlgClosed k] (hΦ : IsModelFrobenius Φ f₀ p) (hm : 1 ≤ m)
    [Finite (FixedPoint Φ m)] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K) (x : FixedPoint Φ m)
    (hx : x.1 ≫ (ofGraph K (frobeniusIterate Φ m) v).c₁ =
      x.1 ≫ (ofGraph K (frobeniusIterate Φ m) v).c₂) :
    (ofGraphFixedLocus hΦ hm K v).liftPoint x.1 hx = sigmaPointι k (FixedPoint Φ m) x :=
  Fork.IsLimit.hom_ext (ofGraphFixedLocus hΦ hm K v).isLimit
    ((FixedLocus.liftPoint_ι _ _ _).trans (sigmaPointι_fixedPointsι Φ m x).symm)

end Correspondence

set_option linter.overlappingInstances false in
/-- **The trace formula on a proper scheme in degree `m`** (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Step 2): for a proper `X` with the model
Frobenius `Φ` and `m ≥ 1`, the trace formula in degree one holds for `Φ_m`. -/
theorem traceFormulaHolds_frobeniusIterate_of_isProper [IsAlgClosed k] [IsProper X.hom]
    [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p) [IsProper Φ.left] (hm : 1 ≤ m) :
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
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hc := Correspondence.isContractingAt_ofGraph_frobeniusIterate hΦ hm v x.1
    (by simpa [Correspondence.ofGraph] using x.2.symm)
  refine Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_isContractingAt _ v F x.1 hc
    (sigmaPointι k _ x) ?_
  rw [Correspondence.liftPoint_ofGraphFixedLocus hΦ hm K v x]
  ext y
  refine ⟨?_, fun hy ↦ ⟨(default : Spec (.of k)), hy.symm⟩⟩
  rintro ⟨z, rfl⟩
  rw [Set.mem_singleton_iff, Subsingleton.elim (α := Spec (.of k)) z default]

set_option linter.overlappingInstances false in
/-- **The trace formula on a proper scheme** (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Step 2, from
`theorem-proper-pushforward-lefschetz-verdier`, `proposition-frobenius-local-term-curve--1` and
`lemma-frobenius-fixed-scheme--1`): for a proper `X` with the model Frobenius `Φ` of a model over a
finite field, the trace formula in degree one holds. -/
theorem traceFormulaHolds_of_isProper [IsAlgClosed k] [IsProper X.hom]
    [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p) [IsProper Φ.left] :
    TraceFormulaHolds ℓ Φ := by
  have h := traceFormulaHolds_frobeniusIterate_of_isProper (ℓ := ℓ) hΦ le_rfl
  rwa [traceFormulaHolds_congr (frobeniusIterate_one Φ)] at h

end AlgebraicGeometry.ProEtale.CondensedRing
