/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingGraph
public import WeilConjectures.TraceFormula.PointComplement
public import WeilConjectures.TraceFormula.PointNormalization
public import WeilConjectures.TraceFormula.ProperCompatibility
public import WeilConjectures.TraceFormula.StalkFrobeniusGraph
public import WeilConjectures.TraceFormula.TraceClassAdditivity

/-!

# The local term of the Frobenius correspondence at a fixed point

Let `(K, φ)` be a Weil object on `X` for the model Frobenius `Φ`, `m ≥ 1`, and let `x` be a
rational point fixed by `Φ_m`. For an open and closed subscheme `B` of the fixed locus of the
graph correspondence `c_m = (𝟙, Φ_m)` with underlying set `{x}`, the local term of the trace
class of `φ_m` along `B` is the trace of the local Frobenius `F_{x,m}` (blueprint
`proposition-frobenius-local-term-curve--1`, `proposition-frobenius-local-term-curve`). The graph of
the Frobenius is contracting at `x`, so by Varshavsky's theorem for contracting correspondences the
local term is the trace of the stalk map of `φ_m` at `x`
(`Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_isContractingAt`), which is the local
Frobenius (`WeilBoundedConstructible.stalkFrobenius_eq_graphStalkMap`, in
`WeilConjectures.TraceFormula.StalkFrobeniusGraph`). The main trace formula does not use this
file: on curves it takes the Frobenius local term from the SGA 5 III B curve route (blueprint
`corollary-contracting-local-terms-point`, item 3,
`Correspondence.localTerm_traceClass_frobeniusGraph_eq_trace_of_smooth`).

With `j : U = X ∖ {x} ⟶ X` the open complement of `x`, the local terms are then additive along
the curve pieces `K^U = j_! Lj^* K` and `K^Z = Rx_* Lx^* K` (blueprint
`proposition-additivity-trace-classes--2`, item 2, at an isolated fixed point): the open piece
contributes zero, its stalk at `x` vanishing
(`WeilBoundedConstructible.localTerm_traceClassWithCoeff_openPieceCoeff_eq_zero`), and the trace
class of the closed piece is the Borel–Moore pushforward of the trace class of the local
Frobenius on the point, whose local term along `B` is `tr(F_{x,m})`
(`WeilBoundedConstructible.localTerm_traceClassWithCoeff_closedPieceCoeff`).

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_trace`: the
  local term of the Frobenius correspondence at a fixed point is the trace of the local
  Frobenius.
- `ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_add_of_range_eq`:
  at the component `{x}` of the fixed locus, the local term is additive along the curve pieces,
  without the trace-class additivity.

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

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X}

/-- **The closed piece of the Frobenius local term** (blueprint
`proposition-frobenius-local-term-curve--1`, Step 3): the local term along `B` of the trace class of
the closed piece coefficient `u^Z = [x, x]_! F_{x,m}` is the trace of the local Frobenius `F_{x,m}`.
The trace class of `u^Z` is the pushforward `h_* Tr(F_{x,m})` along the inclusion `h : s ⟶ Fix(c_m)`
of the point `x` (`Correspondence.ProperPushforwardDiagram.traceClassPushforward_eq`), whose local
term along `B ∋ x` is `∫_s Tr(F_{x,m}) = tr(F_{x,m})`
(`Correspondence.integral_traceClass_ofEnd`). -/
theorem localTerm_traceClassWithCoeff_closedPieceCoeff (K : WeilBoundedConstructible ℓ Φ)
    (m : ℕ) (F : (K.graph m).FixedLocus) [IsProper F.F.hom] (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(K.fixedLocusPoint m F x hx).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)] :
    (F.traceClassWithCoeff _ (K.closedPieceCoeff m x hx)).localTerm j =
      End.of (trace (K.stalkFrobenius m x hx)) := by
  let P := K.closedPieceDiagram m x hx
  let Fc : (K.stalkCorrespondence m x hx).FixedLocus :=
    Correspondence.fixedLocusOfEnd (K.stalkFrobenius m x hx)
  let Fb : P.pushforward.FixedLocus := F.withCoeff _ (K.closedPieceCoeff m x hx)
  have hfix : P.fixMap Fc Fb = K.fixedLocusPoint m F x hx := by
    refine Fb.hom_ext ?_
    rw [P.fixMap_ι]
    exact (Category.id_comp x).trans (F.lift_ι x ((Category.comp_id x).trans hx.symm)).symm
  have hrange : Set.range (P.fixMap Fc Fb).left.base ⊆ Set.range j.left.base := by
    rw [hB, hfix]
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of k)) z default]
    rfl
  have h := P.traceClassPushforward_eq Fc Fb
  rw [Correspondence.ProperPushforwardDiagram.traceClassPushforward] at h
  refine (congrArg (BorelMooreSection.localTerm j) h.symm).trans ?_
  rw [BorelMooreSection.localTerm_pushforward j _ hrange]
  exact Correspondence.integral_traceClass_ofEnd _

/-- **The open piece of the Frobenius local term vanishes** (blueprint
`proposition-frobenius-local-term-curve--1`, Step 2): the stalk of `K^U = j_! Lj^* K` at the point
`x ∉ U` vanishes, so the local term along `B` of the trace class of the open piece coefficient `u^U`
is zero by the zero-stalk vanishing for the Frobenius graph
(`Correspondence.localTerm_traceClass_frobeniusGraph_eq_zero`). -/
theorem localTerm_traceClassWithCoeff_openPieceCoeff_eq_zero {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀} (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructible ℓ Φ) {m : ℕ} (hm : 1 ≤ m) {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (jU : U ⟶ X)
    [IsOpenImmersion jU.left] {ΦU : U ⟶ U} (sq : IsPullback ΦU jU jU (frobeniusIterate Φ m))
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x)
    (hxU : Disjoint (Set.range jU.left.base) (Set.range x.left.base))
    (F : (K.graph m).FixedLocus) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(K.fixedLocusPoint m F x hx).left.base (default : Spec (.of k))}) :
    (F.traceClassWithCoeff _ (K.openPieceCoeff jU m sq ≫
      (boundedConstructibleUpperShriekId ℓ X).inv.app _)).localTerm j = 0 :=
  Correspondence.localTerm_traceClass_frobeniusGraph_eq_zero hΦ hm (K.openPieceCoeff jU m sq)
    (F.withCoeff _ _) x ((Category.comp_id x).trans hx.symm) j hB
    (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ jU x hxU _)

/-- **The local term of the Frobenius correspondence** (blueprint
`proposition-frobenius-local-term-curve--1`): let `Φ` be the model Frobenius of a model `X₀` over a
finite field, let `x` be a rational point fixed by `Φ_m`, `m ≥ 1`, and let `j : B ⟶ Fix(c_m)` be an
open and closed subscheme of the fixed locus of the graph correspondence, proper over `s`, whose
underlying set is the point `x`. Then the local term of the trace class of `φ_m` along `B` is the
trace of the local Frobenius `F_{x,m}` on the geometric stalk `K_x̄`. No local constancy of `K`
at `x` is assumed.

The graph `(𝟙, Φ_m)` is contracting at `x`
(`Correspondence.isContractingAt_ofGraph_frobeniusIterate`), so by Varshavsky's theorem the
local term is the trace of the stalk map of `φ_m`
(`Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_isContractingAt`), which is the local
Frobenius (`stalkFrobenius_eq_graphStalkMap`). -/
theorem localTerm_traceClass_graph_eq_trace {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]
    {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}
    (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructible ℓ Φ) {m : ℕ} (hm : 1 ≤ m) (F : (K.graph m).FixedLocus)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(K.fixedLocusPoint m F x hx).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)] :
    ((K.graph m).traceClass F).localTerm j = End.of (trace (K.stalkFrobenius m x hx)) := by
  have hc := Correspondence.isContractingAt_ofGraph_frobeniusIterate hΦ hm (K.iterateStr m).hom x
    ((Category.comp_id x).trans hx.symm)
  rw [stalkFrobenius_eq_graphStalkMap]
  exact Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_isContractingAt
    (frobeniusIterate Φ m) (K.iterateStr m).hom F x hc j hB

/-- **Additivity of the Frobenius local term at an isolated fixed point** (blueprint
`proposition-additivity-trace-classes--2`, item 2, local terms, the case of the component `β = {x}`;
the statement for every component is `localTerm_traceClass_graph_eq_add`): let
`Φ` be the model Frobenius of a model over a finite field, `m ≥ 1`, `x` a rational point fixed
by `Φ_m` with open complement `jU : U ⟶ X` (with `Φ_{m,U} ≫ jU = jU ≫ Φ_m` cartesian), and
`j : B ⟶ Fix(c_m)` an open and closed subscheme of the fixed locus, proper over `s`, with
underlying set `{x}`. Then the local terms along `B` are additive along the open–closed triangle
`K^U ⟶ K ⟶ K^Z ⟶`: `LT_B(φ_m) = LT_B(u^Z) + LT_B(u^U)`. Both sides are `tr(F_{x,m})`: the left
by `localTerm_traceClass_graph_eq_trace`, the closed piece by
`localTerm_traceClassWithCoeff_closedPieceCoeff` and the open piece vanishes
(`localTerm_traceClassWithCoeff_openPieceCoeff_eq_zero`). -/
theorem localTerm_traceClass_graph_eq_add_of_range_eq {k₀ : Type u} [Field k₀] [Finite k₀]
    [Algebra k₀ k]
    {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀}
    (hΦ : IsModelFrobenius Φ f₀ p) (K : WeilBoundedConstructible ℓ Φ) {m : ℕ} (hm : 1 ≤ m)
    {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated U.hom] (jU : U ⟶ X) [IsOpenImmersion jU.left] {ΦU : U ⟶ U}
    (sq : IsPullback ΦU jU jU (frobeniusIterate Φ m)) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x)
    (hxU : Disjoint (Set.range jU.left.base) (Set.range x.left.base))
    (F : (K.graph m).FixedLocus) [IsProper F.F.hom] {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(K.fixedLocusPoint m F x hx).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)] :
    ((K.graph m).traceClass F).localTerm j =
      (F.traceClassWithCoeff _ (K.closedPieceCoeff m x hx)).localTerm j +
        (F.traceClassWithCoeff _ (K.openPieceCoeff jU m sq ≫
          (boundedConstructibleUpperShriekId ℓ X).inv.app _)).localTerm j := by
  have hZ := localTerm_traceClassWithCoeff_closedPieceCoeff K m F x hx j hB
  have hU := localTerm_traceClassWithCoeff_openPieceCoeff_eq_zero hΦ K hm jU sq x hx hxU F j hB
  exact (localTerm_traceClass_graph_eq_trace hΦ K hm F x hx j hB).trans
    ((add_zero _).symm.trans (congrArg₂ (· + ·) hZ.symm hU.symm))

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
