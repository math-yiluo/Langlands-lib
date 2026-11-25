/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PieceAdditivity
public import WeilConjectures.TraceFormula.IntegralPointThickening
public import WeilConjectures.TraceFormula.StalkFrobeniusGraph

/-!

# Additivity of trace classes along the curve pieces of a Weil object

Let `(K, φ)` be a Weil object on `X` for `Φ`, `m ≥ 1`, `x` a rational point fixed by `Φ_m` and
`j : U ⟶ X` the open complement of `x`. The open–closed triangle
`K^U = j_! Lj^* K ⟶ K ⟶ K^Z = Rx_* Lx^* K ⟶` carries the coefficient maps `u^U`, `φ_m`, `u^Z` of
the graph correspondence `c_m = (𝟙, Φ_m)` (blueprint `proposition-frobenius-local-term-curve--1`),
and the trace classes are additive (blueprint `proposition-additivity-trace-classes--2`, item 2):
```
Tr_{c_m}(φ_m) = Tr_{c_m}(u^Z) + Tr_{c_m}(u^U),
```
and so are the local terms. As for the graph of an arbitrary endomorphism
(`WeilConjectures.TraceFormula.PieceAdditivity`), this is
`Correspondence.traceClass_eq_add_of_distTriang` for the open–closed triangle.

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.upperStar_map_unit_comp_closedPieceCoeff`: the
  closed piece coefficient is compatible with the unit `K ⟶ Rx_* Lx^* K`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.traceClass_graph_eq_add`: additivity of the
  trace classes along the curve pieces.
- `ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_add`: additivity
  of the local terms.

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

/-- The closed piece coefficient of a Weil object is the closed piece coefficient of the graph
correspondence of its Frobenius structure map. -/
lemma closedPieceCoeff_eq_graphClosedPieceCoeff (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    K.closedPieceCoeff m x hx =
      Correspondence.graphClosedPieceCoeff K.carrier (K.iterateStr m).hom hx :=
  Correspondence.ProperPushforwardDiagram.pushforwardCoeff_congr _ _
    (by rw [stalkFrobenius_eq_graphStalkMap]; rfl) _ _ _ _ _ _

/-- **The closed piece coefficient of a Weil object is compatible with the unit** (blueprint
`proposition-additivity-trace-classes--2`, proof of item 2, step (b)): for `x` fixed by `Φ_m`, the
closed piece coefficient `u^Z = [x, x]_! F_{x,m}` satisfies `u^Z ∘ LΦ_m^* η = η ∘ φ_m` for the unit
`η : K ⟶ Rx_* Lx^* K`, up to `R(𝟙)^! ≅ 𝟭`. -/
theorem upperStar_map_unit_comp_closedPieceCoeff (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (frobeniusIterate Φ m)).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).unit.app K.carrier) ≫
      K.closedPieceCoeff m x hx =
      (K.iterateStr m).hom ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ x).unit.app K.carrier ≫
        (boundedConstructibleUpperShriekId ℓ X).inv.app _ :=
  (congrArg (_ ≫ ·) (K.closedPieceCoeff_eq_graphClosedPieceCoeff m x hx)).trans
    (Correspondence.upperStar_map_unit_comp_graphClosedPieceCoeff K.carrier (K.iterateStr m).hom hx)

variable (K : WeilBoundedConstructible ℓ Φ) {U : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (j : U ⟶ X)
  [IsOpenImmersion j.left]

/-- **Additivity of trace classes along the curve pieces** (blueprint
`proposition-additivity-trace-classes--2`, item 2; `proposition-additivity-trace-classes--2` for the
Frobenius graph; `proposition-additivity-trace-classes`): for a rational point `x` fixed by `Φ_m`,
`m ≥ 1`, with open complement `j : U ⟶ X` such that `Φ_{m,U} ≫ j = j ≫ Φ_m` is cartesian, the trace
class of the graph correspondence `(𝟙, Φ_m)` with coefficient `φ_m` is the sum of the trace classes
with the coefficients `u^Z` of `K^Z` and `u^U` of `K^U`. -/
theorem traceClass_graph_eq_add (m : ℕ) (_hm : 1 ≤ m) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {ΦU : U ⟶ U}
    (sq : IsPullback ΦU j j (frobeniusIterate Φ m))
    (hcompl : IsCompl (Set.range j.left.base) (Set.range x.left.base))
    (F : (K.graph m).FixedLocus) :
    (K.graph m).traceClass F =
      F.traceClassWithCoeff _ (K.closedPieceCoeff m x hx) +
        F.traceClassWithCoeff _ (K.openPieceCoeff j m sq ≫
          (boundedConstructibleUpperShriekId ℓ X).inv.app _) := by
  refine (exists_distTriang_openImmersionLowerShriek_lowerStar
    (ℓ := ℓ) j x hcompl K.carrier).elim (fun δ hT ↦ ?_)
  have hu := comp_inv_app_eq_of_comp_eq (boundedConstructibleUpperShriekId ℓ X)
    (K.openPieceCoeff_comp_counit j m sq)
  have hz := eq_comp_inv_app_comp_map (boundedConstructibleUpperShriekId ℓ X)
    (K.upperStar_map_unit_comp_closedPieceCoeff m x hx)
  exact ((K.graph m).traceClass_eq_add_of_distTriang F hT
    (K.openPieceCoeff j m sq ≫ (boundedConstructibleUpperShriekId ℓ X).inv.app _)
    (K.closedPieceCoeff m x hx) hu hz
    (eq_zero_of_lowerShriek_graph (ℓ := ℓ) j x hcompl.disjoint
      ((boundedConstructibleUpperStar _ ℓ j).obj K.carrier)
      ((boundedConstructibleUpperStar _ ℓ x).obj K.carrier) (frobeniusIterate Φ m) hx)
    (eq_zero_of_externalProduct_openPiece (ℓ := ℓ) j x hcompl.disjoint
      ((boundedConstructibleUpperStar _ ℓ j).obj K.carrier)
      ((boundedConstructibleUpperStar _ ℓ x).obj K.carrier) K.carrier
      ((boundedConstructibleUpperStar _ ℓ j).obj K.carrier))
    (eq_zero_of_externalProduct_closedPiece (ℓ := ℓ) j x hcompl.disjoint
      ((boundedConstructibleUpperStar _ ℓ j).obj K.carrier)
      ((boundedConstructibleUpperStar _ ℓ x).obj K.carrier) K.carrier
      ((boundedConstructibleUpperStar _ ℓ x).obj K.carrier))
    (eq_zero_of_externalProduct_shift_to_diag (ℓ := ℓ) j x hcompl.disjoint
      ((boundedConstructibleUpperStar _ ℓ j).obj K.carrier)
      ((boundedConstructibleUpperStar _ ℓ x).obj K.carrier))).trans (add_comm _ _)

/-- **Additivity of local terms along the curve pieces** (blueprint
`proposition-additivity-trace-classes--2`, item 2): for every open and closed subscheme `B` of the
fixed locus, proper over `s`, `LT_B(φ_m) = LT_B(u^Z) + LT_B(u^U)`. -/
theorem localTerm_traceClass_graph_eq_add (m : ℕ) (hm : 1 ≤ m) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {ΦU : U ⟶ U}
    (sq : IsPullback ΦU j j (frobeniusIterate Φ m))
    (hcompl : IsCompl (Set.range j.left.base) (Set.range x.left.base))
    (F : (K.graph m).FixedLocus) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (jB : B ⟶ F.F) [IsOpenImmersion jB.left] [IsClosedImmersion jB.left] :
    ((K.graph m).traceClass F).localTerm jB =
      (F.traceClassWithCoeff _ (K.closedPieceCoeff m x hx)).localTerm jB +
        (F.traceClassWithCoeff _ (K.openPieceCoeff j m sq ≫
          (boundedConstructibleUpperShriekId ℓ X).inv.app _)).localTerm jB := by
  exact (congrArg (fun α ↦ BorelMooreSection.localTerm jB α)
    (K.traceClass_graph_eq_add j m hm x hx sq hcompl F)).trans
    (BorelMooreSection.localTerm_add jB _ _)

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
