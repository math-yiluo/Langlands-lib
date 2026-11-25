/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ClosedPieceSquare
public import WeilConjectures.TraceFormula.ClosedPieceTriangle
public import WeilConjectures.TraceFormula.OpenPieceTriangle
public import WeilConjectures.TraceFormula.PieceVanishing
public import WeilConjectures.TraceFormula.TraceClassTriangle

/-!

# Additivity of trace classes along the pieces of a fixed point

Let `h : X ⟶ X` be an endomorphism, `x` a rational point fixed by `h` and `j : U ⟶ X` the open
complement of `x`. A coefficient map `v : Lh^* K ⟶ K` of the graph correspondence `(𝟙, h)`
induces coefficient maps `u^U` on `K^U = j_! Lj^* K` and `u^Z` on `K^Z = Rx_* Lx^* K` which form,
with `v`, a morphism of the open–closed triangle `K^U ⟶ K ⟶ K^Z ⟶`, and the trace classes are
additive (blueprint `proposition-additivity-trace-classes--2`):
```
Tr_{(𝟙, h)}(v) = Tr_{(𝟙, h)}(u^Z) + Tr_{(𝟙, h)}(u^U).
```
This is `Correspondence.traceClass_eq_add_of_distTriang` for the open–closed triangle; the corner
morphism groups vanish by `WeilConjectures.TraceFormula.PieceVanishing` since `x` is fixed by
`h`.

## Main statements

- `ProEtale.CondensedRing.Correspondence.traceClass_ofGraph_eq_add`: item 1 of
  `proposition-additivity-trace-classes--2` for the graph of `h` and `Z = {x}`.

The curve pieces of a Weil object (item 2) are in
`WeilConjectures.TraceFormula.CurvePiecesAdditivity`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {D : Type*} [Category D] {R : D ⥤ D} (ι : R ≅ 𝟭 D)

/-- Moving `ι⁻¹ : 𝟭 ≅ R` across a commutative square: if `g ≫ ε = a₁ ≫ a₂`, the two composites
```
T --a₁--> M --a₂--> K --ι⁻¹--> R K
T --g--> K' --ι⁻¹--> R K' --R ε--> R K
```
agree. -/
lemma comp_inv_app_eq_of_comp_eq {T M K' K : D} {a₁ : T ⟶ M} {a₂ : M ⟶ K} {g : T ⟶ K'}
    {ε : K' ⟶ K} (h : g ≫ ε = a₁ ≫ a₂) :
    a₁ ≫ a₂ ≫ ι.inv.app K = (g ≫ ι.inv.app K') ≫ R.map ε := by
  have hn := ι.inv.naturality ε
  dsimp only [Functor.id_obj, Functor.id_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc g, h, Category.assoc]

/-- Moving `ι⁻¹ : 𝟭 ≅ R` across a morphism: if `p` is the composite
`T --v--> K --η--> K'' --ι⁻¹--> R K''`, it is also the composite
`T --v--> K --ι⁻¹--> R K --R η--> R K''`. -/
lemma eq_comp_inv_app_comp_map {T K K'' : D} {p : T ⟶ R.obj K''} {v : T ⟶ K} {η : K ⟶ K''}
    (h : p = v ≫ η ≫ ι.inv.app K'') : p = (v ≫ ι.inv.app K) ≫ R.map η := by
  have hn := ι.inv.naturality η
  dsimp only [Functor.id_obj, Functor.id_map] at hn
  rw [h, Category.assoc, hn]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace Correspondence

variable (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) {h : X ⟶ X}
  (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
  {x : RationalPoint X} (hx : x ≫ h = x)

/-- **Additivity of trace classes along the pieces of a fixed point** (blueprint
`proposition-additivity-trace-classes--2`, item 1, and `proposition-additivity-trace-classes--2`,
for the graph correspondence `(𝟙, h)` and the `c`-invariant closed subscheme `Z = {x}` of a rational
point fixed by `h`; Varshavsky, Prop. 1.5.10 after SGA 5, III 4.13): the trace class of
`v : Lh^* K ⟶ K` is the sum of the trace classes of the induced coefficient maps
`u^Z = [x, x]_! v_x` on `K^Z = Rx_* Lx^* K` and `u^U = [j]_! (v|_U)` on `K^U = j_! Lj^* K`.
No invertibility of `v` is required. -/
theorem traceClass_ofGraph_eq_add (F : (ofGraph K h v).FixedLocus) :
    (ofGraph K h v).traceClass F =
      F.traceClassWithCoeff _ (graphClosedPieceCoeff K v hx) +
        F.traceClassWithCoeff _ (graphOpenPieceCoeff K v hx ≫
          (boundedConstructibleUpperShriekId ℓ X).inv.app _) := by
  have hjx := (isCompl_range_pointComplι x).disjoint
  obtain ⟨δ, hT⟩ := exists_distTriang_pointComplι_rationalPoint x K
  rw [add_comm]
  refine (ofGraph K h v).traceClass_eq_add_of_distTriang F hT _ _ ?_ ?_
    (eq_zero_of_lowerShriek_graph (pointComplι x) x hjx _ _ h hx)
    (eq_zero_of_externalProduct_openPiece (pointComplι x) x hjx _ _ K _)
    (eq_zero_of_externalProduct_closedPiece (pointComplι x) x hjx _ _ K _)
    (eq_zero_of_externalProduct_shift_to_diag (pointComplι x) x hjx _ _)
  · exact comp_inv_app_eq_of_comp_eq (boundedConstructibleUpperShriekId ℓ X)
      (graphOpenPieceCoeff_comp_counit K v hx)
  · exact eq_comp_inv_app_comp_map (boundedConstructibleUpperShriekId ℓ X)
      (upperStar_map_unit_comp_graphClosedPieceCoeff K v hx)

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
