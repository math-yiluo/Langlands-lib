/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FixedPointComponent
public import WeilConjectures.TraceFormula.FixedPointScheme
public import WeilConjectures.TraceFormula.SupportedRestriction

/-!

# The Frobenius local term at a fixed point as a restriction map

Let `Φ` be the model Frobenius of `X = X₀ ×_{k₀} k` for a model `X₀` over a finite field `k₀`,
`m ≥ 1`, `v : LΦ_m^* K ⟶ K` an arbitrary map, and `c = (𝟙, Φ_m)` the graph correspondence with
coefficient `v`. Every rational point `y` of the fixed locus `Fix(c)` is open and closed in
`Fix(c)` (the fixed locus is a finite disjoint union of reduced points, blueprint
`lemma-frobenius-fixed-scheme`), so the local term `LT_y(v)` at `y` is defined, and it is the
composite of the stalks at `y` of the supported class `[v]`, the supported restriction `ρ_P` from
graph-supported to `y`-supported cohomology and the evaluation (blueprint
`lemma-local-term-restriction-map`).

## Main statements

- `ProEtale.CondensedRing.Correspondence.FixedLocus.isOpenImmersion_left_of_isModelFrobenius`,
  `ProEtale.CondensedRing.Correspondence.FixedLocus.isClosedImmersion_left`: a rational point of
  the Frobenius fixed locus is an open and closed immersion.
- `Correspondence.localTerm_traceClass_frobeniusGraph_eq_supportedRestriction`: the local
  term at a fixed point of the Frobenius graph correspondence through the supported restriction
  (blueprint `lemma-local-term-restriction-map`).

## Implementation notes

As in `WeilConjectures.TraceFormula.SupportedRestriction`, the product factors are in the order
`P = K ⊠ D_X K` of the library and the graph is `(𝟙, Φ_m)`; the blueprint uses the transposed
graph `γ = (Φ_m, 𝟙)` and `D_X K ⊠ K`. The coefficients are `ℚ̄_ℓ`. The stalk at `y` of the source
`Rc^! P` of `ρ_P` is the graph-supported cohomology `RΓ_Γ(T, P)` on the strict localization `T` of
`X × X` at `(y, y)`, the stalk of its target `Rd^! LΔ^* P` is `RΓ_y(X, LΔ^* P)`, and the final
isomorphisms are `RΓ_y(X, ω_X) ≅ RΓ(y, ω_y)` followed by `∫_y`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [IsAlgClosed k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X} {m : ℕ}

namespace Correspondence

omit [IsAlgClosed k] in
/-- A rational point of the fixed locus of any correspondence is a closed immersion: it is a
section of the separated structure morphism of the fixed locus. -/
lemma FixedLocus.isClosedImmersion_left {c : Correspondence ℓ K} (F : c.FixedLocus)
    (y : RationalPoint F.F) : IsClosedImmersion y.left := by
  have h : IsClosedImmersion (y.left ≫ F.F.hom) := by
    rw [Over.w y]
    exact inferInstanceAs (IsClosedImmersion (𝟙 (Spec (.of k))))
  exact IsClosedImmersion.of_comp y.left F.F.hom

/-- A rational point of the fixed locus of the graph correspondence `(𝟙, Φ_m)` of the model
Frobenius, `m ≥ 1`, is an open immersion: the fixed locus is a finite disjoint union of reduced
points (blueprint `lemma-frobenius-fixed-scheme`). -/
lemma FixedLocus.isOpenImmersion_left_of_isModelFrobenius (hΦ : IsModelFrobenius Φ f₀ p)
    (hm : 1 ≤ m) {v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K}
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (y : RationalPoint F.F) :
    IsOpenImmersion y.left := by
  obtain ⟨g, hg, hrange⟩ :=
    F.exists_isOpenImmersion_rationalPoint hΦ hm (y.left.base (default : Spec (.of k)))
  have hgy : g = y := by
    refine rationalPoint_ext ?_
    have hmem : g.left.base (IsLocalRing.closedPoint k) ∈ Set.range g.left.base := ⟨_, rfl⟩
    rw [hrange] at hmem
    exact hmem.trans (congrArg y.left.base (Subsingleton.elim (α := Spec (.of k)) _ _))
  exact hgy ▸ hg

/-- **The Frobenius local term as a restriction map** (blueprint
`lemma-local-term-restriction-map`): let `Φ` be the model Frobenius of a model over a finite
field, `m ≥ 1`, `v : LΦ_m^* K ⟶ K` an arbitrary map and `y` a rational point of the fixed locus
of the graph correspondence `c = (𝟙, Φ_m)`, that is a fixed point of `Φ_m`. Then `y` is open and
closed in the fixed locus, and the local term `LT_y(v)` is the composite in `End(ℚ̄_ℓ,s)`
```
ℚ̄_ℓ,s ≅ (ℚ̄_ℓ,C)_y --[v]_y--> (Rc^! P)_y --(ρ_P)_y--> (Rd^! LΔ^* P)_y --ev_y--> (ω_Fix(c))_y
  ≅ Ry^! ω_Fix(c) ≅ ω_s ≅ ℚ̄_ℓ,s
```
of the stalks at `y` of the class `[v]` of `v` in graph-supported cohomology (the mate of `v`
read through external duality `𝓗_c(K) ≅ Rc^! P`), the restriction `ρ_P` from graph-supported to
`y`-supported cohomology and the evaluation `ev_K`, `P = K ⊠ D_X K`; here
`(Rc^! P)_y = RΓ_Γ(T, P)` and `(Rd^! LΔ^* P)_y = RΓ_y(X, LΔ^* P)` on the strict localization `T`
of `X × X` at `(y, y)`, and the last isomorphisms are `RΓ_y(X, ω_X) ≅ RΓ(y, ω_y)` followed by
`∫_y`. -/
theorem localTerm_traceClass_frobeniusGraph_eq_supportedRestriction
    (hΦ : IsModelFrobenius Φ f₀ p) (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (y : RationalPoint F.F) :
    haveI := F.isOpenImmersion_left_of_isModelFrobenius hΦ hm y
    haveI := F.isClosedImmersion_left y
    ((ofGraph K (frobeniusIterate Φ m) v).traceClass F).localTerm y =
      .of ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ y)).hom ≫
        (boundedConstructibleUpperStar _ ℓ y).map
          ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
            (boundedConstructibleUpperStar _ ℓ F.ι).map
              ((ofGraph K (frobeniusIterate Φ m) v).mate ≫
                (ofGraph K (frobeniusIterate Φ m) v).verdierDualityIso.hom)) ≫
        (boundedConstructibleUpperStar _ ℓ y).map (F.supportedRestriction _) ≫
        (boundedConstructibleUpperStar _ ℓ y).map F.supportedEvaluation ≫
        (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ y).inv.app _ ≫
        (dualizingComplexComp ℓ y).hom ≫ (dualizingComplexPointIso ℓ k).hom) :=
  haveI := F.isOpenImmersion_left_of_isModelFrobenius hΦ hm y
  haveI := F.isClosedImmersion_left y
  localTerm_point_traceClass_eq_supportedRestriction _ F y

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
