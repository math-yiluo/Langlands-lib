/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FixedPointComponent
public import WeilConjectures.TraceFormula.SupportedRestriction

/-!

# The Frobenius local term through the supported restriction

Let `Φ` be the model Frobenius of `X = X₀ ×_{k₀} k` for a model `X₀` over a finite field `k₀`,
`m ≥ 1`, `v : LΦ_m^* K ⟶ K` an arbitrary map, and `c = (𝟙, Φ_m)` the graph correspondence with
coefficient `v`. Its fixed locus is a finite disjoint union of reduced points (blueprint
`lemma-frobenius-fixed-scheme`), so an open and closed subscheme `B` of the fixed locus with
underlying set a fixed point `y` is a copy of the base point
(`Correspondence.FixedLocus.isoPointOfRangeEq`), and the restriction of the supported restriction
`ρ_P`, `P = K ⊠ D_X K`, to `B` is its stalk at `y`: the supported restriction
`RΓ_a(T, P) ⟶ RΓ_y(X, LΔ^* P)` on the strict localization `T` of `X × X` at `(y, y)` of blueprint
`lemma-local-term-restriction-map`.

## Main statements

- `Correspondence.localTerm_traceClass_frobeniusGraph_eq_zero_of_supportedRestriction`:
  if the stalk at `y` of the supported restriction vanishes, so does the local term `LT_y(v)`
  (blueprint `lemma-local-term-restriction-map`, `lemma-vanishing-local-term-zero-stalk--2`, proof).
  By blueprint `lemma-vanishing-local-term-zero-stalk`, this applies on a smooth curve when
  `K_y = 0`.

The identity between the local term and the integral of the composite of the supported class,
the supported restriction and the evaluation holds for every correspondence
(`ProEtale.CondensedRing.Correspondence.localTerm_traceClass_eq_integral_supportedRestriction`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [IsAlgClosed k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

/-- **Vanishing of the Frobenius local term through the supported restriction** (blueprint
`lemma-local-term-restriction-map` and the proof of `lemma-vanishing-local-term-zero-stalk--2`): let
`Φ` be the model Frobenius of a model over a finite field, `m ≥ 1`, `v : LΦ_m^* K ⟶ K` an arbitrary
map, `z` a rational point of the fixed locus of the graph correspondence `(𝟙, Φ_m)`, and `B` an open
and closed subscheme of the fixed locus, proper over `s`, with underlying set `{z}`. If the stalk at
`z` of the supported restriction `ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P`, `P = K ⊠ D_X K`, is zero,
then the local term `LT_B(v)` is zero.

The fixed locus is a disjoint union of reduced points (blueprint `lemma-frobenius-fixed-scheme`), so
`B ≅ s` with `s ≅ B ⟶ Fix(c)` the point `z`, and the restriction of `ρ_P` to `B` vanishes; the
local term is the integral of a composite through this restriction
(`localTerm_traceClass_eq_integral_supportedRestriction`). -/
theorem localTerm_traceClass_frobeniusGraph_eq_zero_of_supportedRestriction {k₀ : Type u}
    [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base = {z.left.base (default : Spec (.of k))})
    (h : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction (externalProduct ℓ K (verdierDual ℓ K))) = 0) :
    ((ofGraph K (frobeniusIterate Φ m) v).traceClass F).localTerm j = 0 := by
  refine localTerm_traceClass_eq_zero_of_supportedRestriction _ F j
    (upperStar_map_eq_zero_of_inv_comp (FixedLocus.isoPointOfRangeEq j hΦ hm hB) j ?_)
  rw [FixedLocus.isoPointOfRangeEq_inv_comp_eq j hΦ hm z hB]
  exact h

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
