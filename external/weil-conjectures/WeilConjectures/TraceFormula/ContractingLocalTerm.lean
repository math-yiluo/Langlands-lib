/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingAdditivity
public import WeilConjectures.TraceFormula.Specialization.Vanishing
import WeilConjectures.TraceFormula.ProperCompatibility

/-!

# Local terms of contracting correspondences

Varshavsky's theorem for contracting correspondences (blueprint
`theorem-contracting-correspondences-local-terms`, for `Z = {x}`;
`ProEtale.CondensedRing.Correspondence.restrict_traceClass_eq_pushforward_of_isContractingAt`):
if `c` is contracting at the `k`-point `y` of the fixed locus, the trace class of `c` on an open
and closed subscheme `B` of the fixed locus with underlying set `{y}` is the pushforward of the
trace class of the restricted coefficient map `u_Z : K_x ⟶ K_x`
(`Correspondence.contractingStalkMap`).

The proof follows the blueprint (`theorem-contracting-correspondences-local-terms`):
* the additivity of trace classes along the pieces `K^U = j_! Lj^* K` and `K^Z = Rx_* Lx^* K`
  (`Correspondence.traceClass_eq_add_of_isPullback`);
* the proper pushforward compatibility of trace classes for the closed piece
  (`Correspondence.ProperPushforwardDiagram.traceClassPushforward_eq`);
* the vanishing of the trace class on `B` for coefficients with zero stalk at `x`, applied to the
  open piece (`Correspondence.restrict_traceClass_eq_zero_of_isContractingAt`, blueprint
  `theorem-contracting-correspondences-local-terms`, proved by specialization to the normal cone in
  `WeilConjectures.TraceFormula.Specialization.Vanishing`).

As consequences, the local term at a contracting fixed point with zero stalk vanishes
(`Correspondence.localTerm_traceClass_eq_zero_of_isContractingAt`, blueprint
`corollary-contracting-local-terms-point`, item 2), in particular for the graph of a Frobenius
(`Correspondence.localTerm_traceClass_frobeniusGraph_eq_zero`, item 3).

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

variable (c : Correspondence ℓ K)

/-- **Contracting correspondences and local terms** (blueprint
`theorem-contracting-correspondences-local-terms`, for the closed subscheme `Z = {x}` of the
rational point `x = c₁(y)`; Varshavsky, *Lefschetz–Verdier trace formula and a generalization of a
theorem of Fujiwara*, Thm. 2.1.3): let `c` be contracting at `y`, so that `C_Z = c₁⁻¹(x)` is the
reduced point `y`, the correspondence `c_Z` induced on `Z` is the identity correspondence of the
point and the restricted coefficient map is `u_Z = contractingStalkMap hc`. For an open and closed
subscheme `B` of the fixed locus, proper over `s`, with underlying set `{y}` and point `e : s ⟶ B`,
the restriction of the trace class of `c` to `B` is the pushforward along `e` of the trace class of
`u_Z`: `Tr_c(u)|_B = e_* Tr_{c_Z}(u_Z)`.

This is the blueprint proof (`theorem-contracting-correspondences-local-terms`): by additivity
(`traceClass_eq_add_of_isPullback`) the trace class is the sum of the trace classes of the
coefficient maps `u^Z = [x, y]_! u_Z` on `K^Z` and `u^U` on `K^U`; the first is the pushforward
of the trace class of `u_Z` along the induced map of fixed loci by proper pushforward
compatibility (`ProperPushforwardDiagram.traceClassPushforward_eq`), and the second vanishes on
`B` since `K^U` has zero stalk at `x` (`restrict_traceClass_eq_zero_of_isContractingAt`). -/
theorem restrict_traceClass_eq_pushforward_of_isContractingAt (F : c.FixedLocus)
    {y : RationalPoint c.C} (hc : c.IsContractingAt y) {B : Over (Spec (.of k))}
    [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    [IsClosedImmersion j.left] (e : point k ⟶ B) [IsProper e.left]
    (he : e ≫ j = F.liftPoint y hc.comp_c₁_eq_comp_c₂)
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))}) :
    (c.traceClass F).restrict j = BorelMooreSection.pushforward e
      ((ofEnd _ (contractingStalkMap hc)).traceClass (fixedLocusOfEnd _)) := by
  have hle := preimage_pointComplOpens_le_of_isPullback hc.comp_c₁_eq_comp_c₂ hc.isPullback
  have hc' : (c.withCoeff (pointOpenPiece K (y ≫ c.c₁))
      (c.pointOpenPieceCoeff (y ≫ c.c₁) hle)).IsContractingAt y := ⟨hc.1, hc.2, hc.3⟩
  have hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (y ≫ c.c₁)).obj (pointOpenPiece K (y ≫ c.c₁))) :=
    isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ
      (pointComplι (y ≫ c.c₁)) _ (isCompl_range_pointComplι _).disjoint _
  have hU : (F.traceClassWithCoeff _ (c.pointOpenPieceCoeff (y ≫ c.c₁) hle)).restrict j = 0 :=
    restrict_traceClass_eq_zero_of_isContractingAt
      (c.withCoeff (pointOpenPiece K (y ≫ c.c₁)) (c.pointOpenPieceCoeff (y ≫ c.c₁) hle))
      (F.withCoeff _ _) hc' j hB hK
  let P := restrictedClosedPieceDiagram hc.comp_c₁_eq_comp_c₂ hc.isPullback
  let Fc := fixedLocusOfEnd (contractingStalkMap hc)
  let Fb : P.pushforward.FixedLocus := F.withCoeff _ P.pushforwardCoeff
  have : IsProper (e ≫ j).left := by
    rw [Over.comp_left]
    infer_instance
  have hfix : P.fixMap Fc Fb = e ≫ j := by
    rw [he]
    refine Fb.hom_ext ?_
    rw [P.fixMap_ι]
    exact (Category.id_comp y).trans (F.liftPoint_ι y _).symm
  have hZ := P.traceClassPushforward_eq Fc Fb
  rw [ProperPushforwardDiagram.traceClassPushforward, BorelMooreSection.pushforward_congr hfix,
    ← BorelMooreSection.pushforward_comp] at hZ
  rw [traceClass_eq_add_of_isPullback c F hc.comp_c₁_eq_comp_c₂ hc.isPullback,
    BorelMooreSection.restrict_add, hU, add_zero]
  change (P.pushforward.traceClass Fb).restrict j = _
  rw [← hZ, BorelMooreSection.restrict_pushforward_self]

/-- **Zero-stalk vanishing of local terms** (blueprint `corollary-contracting-local-terms-point`,
item 2; Varshavsky, Thm. 2.1.3): if `c` is contracting at the fixed point `y`, `B` is an open and
closed subscheme of the fixed locus, proper over `s`, whose underlying set is `{y}`, and the stalk
`K_{c₁ y}` vanishes, then the local term of the trace class of `c` along `B` is zero, whatever
the coefficient map `u`: the restriction of the trace class to `B` vanishes
(`restrict_traceClass_eq_zero_of_isContractingAt`). -/
theorem localTerm_traceClass_eq_zero_of_isContractingAt (F : c.FixedLocus)
    (y : RationalPoint c.C) (hc : c.IsContractingAt y) {B : Over (Spec (.of k))}
    [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))})
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (y ≫ c.c₁)).obj K)) :
    (c.traceClass F).localTerm j = 0 := by
  rw [BorelMooreSection.localTerm,
    restrict_traceClass_eq_zero_of_isContractingAt c F hc j hB hK]
  exact BorelMooreSection.integral_zero

variable {c}

/-- **Zero-stalk vanishing for the Frobenius graph** (blueprint
`corollary-contracting-local-terms-point`, item 3): let `Φ` be the model Frobenius of a model `X₀`
of finite type over a finite field `k₀`, `m ≥ 1`, let `v : LΦ_m^* K ⟶ K` be an arbitrary, not
necessarily invertible, map (for instance the iterate `ψ_m` of a Frobenius coefficient morphism `ψ`,
or `φ_m` for a Weil object) and `x` a rational point fixed by `Φ_m`. If the stalk `K_x` vanishes,
the local term of the graph correspondence `(𝟙, Φ_m)` with coefficient map `v` along an open and
closed subscheme `B` of the fixed locus, proper over `s`, with underlying set `{x}`, is zero.
The graph is contracting at `x` since `Φ_m^♯ (t_i - a_i) = (t_i - a_i)^{q^m}` in affine
coordinates, and the claim is item 2. -/
theorem localTerm_traceClass_frobeniusGraph_eq_zero {k₀ : Type u} [Field k₀] [Finite k₀]
    [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀]
    {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (x : RationalPoint X)
    (hx : x ≫ (ofGraph K (frobeniusIterate Φ m) v).c₁ = x ≫ (ofGraph K (frobeniusIterate Φ m) v).c₂)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base = {(F.liftPoint x hx).left.base (default : Spec (.of k))})
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :
    ((ofGraph K (frobeniusIterate Φ m) v).traceClass F).localTerm j = 0 := by
  have hc := isContractingAt_ofGraph_frobeniusIterate hΦ hm v x hx
  refine localTerm_traceClass_eq_zero_of_isContractingAt _ F x hc j hB ?_
  have h₁ : x ≫ (ofGraph K (frobeniusIterate Φ m) v).c₁ = x := Category.comp_id x
  rw [h₁]
  exact hK

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
