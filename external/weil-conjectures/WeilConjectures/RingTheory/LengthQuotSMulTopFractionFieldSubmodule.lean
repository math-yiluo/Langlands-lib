/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.LocalRing.Defs

import Mathlib.RingTheory.OrderOfVanishing.Basic
import WeilConjectures.RingTheory.LengthQuotSMulTopFGFractionFieldSubmodule

/-!
# Bounded length for a fraction-field submodule modulo a scalar

Source: Stacks Project, Algebra, Tag 00PE, `lemma-finite-length`
(blueprint: lem-weil-pbc-dim-one-submodule-quotient-finite-length).
-/

@[expose] public section

universe u v

namespace Submodule

private theorem length_quotSMulTop_le_of_fg
    {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    (x : R) (b : ℕ∞)
    (hfg : ∀ N : Submodule R V, N.FG → Module.length R (QuotSMulTop x N) ≤ b) :
    Module.length R (QuotSMulTop x V) ≤ b := by
  classical
  rw [← WithBot.coe_le_coe, Module.coe_length, Order.krullDim_eq_iSup_length,
    WithBot.coe_le_coe, iSup_le_iff]
  intro p
  have hw (i : Fin p.length) :
      ∃ m : V, (Submodule.Quotient.mk m : QuotSMulTop x V) ∈ p i.succ ∧
        (Submodule.Quotient.mk m : QuotSMulTop x V) ∉ p (Fin.castSucc i) := by
    obtain ⟨q, hq, hq'⟩ := IsConcreteLE.exists_of_lt
      (show p (Fin.castSucc i) < p i.succ from p.step i)
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨m, hq, hq'⟩
  choose m hm hm' using hw
  let N : Submodule R V := Submodule.span R (Set.range m)
  have hN : N.FG := Submodule.fg_span (Set.finite_range m)
  let f : QuotSMulTop x N →ₗ[R] QuotSMulTop x V := QuotSMulTop.map x N.subtype
  let q : LTSeries (Submodule R (QuotSMulTop x N)) :=
    { length := p.length
      toFun := fun i ↦ (p i).comap f
      step := fun i ↦ by
        apply lt_of_le_of_ne (Submodule.comap_mono (p.step i).le)
        intro he
        let z : N := ⟨m i, Submodule.subset_span (Set.mem_range_self i)⟩
        have hz : (Submodule.Quotient.mk z : QuotSMulTop x N) ∈
            (p i.succ).comap f := hm i
        have hz' : (Submodule.Quotient.mk z : QuotSMulTop x N) ∉
            (p (Fin.castSucc i)).comap f := hm' i
        exact hz' (he ▸ hz) }
  have hq : (q.length : ℕ∞) ≤ Module.length R (QuotSMulTop x N) := by
    rw [← WithBot.coe_le_coe, Module.coe_length]
    exact Order.LTSeries.length_le_krullDim q
  exact hq.trans (hfg N hN)

/-- Over a one-dimensional Noetherian local domain, reduction of any submodule of a finite
power of the fraction field modulo a nonzero scalar has bounded finite length.
Source: Stacks Project, Algebra, Tag 00PE, `lemma-finite-length`
(blueprint: lem-weil-pbc-dim-one-submodule-quotient-finite-length).

Proof (the node's nine steps):
1. The nonzero scalar is a nonzerodivisor. Dimension one and Noetherianity give finite length
   of `R/xR` by `lem-weil-pbc-dim-le-one-principal-quotient-finite-length`; write its length as l.
2. If x is a unit, `xM = M`, so the quotient has length zero (`def-weil-pbc-module-length`).
3. Replace the ambient space by the K-span of M, of dimension r' at most r. A basis identifies
   it with `K^r'` and preserves the quotient length (`def-weil-pbc-module-length`). The case
   r' = 0 is immediate. Treat finite M first, then arbitrary M.
4. For finite M, clear denominators by a nonzero scalar, giving an isomorphic module inside
   `F = R^r'`, still spanning `K^r'`; the quotient length is unchanged.
5. Clearing denominators in expressions for the standard basis gives nonzero d with `dF ⊆ M`.
   Every prime containing d is maximal, by dimension one. Thus x is in the radical of dR
   (`lem-weil-pbc-zero-locus-eq-iff-radical-eq`), so `x^c F ⊆ M` for some c.
6. Cancellation of nonzero powers of x identifies each `x^i N/x^(i+1) N` with `N/xN`.
   Additivity (`lem-weil-pbc-length-additive-short-exact`) and induction give
   `length(N/x^n N) = n length(N/xN)`.
7. Coordinatewise reduction identifies `F/xF` with `(R/xR)^r'`. Additivity and induction give
   length r'l, and step 6 gives `length(F/x^n F) = nr'l`.
8. The inclusions `x^(n+c) F ⊆ x^n M ⊆ x^n F` and `x^n M ⊆ M ⊆ F`, together with
   additivity, bound `n length(M/xM)` above by `(n+c)r'l`. First this makes the length finite;
   then let n grow to obtain `length(M/xM) ≤ r'l ≤ rl`.
9. For arbitrary M, choose representatives of the k strict steps of any chain in `M/xM`.
   Their finite span M' gives, by inverse images, a strict chain of k steps in `M'/xM'`.
   The finite case gives `k ≤ rl`. Taking the supremum of all chain lengths gives the bound
   and finite length (`def-weil-pbc-module-length`). -/
theorem length_quotSMulTop_le_of_ringKrullDim_eq_one_of_isLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (r : ℕ) (M : Submodule R (Fin r → K)) (hdim : ringKrullDim R = 1)
    (x : R) (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x R) < ⊤ ∧
      Module.length R (QuotSMulTop x M) < ⊤ ∧
      Module.length R (QuotSMulTop x M) ≤ (r : ℕ∞) * Module.length R (QuotSMulTop x R) := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  have hlen : Module.length R (QuotSMulTop x R) < ⊤ := by
    have hfin := isFiniteLength_quotient_span_singleton R
      (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
    have he : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
      Submodule.quotEquivOfEq _ _ (by simp [← Submodule.ideal_span_singleton_smul])
    rw [he.length_eq]
    exact (Module.length_ne_top_iff.mpr hfin).lt_top
  have hbound : Module.length R (QuotSMulTop x M) ≤
      (r : ℕ∞) * Module.length R (QuotSMulTop x R) := by
    apply length_quotSMulTop_le_of_fg
    intro N hN
    let e := Submodule.equivMapOfInjective M.subtype M.subtype_injective N
    rw [(QuotSMulTop.congr x e).length_eq]
    exact length_quotSMulTop_le_of_fg_of_ringKrullDim_eq_one_of_isLocalRing
      r (N.map M.subtype) (hN.map _) hdim x hx
  exact ⟨hlen, lt_of_le_of_lt hbound (WithTop.mul_lt_top (ENat.natCast_lt_top r) hlen), hbound⟩

end Submodule

