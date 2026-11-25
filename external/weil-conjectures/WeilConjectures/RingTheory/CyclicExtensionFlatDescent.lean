/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.RingTheory.IdealPowerHomLift
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Descent of extensions of cyclic ideal-power quotients

Source: Stacks Project, More on Algebra, Lemma 05EG, the case `M = R/I^n`
(blueprint: lem-weil-pbc-cyclic-extension-flat-descent).

Base change is written `S ⊗[R] M`, as in `LinearMap.baseChange`; tensor symmetry identifies
this with the source's `M ⊗[R] S`. Short exactness is expressed by injectivity, `Function.Exact`,
and surjectivity, the module interpretation of `CategoryTheory.ShortComplex.ShortExact`
via `ShortExact.moduleCat_exact_iff_function_exact` and its injective/surjective lemmas.
-/

@[expose] public section

universe u v w x

open TensorProduct

namespace LinearMap

/-- An extension of a cyclic ideal-power quotient descends along a flat neighbourhood.
Source: Stacks Project, More on Algebra, Lemma 05EG, second paragraph of the proof
(blueprint: lem-weil-pbc-cyclic-extension-flat-descent).

Proof:
1. Lift `1 ⊗ 1` to `τ` in the given extension. Exactness and injectivity give
   the unique map `d : I^n → S ⊗ N` satisfying `a (d r) = r • τ`.
2. Apply `exists_ideal_power_hom_lift` to obtain `l : I^n → N` and `m` with
   `1 ⊗ l(r) = d(r) + r • m`. Replace `τ` by `τ + a(m)`.
3. Construct `E = (N × R) / range (r ↦ (l(r), -r))`, with inclusion `j`
   and second-coordinate quotient `q`. A relation with second coordinate zero
   has `r = 0`, proving injectivity. A representative `(p,r)` in `ker q`
   has `r ∈ I^n` and equals `j(p + l(r))`, proving exactness; `q` is surjective.
4. The map `(p,r) ↦ a(1 ⊗ p) + r • (τ + a(m))` kills the relations.
   Descend it to `E` and extend scalars to obtain `θ₀ : S ⊗ E → T`.
   Check both commuting squares on pure tensors and quotient representatives.
5. Flat tensor exactness gives `ker q_S = range j_S`, and tensor right
   exactness gives surjectivity of `q_S`. If `θ₀ z = 0`, lift `z` from `j_S`
   and use injectivity of `a` to show `z = 0`. To lift `t` from `θ₀`, first
   lift `b(t)` through `q_S`, then lift the remainder from `a`. Thus `θ₀`
   is bijective and gives the required linear equivalence. -/
theorem exists_cyclic_extension_flat_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (n : ℕ) (hn : 1 ≤ n)
    {N : Type w} [AddCommGroup N] [Module R N]
    {T : Type x} [AddCommGroup T] [Module S T]
    (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] (R ⧸ I ^ n))
    (ha : Function.Injective a) (hab : Function.Exact a b)
    (_hb : Function.Surjective b) :
    ∃ (E : Type (max u w)) (_ : AddCommGroup E) (_ : Module R E)
      (j : N →ₗ[R] E) (q : E →ₗ[R] (R ⧸ I ^ n)),
      Function.Injective j ∧ Function.Exact j q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] T,
        θ.toLinearMap.comp (j.baseChange S) = a ∧
        b.comp θ.toLinearMap = q.baseChange S := by
  classical
  let : Module R T := Module.restrictScalars R S T
  let : IsScalarTower R S T := IsScalarTower.restrictScalars R S T
  have : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  let J := I ^ n
  obtain ⟨τ, hτ⟩ := _hb (1 ⊗ₜ[R] (1 : R ⧸ J))
  let ar := a.restrictScalars R
  let c : J →ₗ[R] T := (LinearMap.id : R →ₗ[R] R).smulRight τ |>.comp J.subtype
  have hc : ∀ r : J, c r ∈ LinearMap.range ar := by
    intro r
    apply (hab (c r)).mp
    change b ((r : R) • τ) = 0
    rw [map_smul_of_tower, hτ, ← TensorProduct.tmul_smul]
    have hr : (r : R) • (1 : R ⧸ J) = 0 := by
      change Ideal.Quotient.mk J ((r : R) * 1) = 0
      simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr r.property)
    rw [hr, TensorProduct.tmul_zero]
  let d : J →ₗ[R] S ⊗[R] N :=
    (LinearEquiv.ofInjective ar ha).symm.toLinearMap.comp (c.codRestrict _ hc)
  have hd (r : J) : a (d r) = (r : R) • τ := by
    have h := (LinearEquiv.ofInjective ar ha).apply_symm_apply (c.codRestrict _ hc r)
    exact congrArg Subtype.val h
  obtain ⟨l, m, hl⟩ := exists_ideal_power_hom_lift hflat I hI hquot n hn d
  let τ' := τ + a m
  have hτ' : b τ' = 1 ⊗ₜ[R] (1 : R ⧸ J) := by
    dsimp [τ']
    rw [map_add, hτ, hab.apply_apply_eq_zero m, add_zero]
  have hlτ (r : J) : a (1 ⊗ₜ[R] l r) = (r : R) • τ' := by
    rw [hl r, map_add, map_smul_of_tower, hd r]
    exact (smul_add _ _ _).symm
  let k : J →ₗ[R] N × R := l.prod (-J.subtype)
  let W := LinearMap.range k
  let E := (N × R) ⧸ W
  let j : N →ₗ[R] E := W.mkQ.comp (LinearMap.inl R N R)
  let q₀ : N × R →ₗ[R] R ⧸ J := J.mkQ.comp (LinearMap.snd R N R)
  have hq₀ : W ≤ LinearMap.ker q₀ := by
    rintro z ⟨r, rfl⟩
    change J.mkQ (-(r : R)) = 0
    rw [map_neg]
    exact neg_eq_zero.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr r.property)
  let q : E →ₗ[R] R ⧸ J := W.liftQ q₀ hq₀
  have hj : Function.Injective j := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro p hp
    have hp' : (p, (0 : R)) ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hp
    obtain ⟨r, hr⟩ := hp'
    have hr0 : r = 0 := by
      apply Subtype.ext
      have := congrArg Prod.snd hr
      simpa [k] using this
    have := congrArg Prod.fst hr
    simpa [k, hr0] using this.symm
  have hjq : Function.Exact j q := by
    intro z
    obtain ⟨⟨p, r⟩, rfl⟩ := W.mkQ_surjective z
    change J.mkQ r = 0 ↔ ∃ p', j p' = W.mkQ (p, r)
    constructor
    · intro hr
      have hrJ : r ∈ J := (Submodule.Quotient.mk_eq_zero J).mp hr
      refine ⟨p + l ⟨r, hrJ⟩, ?_⟩
      change W.mkQ (p + l ⟨r, hrJ⟩, 0) = W.mkQ (p, r)
      apply sub_eq_zero.mp
      rw [← map_sub]
      apply (Submodule.Quotient.mk_eq_zero W).mpr
      refine ⟨⟨r, hrJ⟩, ?_⟩
      apply Prod.ext
      · change l ⟨r, hrJ⟩ = (p + l ⟨r, hrJ⟩) - p
        exact (add_sub_cancel_left p (l ⟨r, hrJ⟩)).symm
      · simp [k]
    · rintro ⟨p', hp'⟩
      have := congrArg q hp'
      change J.mkQ 0 = J.mkQ r at this
      simpa using this.symm
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨r, rfl⟩ := J.mkQ_surjective z
    exact ⟨W.mkQ (0, r), rfl⟩
  let g₀ : N × R →ₗ[R] T :=
    ((a.restrictScalars R).comp (TensorProduct.mk R S N 1)).coprod
      ((LinearMap.id : R →ₗ[R] R).smulRight τ')
  have hg₀ : W ≤ LinearMap.ker g₀ := by
    rintro z ⟨r, rfl⟩
    change a (1 ⊗ₜ[R] l r) + (-(r : R)) • τ' = 0
    rw [hlτ, neg_smul, add_neg_cancel]
  let g : E →ₗ[R] T := W.liftQ g₀ hg₀
  let θ₀ : S ⊗[R] E →ₗ[S] T := g.liftBaseChange S
  have hθj : θ₀.comp (j.baseChange S) = a := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s p
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
    change s • g₀ (p, 0) = a (s ⊗ₜ[R] p)
    simp only [g₀, LinearMap.coprod_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
      LinearMap.smulRight_apply, LinearMap.id_apply, zero_smul, add_zero]
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hbg (z : E) : b (g z) = 1 ⊗ₜ[R] q z := by
    obtain ⟨⟨p, r⟩, rfl⟩ := W.mkQ_surjective z
    change b (a (1 ⊗ₜ[R] p) + r • τ') = 1 ⊗ₜ[R] J.mkQ r
    rw [map_add, hab.apply_apply_eq_zero, zero_add, map_smul_of_tower, hτ',
      ← TensorProduct.tmul_smul]
    congr 1
    change Ideal.Quotient.mk J (r * 1) = Ideal.Quotient.mk J r
    rw [mul_one]
  have hbθ : b.comp θ₀ = q.baseChange S := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s z
    change b (s • g z) = s ⊗ₜ[R] q z
    rw [map_smul, hbg, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hcj (p : S ⊗[R] N) : θ₀ (j.baseChange S p) = a p :=
    DFunLike.congr_fun hθj p
  have hcb (e : S ⊗[R] E) : b (θ₀ e) = q.baseChange S e :=
    DFunLike.congr_fun hbθ e
  have hθ : Function.Bijective θ₀ := by
    have hbase : Function.Exact (j.baseChange S) (q.baseChange S) :=
      Module.Flat.lTensor_exact S hjq
    have hqbase : Function.Surjective (q.baseChange S) := q.lTensor_surjective S hq
    constructor
    · apply (LinearMap.ker_eq_bot).mp
      apply le_antisymm _ bot_le
      intro z hz
      change θ₀ z = 0 at hz
      have hqz : q.baseChange S z = 0 := by
        rw [← hcb, hz, map_zero]
      obtain ⟨p, hp⟩ := (hbase z).mp hqz
      have hap : a p = 0 := by
        rw [← hcj, hp, hz]
      have hp0 : p = 0 := ha (hap.trans (map_zero a).symm)
      simpa [hp0] using hp.symm
    · intro z
      obtain ⟨e, he⟩ := hqbase (b z)
      have hzero : b (z - θ₀ e) = 0 := by
        rw [map_sub, hcb, he, sub_self]
      obtain ⟨p, hp⟩ := (hab (z - θ₀ e)).mp hzero
      refine ⟨j.baseChange S p + e, ?_⟩
      rw [map_add, hcj, hp]
      exact sub_add_cancel z (θ₀ e)
  refine ⟨E, inferInstance, inferInstance, j, q, hj, hjq, hq,
    LinearEquiv.ofBijective θ₀ hθ, hθj, hbθ⟩

end LinearMap
