/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.Basic
public import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Smooth primitives on the profinite completion of the integers

Source: the cyclic refinement argument of `sk-lem-base-field-cd-finite-field.proof.md`.
(blueprint: lem-sfb-profinite-integer-smooth-primitives)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace DiscreteModule

private theorem sum_periods {A : Type v} [AddCommGroup A] (F : ℕ → A) (n : ℕ)
    (hF : ∀ m i, F (n * m + i) = F i) (m : ℕ) :
    ∑ i ∈ Finset.range (n * m), F i = m • ∑ i ∈ Finset.range n, F i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [mul_add, mul_one, Finset.sum_range_add, ih, succ_nsmul]
    simp only [hF]

/-- Summation on a cyclic quotient, refined by the coefficient exponent, gives a smooth
primitive for translation by a topological generator.

Source: blueprint `sk-lem-base-field-cd-finite-field.proof.md`, finite modules paragraph;
the summation construction in `DiscreteModule.IsEllAdicQuotient.exists_mul_sub_eq`.
(blueprint: lem-sfb-profinite-integer-smooth-primitives)

Proof: Take an open normal subgroup on whose right cosets f is constant, and let n be the
order of the generator in that finite quotient. Refine to the cyclic quotient of order
n*ell. The quotient map to the original quotient is the homomorphism sending generator
to generator; equality with the original projection follows on dense generator powers.
Set h(x) to the sum of f(tau^i) for i below the least residue of x modulo n*ell. The full
sum is ell times a sum over n terms and hence zero. Incrementing the residue gives the
required difference, including at the wraparound. The kernel of the refined quotient
fixes h on the right, so h is smooth. -/
theorem exists_smooth_primitive_of_cyclic_residues
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (τ : G) (hd : DenseRange (zpowersHom G τ))
    (residue : ∀ n : ℕ, 0 < n → G →ₜ* Multiplicative (ZMod n))
    (hresidue : ∀ (n : ℕ) (hn : 0 < n),
      residue n hn τ = Multiplicative.ofAdd 1)
    (ell : ℕ) (hell : 1 < ell)
    {A : Type v} [AddCommGroup A] (f : G → A)
    (hf : IsOpen (rightStab G f : Set G)) (hkill : ∀ x, ell • f x = 0) :
    ∃ h : G → A, IsOpen (rightStab G h : Set G) ∧ ∀ x, h (x * τ) - h x = f x := by
  classical
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hf
    (show (1 : G) ∈ rightStab G f from (rightStab G f).one_mem)
  let Q := G ⧸ U.toSubgroup
  let π : G →* Q := QuotientGroup.mk' U.toSubgroup
  have hπ : Continuous π := QuotientGroup.continuous_mk
  have : Finite Q := inferInstanceAs (Finite (G ⧸ U.toSubgroup))
  let n := orderOf (π τ)
  have hn : 0 < n := orderOf_pos (π τ)
  let N := n * ell
  have hN : 0 < N := Nat.mul_pos hn (by omega)
  have : NeZero N := ⟨by omega⟩
  have hN1 : 1 < N := by dsimp [N]; nlinarith
  have : Fact (1 < N) := ⟨hN1⟩
  let q := residue N hN
  have hgen : ∀ x : Multiplicative (ZMod N),
      x ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod N)) := by
    intro x
    refine ⟨(x.toAdd.val : ℤ), ?_⟩
    apply Multiplicative.toAdd.injective
    simp
  have hord : orderOf (π τ) ∣ orderOf (Multiplicative.ofAdd (1 : ZMod N)) := by
    simp [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one, n, N]
  let a : Multiplicative (ZMod N) →* Q := monoidHomOfForallMemZpowers hgen hord
  have ha : a (Multiplicative.ofAdd 1) = π τ :=
    monoidHomOfForallMemZpowers_apply_gen hgen hord
  have heq : a.comp q.toMonoidHom = π := by
    apply DFunLike.ext'
    apply hd.equalizer ((continuous_of_discreteTopology : Continuous a).comp q.continuous) hπ
    funext z
    change a (q (τ ^ z.toAdd)) = π (τ ^ z.toAdd)
    rw [map_zpow, map_zpow, show q τ = Multiplicative.ofAdd 1 from hresidue N hN,
      map_zpow, ha]
  have key (x y : G) (hxy : q x = q y) : f x = f y := by
    have hπxy : π x = π y := by
      rw [← DFunLike.congr_fun heq x, ← DFunLike.congr_fun heq y]
      exact congrArg a hxy
    have hmem : x⁻¹ * y ∈ U := QuotientGroup.eq.mp hπxy
    simpa using ((mem_rightStab.mp (hU hmem)) x).symm
  let idx : G → ℕ := fun x ↦ (q x).toAdd.val
  let F : ℕ → A := fun i ↦ f (τ ^ i)
  have key₁ (x : G) : f x = F (idx x) := by
    apply key
    apply Multiplicative.toAdd.injective
    simp [idx, q, hresidue]
  have key₂ (m i : ℕ) : F (n * m + i) = F i := by
    have hp : π (τ ^ (n * m + i)) = π (τ ^ i) := by
      simp [map_pow, pow_add, pow_mul, n, pow_orderOf_eq_one]
    have hmem : (τ ^ (n * m + i))⁻¹ * τ ^ i ∈ U := QuotientGroup.eq.mp hp
    simpa [F] using ((mem_rightStab.mp (hU hmem)) (τ ^ (n * m + i))).symm
  have hsum : ∑ i ∈ Finset.range N, F i = 0 := by
    rw [show N = n * ell from rfl, sum_periods F n key₂,
      Finset.smul_sum]
    exact Finset.sum_eq_zero (fun i _ ↦ hkill (τ ^ i))
  let V : Subgroup G := q.toMonoidHom.ker
  have hVo : IsOpen (V : Set G) := (isOpen_discrete {1}).preimage q.continuous
  have hidx (x k : G) (hk : k ∈ V) : idx (x * k) = idx x := by
    have hk' : q k = 1 := hk
    simp [idx, map_mul, hk']
  refine ⟨fun x ↦ ∑ i ∈ Finset.range (idx x), F i, ?_, fun x ↦ ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := V) (fun k hk x ↦ ?_) hVo
    simp only [hidx x k hk]
  · have hidxτ : idx (x * τ) = (idx x + 1) % N := by
      simp only [idx, map_mul, toAdd_mul,
        show q τ = Multiplicative.ofAdd 1 from hresidue N hN, toAdd_ofAdd]
      rw [ZMod.val_add, ZMod.val_one]
    have hlt : idx x < N := ZMod.val_lt _
    simp only
    rcases Nat.lt_or_ge (idx x + 1) N with h | h
    · rw [hidxτ, Nat.mod_eq_of_lt h, Finset.sum_range_succ, add_sub_cancel_left, key₁ x]
    · have h' : idx x + 1 = N := by omega
      rw [← h', Finset.sum_range_succ, ← key₁ x] at hsum
      rw [hidxτ, h', Nat.mod_self, Finset.sum_range_zero, zero_sub, neg_eq_iff_eq_neg]
      exact eq_neg_of_add_eq_zero_left hsum

end DiscreteModule
