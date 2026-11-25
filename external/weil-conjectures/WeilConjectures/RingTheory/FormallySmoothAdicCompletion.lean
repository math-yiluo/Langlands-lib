/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Adic formal smoothness of the completion

Source: Stacks Project, More on Algebra, Lemma 15.38.4 (Tag 07ED), (1) implies (2)
with the base ring discrete (blueprint: lem-weil-pbc-fs-adic-completion).
-/

@[expose] public section

universe u v

namespace Algebra

/-- Formal smoothness for the `n`-adic topology passes to the completion when `n` is
finitely generated. The completion has its induced `R`-algebra structure, and its
ideal is the extension of `n` along the canonical map from `S`.
Source: Stacks Project, More on Algebra, Lemma 15.38.4 (Tag 07ED), (1) implies (2),
with the zero ideal on `R` (blueprint: lem-weil-pbc-fs-adic-completion).

Proof:
1. By `lem-weil-pbc-adic-completion-mod-power` (Stacks, Tag 05GG), the projections
   `pi_m : S^ → S/n^m` are surjective algebra maps, commute with the canonical
   `iota : S → S^`, and have kernel `n^m S^` for every positive `m`.
2. Expanding products of sums of generators proves `(n S^) ^ m = n^m S^`, so these
   kernels are precisely the powers of the extended ideal
   (`def-weil-pbc-algebra-hom-quotient`).
3. Given a square-zero ideal `J` of an `R`-algebra `D` and an algebra map
   `g : S^ → D/J` killing `(n S^) ^ k`, with `k` positive, restrict along `iota`.
   The map `g_0 = g ∘ iota` kills `n^k` (`theorem-finite-etale-covers-proper-henselian--2`).
4. Formal smoothness of `S` provides a lift `f_0 : S → D` of `g_0`.
5. Since `f_0(n^k)` lies in `J` and `J^2 = 0`, `f_0` kills `n^(2k)`; this is the
   argument of Stacks Tag 07EC(1) using `def-weil-pbc-algebra-hom-quotient`.
6. Factor `f_0` through the quotient `S/n^(2k)` and compose with `pi_(2k)` to
   obtain the algebra map `f : S^ → D` extending `f_0`.
7. The map `g` also factors through `pi_(2k)`. Its factor and the reduction of
   the factor of `f_0` agree after the surjective quotient map from `S`, hence
   agree. Thus reduction of `f` is `g`, solving every required lifting problem.
-/
theorem FormallySmoothAdic.adicCompletion (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] (n : Ideal S) (hn : n.FG)
    (h : FormallySmoothAdic R S n) :
    FormallySmoothAdic R (AdicCompletion n S)
      (n.map (algebraMap S (AdicCompletion n S))) := by
  intro D _ _ J hJ g hg
  obtain ⟨k, hk, hgk⟩ := hg
  let C := AdicCompletion n S
  let ι : S →ₐ[R] C := IsScalarTower.toAlgHom R S C
  let N : Ideal C := n.map (algebraMap S C)
  have hi (x : S) (hx : x ∈ n ^ k) : ι x ∈ N ^ k := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨f₀, hf₀⟩ := h J hJ (g.comp ι) ⟨k, hk, fun x hx ↦ hgk _ (hi x hx)⟩
  have hfJ : n ^ k ≤ J.comap f₀.toRingHom := by
    intro x hx
    have hz : (Ideal.Quotient.mkₐ R J) (f₀ x) = 0 := by
      have hxg := hgk (ι x) (hi x hx)
      have he := congrArg (fun q : S →ₐ[R] D ⧸ J => q x) hf₀
      exact he.symm ▸ hxg
    change f₀ x ∈ J
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hfkill : ∀ x ∈ n ^ (k + k), f₀ x = 0 := by
    have hp : n ^ (k + k) ≤ (J ^ 2).comap f₀.toRingHom := by
      rw [pow_add, pow_two]
      exact (Ideal.mul_mono hfJ hfJ).trans (Ideal.le_comap_mul _)
    rw [hJ] at hp
    exact fun x hx ↦ hp hx
  let π : C →ₐ[R] S ⧸ n ^ (k + k) :=
    (AdicCompletion.evalₐ n (k + k)).restrictScalars R
  let f : C →ₐ[R] D := (Ideal.Quotient.liftₐ (n ^ (k + k)) f₀ hfkill).comp π
  have hker (m : ℕ) :
      RingHom.ker (AdicCompletion.evalₐ n m).toRingHom = N ^ m := by
    ext x
    rw [RingHom.mem_ker]
    rw [← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem S, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hn]
    change (AdicCompletion.evalₐ n m) x = 0 ↔ AdicCompletion.eval n S m x = 0
    let e := Ideal.quotientEquivAlgOfEq S
      (show (n ^ m • ⊤ : Ideal S) = n ^ m by simp)
    change e (AdicCompletion.eval n S m x) = 0 ↔ AdicCompletion.eval n S m x = 0
    exact map_eq_zero_iff e e.injective
  refine ⟨f, ?_⟩
  ext x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (π x)
  have hπa : π (ι a) = Ideal.Quotient.mk (n ^ (k + k)) a :=
    AdicCompletion.evalₐ_of n (k + k) a
  have hd : x - ι a ∈ N ^ (k + k) := by
    rw [← hker, RingHom.mem_ker]
    change π (x - ι a) = 0
    rw [map_sub, hπa, ha, sub_self]
  have hgd : g (x - ι a) = 0 :=
    hgk _ ((Ideal.pow_le_pow_right (Nat.le_add_right k k)) hd)
  have hga : g x = g (ι a) := by
    simpa only [map_sub, sub_eq_zero] using hgd
  have hfa : f x = f₀ a := by
    change Ideal.Quotient.liftₐ (n ^ (k + k)) f₀ hfkill (π x) = f₀ a
    rw [← ha]
    rfl
  change Ideal.Quotient.mkₐ R J (f x) = g x
  rw [hfa, hga]
  exact DFunLike.congr_fun hf₀ a

end Algebra
