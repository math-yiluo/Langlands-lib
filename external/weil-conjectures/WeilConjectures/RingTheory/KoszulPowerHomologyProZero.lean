/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Filtration

/-!
# Positive Koszul homology of powers is pro-zero

Source: Stacks Project, Tag 0921.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

namespace ExteriorAlgebra

private theorem koszul_generator_smul_cycle (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A) (n : ℕ) (i : Fin r)
    (z : ⋀[A]^(n + 1) (Fin r →₀ A)) (hz : koszulBoundary A r f n z = 0) :
    f i • z ∈ LinearMap.range (koszulBoundary A r f (n + 1)) := by
  let e : Fin r →₀ A := Finsupp.single i 1
  let y : ⋀[A]^(n + 1 + 1) (Fin r →₀ A) :=
    ⟨ι A e * z, by
      change _ ∈ (LinearMap.range (ι A)) ^ (n + 1 + 1)
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ e) z.property⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  have hz' : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin r →₀ A)))
      (Finsupp.linearCombination A f) (z : ExteriorAlgebra A (Fin r →₀ A)) = 0 :=
    congrArg Subtype.val hz
  change CliffordAlgebra.contractLeft
    (Q := (0 : QuadraticForm A (Fin r →₀ A)))
    (Finsupp.linearCombination A f) (ι A e * (z : ExteriorAlgebra A (Fin r →₀ A))) =
      f i • (z : ExteriorAlgebra A (Fin r →₀ A))
  rw [CliffordAlgebra.contractLeft_ι_mul, hz']
  simp [e]

private theorem koszul_ideal_smul_cycles (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A) (n : ℕ) :
    Ideal.span (Set.range f) • LinearMap.ker (koszulBoundary A r f n) ≤
      LinearMap.range (koszulBoundary A r f (n + 1)) := by
  apply Submodule.smul_le.mpr
  intro c hc z hz
  induction hc using Submodule.span_induction with
  | mem c hc =>
      obtain ⟨i, rfl⟩ := hc
      exact koszul_generator_smul_cycle A r f n i z hz
  | zero => simp
  | add c d hc hd ihc ihd =>
      simpa only [add_smul] using (LinearMap.range _).add_mem ihc ihd
  | smul b c hc ih =>
      simpa only [smul_eq_mul, mul_smul] using (LinearMap.range _).smul_mem b ih

private theorem homologyMap_zero_of_cycles_to_boundaries
    (A : Type u) [CommRing A] {K L : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : K ⟶ L) (n : ℕ)
    (hf : ∀ z : K.cycles n, f.f n (K.iCycles n z) ∈
      LinearMap.range ((L.d (n + 1) n).hom)) :
    HomologicalComplex.homologyMap f n = 0 := by
  apply (cancel_epi (K.homologyπ n)).mp
  apply (cancel_mono (L.homologyι n)).mp
  simp only [comp_zero, zero_comp, Category.assoc]
  change (K.sc n).homologyπ ≫ CategoryTheory.ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f) ≫ (L.sc n).homologyι = 0
  rw [CategoryTheory.ShortComplex.π_homologyMap_ι]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨w, hw⟩ := hf z
  change L.pOpcycles n (f.f n (K.iCycles n z)) = 0
  rw [← hw]
  exact congrArg (fun φ ↦ φ w) (L.d_pOpcycles (n + 1) n)

private theorem power_exterior_image_mem (A : Type u) [CommRing A]
    (r : ℕ) (a : Fin r → A) (m c n : ℕ) (hn : 0 < n)
    (x : ⋀[A]^n (Fin r →₀ A)) :
    exteriorPower.map n (Finsupp.linearCombination A
      (fun i ↦ Finsupp.single i (a i ^ ((m + 1) * c)))) x ∈
      (Ideal.span (Set.range (fun i ↦ a i ^ (m + 1)))) ^ c •
        (⊤ : Submodule A (⋀[A]^n (Fin r →₀ A))) := by
  classical
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower n
  let T := exteriorPower.map n (Finsupp.linearCombination A
    (fun i ↦ Finsupp.single i (a i ^ ((m + 1) * c))))
  let P : Submodule A (⋀[A]^n (Fin r →₀ A)) :=
    (Ideal.span (Set.range (fun i ↦ a i ^ (m + 1)))) ^ c • ⊤
  have htop : P.comap T = ⊤ := by
    apply (Submodule.eq_top_iff_forall_basis_mem b).mpr
    intro s
    change T (b s) ∈ P
    let v : Fin n → Fin r := Set.powersetCard.ofFinEmbEquiv.symm s
    have heq : T (b s) = (∏ i : Fin n, a (v i) ^ ((m + 1) * c)) • b s := by
      dsimp only [T, b]
      rw [exteriorPower.basis_apply]
      dsimp only [exteriorPower.ιMulti_family]
      rw [exteriorPower.map_apply_ιMulti]
      simpa only [Function.comp_def, Finsupp.coe_basisSingleOne,
        Finsupp.linearCombination_single, one_smul, Finsupp.smul_single, smul_eq_mul, mul_one] using
        (exteriorPower.ιMulti A n).map_smul_univ
          (fun i ↦ a (v i) ^ ((m + 1) * c))
          (fun i ↦ Finsupp.single (v i) (1 : A))
    rw [heq]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    apply Ideal.prod_mem _ (i := (⟨0, hn⟩ : Fin n)) (Finset.mem_univ _)
    rw [pow_mul]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self (v ⟨0, hn⟩))) c
  change x ∈ P.comap T
  rw [htop]
  exact Submodule.mem_top

/-- Positive Koszul homology of powers of a finite sequence over a Noetherian ring
has eventually zero transitions. Indices `m` stand for exponent `m + 1`.
Source: Stacks Project, Tag 0921 (lemma-sequence-Koszul-complexes).
(auxiliary; not a blueprint node).

Proof: signed insertion of a generator gives dh+hd=f_i, so the ideal generated by
f annihilates the cycle module modulo the boundaries. Fix a positive degree and
level m, put J=(a_i^(m+1)), and apply Artin--Rees to the cycle submodule of the
finite free exterior power K_n. For its Artin--Rees index c, take
k=m+(m+1)(c+1). Every diagonal transition coefficient in positive degree has a
factor a_i^(k-m), hence lies in J^(c+1). A cycle therefore maps into
J^(c+1)K_n intersect cycles, which Artin--Rees puts in J times cycles, and this
lies in boundaries by the insertion identity. Thus the homology map is zero.
No regularity assumption is used; the empty sequence has zero positive terms. -/
theorem koszul_power_homology_pro_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] (r : ℕ) (a : Fin r → A)
    (t : ∀ m k : ℕ, m ≤ k →
      (koszulComplex A r (fun i ↦ a i ^ (k + 1)) ⟶
        koszulComplex A r (fun i ↦ a i ^ (m + 1))))
    (ht : ∀ m k h n, (t m k h).f n = ModuleCat.ofHom
      (exteriorPower.map n (Finsupp.linearCombination A
        (fun i ↦ Finsupp.single i (a i ^ (k - m)))))) :
    ∀ (n : ℕ), 0 < n → ∀ m : ℕ, ∃ (k : ℕ) (h : m ≤ k),
      HomologicalComplex.homologyMap (t m k h) n = 0 := by
  intro n hn m
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let f : Fin r → A := fun i ↦ a i ^ (m + 1)
  let Z := LinearMap.ker (koszulBoundary A r f n)
  let J := Ideal.span (Set.range f)
  obtain ⟨c, hc⟩ := J.exists_pow_inf_eq_pow_smul Z
  let k := m + (m + 1) * (c + 1)
  have hmk : m ≤ k := Nat.le_add_right _ _
  refine ⟨k, hmk, homologyMap_zero_of_cycles_to_boundaries A (t m k hmk) (n + 1) ?_⟩
  intro z
  let y : ⋀[A]^(n + 1) (Fin r →₀ A) := (t m k hmk).f (n + 1)
    ((koszulComplex A r (fun i ↦ a i ^ (k + 1))).iCycles (n + 1) z)
  have hyJ : y ∈ J ^ (c + 1) • (⊤ : Submodule A (⋀[A]^(n + 1) (Fin r →₀ A))) := by
    dsimp only [y]
    rw [ht]
    change exteriorPower.map (n + 1) _ _ ∈ _
    have hexp : k - m = (m + 1) * (c + 1) := by dsimp [k]; omega
    rw [hexp]
    exact power_exterior_image_mem A r a m (c + 1) (n + 1) (by omega) _
  have hyZ : y ∈ Z := by
    change koszulBoundary A r f n y = 0
    have hd (g : Fin r → A) (l : ℕ) : (koszulComplex A r g).d (l + 1) l =
        ModuleCat.ofHom (koszulBoundary A r g l) := by
      dsimp only [koszulComplex]
      exact ChainComplex.of_d _ _ l
    have hh := congrArg (fun φ ↦ φ z)
      ((koszulComplex A r (fun i ↦ a i ^ (k + 1))).iCycles_d (n + 1) n)
    simp only [ModuleCat.comp_apply, hd] at hh
    have hm := congrArg (fun φ ↦ φ
      ((koszulComplex A r (fun i ↦ a i ^ (k + 1))).iCycles (n + 1) z))
      ((t m k hmk).comm (n + 1) n)
    simp only [ModuleCat.comp_apply, hd] at hm
    change koszulBoundary A r f n y = _ at hm
    rw [hm, hh]
    exact map_zero _
  have hy : y ∈ J • Z := by
    have hh : y ∈ J ^ (c + 1) • ⊤ ⊓ Z := ⟨hyJ, hyZ⟩
    rw [hc (c + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hh
    exact (show J • (J ^ c • ⊤ ⊓ Z) ≤ J • Z from
      Submodule.smul_le.mpr (fun b hb x hx ↦ Submodule.smul_mem_smul hb hx.2)) hh
  have hb := koszul_ideal_smul_cycles A r f n hy
  change y ∈ LinearMap.range ((koszulComplex A r f).d (n + 1 + 1) (n + 1)).hom
  have hd : (koszulComplex A r f).d (n + 1 + 1) (n + 1) =
      ModuleCat.ofHom (koszulBoundary A r f (n + 1)) := by
    dsimp only [koszulComplex]
    exact ChainComplex.of_d _ _ (n + 1)
  rw [hd]
  exact hb

end ExteriorAlgebra
