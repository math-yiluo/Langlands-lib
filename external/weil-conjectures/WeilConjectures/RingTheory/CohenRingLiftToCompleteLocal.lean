/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.CohenRingModPowFormallySmooth
import Mathlib.RingTheory.AdicCompletion.RingHom

/-! # Lifting a Cohen ring into a complete local ring
Source: Stacks Project, Algebra, Theorem 032A(1), second proof paragraph. -/

@[expose] public section

universe u v
namespace IsLocalRing

private theorem lift_cohen_square_zero (p : ℕ) (C : Type v) [CommRing C]
    (hC : IsCohenRing p C) (D : Type u) [CommRing D] (n : ℕ) (hn : 1 ≤ n)
    (hpn : (p : D) ^ n = 0) (J : Ideal D) (hJ : J ^ 2 = ⊥) (g : C →+* D ⧸ J) :
    ∃ f : C →+* D, (Ideal.Quotient.mk J).comp f = g := by
  have hkill : Ideal.span {(p : C) ^ n} ≤ RingHom.ker g := by
    rw [Ideal.span_le]
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change g ((p : C) ^ n) = 0
    rw [map_pow, map_natCast]
    simpa using congrArg (Ideal.Quotient.mk J) hpn
  let g' := Ideal.Quotient.lift (Ideal.span {(p : C) ^ n}) g
    (fun x hx ↦ RingHom.mem_ker.mp (hkill hx))
  obtain ⟨f, hf⟩ :=
    (IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth p C hC n hn).2
      D hpn J hJ g'
  refine ⟨f.comp (Ideal.Quotient.mk _), ?_⟩
  rw [← RingHom.comp_assoc, hf]
  ext x
  rfl

/-- A prescribed residue isomorphism of a Cohen ring lifts into a complete local ring.
Source: Stacks Project, Algebra, Theorem 032A(1), second proof paragraph.
(blueprint: lem-weil-pbc-cohen-ring-lift-complete-local)

Proof: Since p is zero in the residue field of R, p lies in m and p^n lies in m^n.
Thus R/m^n is a Z/p^n-algebra. Start with the given residue isomorphism e. Inductively
lift C/p^n to R/m^n using formal smoothness of C/p^n over Z/p^n and the square-zero
kernel of R/m^n to R/m^(n-1). The resulting maps commute with the reduction maps.
Precompose each with C to C/p^n, forming a compatible system. This gives a ring map
from C into the adic completion of R; completeness identifies the latter with R.
Its first component is e composed with reduction modulo p, giving the equality. -/
theorem exists_cohenRing_lift (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (p : ℕ) [CharP (ResidueField R) p]
    (C : Type v) [CommRing C] (hC : IsCohenRing p C)
    (e : (C ⧸ Ideal.span {(p : C)}) ≃+* ResidueField R) :
    ∃ f : C →+* R,
      (residue R).comp f = e.toRingHom.comp (Ideal.Quotient.mk _) := by
  classical
  let m := maximalIdeal R
  have hpR : (p : R) ∈ m := by
    apply (residue_eq_zero_iff (R := R) _).mp
    simp
  have hstep (n : ℕ) (g : C →+* R ⧸ m ^ (n + 1)) :
      ∃ f : C →+* R ⧸ m ^ (n + 2),
        (Ideal.Quotient.factorPow m (by omega : n + 1 ≤ n + 2)).comp f = g := by
    let D := R ⧸ m ^ (n + 2)
    let J : Ideal D := (m ^ (n + 1)).map (Ideal.Quotient.mk (m ^ (n + 2)))
    have hJ : J ^ 2 = ⊥ := by
      rw [show J = (m ^ (n + 1)).map (Ideal.Quotient.mk (m ^ (n + 2))) from rfl,
        ← Ideal.map_pow, ← pow_mul]
      apply eq_bot_mono (Ideal.map_mono (Ideal.pow_le_pow_right
        (I := m) (show n + 2 ≤ (n + 1) * 2 by omega)))
      exact Ideal.map_quotient_self _
    have hpn : (p : D) ^ (n + 2) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (m ^ (n + 2))) p, ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hpR (n + 2)
    let q := DoubleQuot.quotQuotEquivQuotOfLE
      (Ideal.pow_le_pow_right (I := m) (by omega : n + 1 ≤ n + 2))
    obtain ⟨f, hf⟩ := lift_cohen_square_zero p C hC D (n + 2) (by omega) hpn J hJ
      (q.symm.toRingHom.comp g)
    refine ⟨f, ?_⟩
    have hq : q.toRingHom.comp (Ideal.Quotient.mk J) =
        Ideal.Quotient.factorPow m (by omega : n + 1 ≤ n + 2) := by
      ext x
      rfl
    rw [← hq, RingHom.comp_assoc, hf]
    ext x
    exact q.apply_symm_apply (g x)
  let fzero : C →+* R ⧸ m ^ (0 + 1) :=
    (Ideal.quotEquivOfEq (show maximalIdeal R = m ^ (0 + 1) by simp [m])).toRingHom.comp
      (e.toRingHom.comp (Ideal.Quotient.mk _))
  let f : (n : ℕ) → C →+* R ⧸ m ^ (n + 1) :=
    fun n ↦ Nat.rec fzero (fun n g ↦ Classical.choose (hstep n g)) n
  have hf : ∀ n, (Ideal.Quotient.factorPow m (by omega : n + 1 ≤ n + 1 + 1)).comp
      (f (n + 1)) = f n := by
    intro n
    exact Classical.choose_spec (hstep n (f n))
  let F := IsAdicComplete.StrictMono.liftRingHom m (a := fun n ↦ n + 1)
    (by intro a b hab; dsimp; omega) f (fun {n} ↦ hf n)
  refine ⟨F, ?_⟩
  ext x
  have hx := IsAdicComplete.StrictMono.mk_liftRingHom
    (I := m) (a := fun n ↦ n + 1) (by intro a b hab; dsimp; omega) f (fun {n} ↦ hf n) (n := 0) x
  change (Ideal.Quotient.mk (m ^ (0 + 1))) (F x) = fzero x at hx
  change (residue R) (F x) = e ((Ideal.Quotient.mk _) x)
  apply (Ideal.quotEquivOfEq
    (show maximalIdeal R = m ^ (0 + 1) by simp [m])).injective
  rw [residue_def, Ideal.quotEquivOfEq_mk]
  exact hx

end IsLocalRing
