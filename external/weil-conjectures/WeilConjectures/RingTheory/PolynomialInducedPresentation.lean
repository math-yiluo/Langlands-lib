/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic.Abel

/-! # Canonical induced presentation for a polynomial module
Source: Weibel, An Introduction to Homological Algebra, Theorem 4.3.7,
pp. 101–102, sequence (*) and its exactness proof.
(blueprint: lem-pc-polynomial-induced-presentation)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped ChangeOfRings

namespace ModuleCat

noncomputable section

section Sequences
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
private def seqDelta (T : Module.End R M) : (ℕ →₀ M) →ₗ[R] (ℕ →₀ M) :=
  Finsupp.lmapDomain M R Nat.succ - Finsupp.mapRange.linearMap T
private def seqEval (T : Module.End R M) : (ℕ →₀ M) →ₗ[R] M :=
  Finsupp.lsum R (fun n ↦ T ^ n)
private lemma seqDelta_single (T : Module.End R M) (k : ℕ) (m : M) :
    seqDelta T (Finsupp.single k m) =
      Finsupp.single (k + 1) m - Finsupp.single k (T m) := by
  simp [seqDelta]
private lemma seqEval_single (T : Module.End R M) (k : ℕ) (m : M) :
    seqEval T (Finsupp.single k m) = (T ^ k) m := by
  simp [seqEval]
private lemma seqDelta_injective (T : Module.End R M) : Function.Injective (seqDelta T) := by
  classical
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro q hq
  change seqDelta T q = 0 at hq
  by_contra hn
  have hs : q.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
  let k := q.support.max' hs
  have hk : q k ≠ 0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ hs)
  have hk' : q (k + 1) = 0 := by
    by_contra h
    have := Finset.le_max' q.support (k + 1) (Finsupp.mem_support_iff.mpr h)
    omega
  have hh := DFunLike.congr_fun hq (k + 1)
  exact hk (by simpa [seqDelta, Finsupp.mapDomain_apply_of_injective Nat.succ_injective,
    hk'] using hh)
private lemma seqDelta_correction (T : Module.End R M) (q : ℕ →₀ M) :
    ∃ p, seqDelta T p = q - Finsupp.single 0 (seqEval T q) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add q q' hq hq' =>
    obtain ⟨p, hp⟩ := hq
    obtain ⟨p', hp'⟩ := hq'
    exact ⟨p + p', by simp only [map_add, hp, hp', Finsupp.single_add]; abel⟩
  | single k m =>
    induction k generalizing m with
    | zero => exact ⟨0, by simp [seqEval_single]⟩
    | succ k ih =>
      obtain ⟨p, hp⟩ := ih (T m)
      refine ⟨Finsupp.single k m + p, ?_⟩
      rw [map_add, seqDelta_single, hp, seqEval_single, seqEval_single]
      simp only [pow_succ, Module.End.mul_apply]
      abel

end Sequences

set_option backward.isDefEq.respectTransparency false in
/-- An S-module has a length-one presentation by two copies of the module
induced from its restriction to the coefficient ring R.
Source: Weibel, An Introduction to Homological Algebra, Theorem 4.3.7,
pp. 101–102, sequence (*).
Proof: identify S with R[t], with t the last variable and R included by
rename Fin.castSucc. Put L = M restricted to R and E = S tensor_R L.
Define delta(f tensor m) = (t*f) tensor m - f tensor (t*m) and
pi(f tensor m) = f*m. Both respect the R-balancing relation and are S-linear;
pi delta = 0 by associativity. Since S has R-basis 1,t,t^2,..., E identifies
with finitely supported sequences in L. A nonzero sequence with highest
nonzero coefficient m_k has coefficient m_k in degree k+1 of delta, so
delta is injective. The argument uses a coefficient in L, not cancellation
in the ring. For an element in ker pi, subtract delta(t^(k-1) tensor m_k)
to eliminate its highest coefficient, and descend by induction on k. In
degree zero the condition pi = 0 forces the coefficient to vanish.
Thus ker pi = im delta. Finally pi(1 tensor m) = m proves surjectivity.
This proves short exactness, including n=0, zero modules, and the zero ring.
No Tor bound, finiteness, or domain assumption is involved.
(blueprint: lem-pc-polynomial-induced-presentation) -/
theorem exists_polynomial_induced_presentation
    {A : Type u} [CommRing A] (n : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin (n + 1)) A)) :
    let E := (extendScalars (MvPolynomial.rename Fin.castSucc).toRingHom).obj
      ((restrictScalars (MvPolynomial.rename Fin.castSucc).toRingHom).obj M)
    ∃ (δ : E ⟶ E) (π : E ⟶ M) (w : δ ≫ π = 0),
      (ShortComplex.mk δ π w).ShortExact := by
  classical
  let R := MvPolynomial (Fin n) A
  let S := MvPolynomial (Fin (n + 1)) A
  let ρ : R →+* S := (MvPolynomial.rename Fin.castSucc).toRingHom
  let L := (restrictScalars ρ).obj M
  let E := (extendScalars ρ).obj L
  let x : S := MvPolynomial.X (Fin.last n)
  let tM : M ⟶ M := ofHom (x • LinearMap.id)
  let t : L ⟶ L := (restrictScalars ρ).map tM
  let δ : E ⟶ E := ofHom (x • LinearMap.id) - (extendScalars ρ).map t
  let π : E ⟶ M := (extendRestrictScalarsAdj ρ).counit.app M
  let e := (MvPolynomial.renameEquiv A (finRotate (n + 1))).trans
    (MvPolynomial.finSuccEquiv A n)
  have he : e.toRingEquiv.toRingHom.comp ρ = (Polynomial.C : R →+* _) := by
    ext a : 1
    · ext z : 1
      simp [e, ρ, MvPolynomial.finSuccEquiv_apply]
    · have ha : finRotate (n + 1) a.castSucc = a.succ := finRotate_of_lt a.isLt
      simp [e, ρ, ha, MvPolynomial.finSuccEquiv_X_succ]
  let eL : ((restrictScalars ρ).obj (of S S)) ≃ₗ[R] Polynomial R :=
    { __ := e.toRingEquiv.toAddEquiv
      map_smul' r z := by
        rw [ModuleCat.restrictScalars.smul_def]
        simp only [RingHom.id_apply, Polynomial.smul_eq_C_mul]
        change e (ρ r • (show S from z)) = Polynomial.C r * e (show S from z)
        rw [smul_eq_mul]
        rw [map_mul, show e (ρ r) = Polynomial.C r from RingHom.congr_fun he r] }
  let b := (Polynomial.basisMonomials R).map eL.symm
  let c := TensorProduct.equivFinsuppOfBasisLeft (N := L) b
  have hb (k : ℕ) : b k = x ^ k := by
    apply eL.injective
    dsimp only [b]
    simp only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
      Polynomial.coe_basisMonomials]
    change Polynomial.monomial k 1 = e (x ^ k)
    simp [e, x, MvPolynomial.finSuccEquiv_X_zero,
      Polynomial.monomial_one_right_eq_X_pow]
  have hc (k : ℕ) (m : L) : c.symm (Finsupp.single k m) =
      (x ^ k) ⊗ₜ[R,ρ] m := by
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    simp [hb]
  have hπ (s : S) (m : L) : π (s ⊗ₜ[R,ρ] m) = s • (show M from m) := by
    have hs : (s ⊗ₜ[R,ρ] m : E) = s • ((1 : S) ⊗ₜ[R,ρ] m : E) := by
      simp [ExtendScalars.smul_tmul]
    rw [hs, π.hom.map_smul]
    exact congrArg (s • ·)
      (extendRestrictScalarsAdj_counit_app_apply_one_tmul (f := ρ) M (show M from m))
  have ht (k : ℕ) (m : L) : (t.hom ^ k) m = x ^ k • (show M from m) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change x • (x ^ k • (show M from m)) = x ^ (k + 1) • (show M from m)
      rw [← mul_smul, pow_succ']
  have hδ (k : ℕ) (m : L) :
      δ (c.symm (Finsupp.single k m)) =
        c.symm (seqDelta t.hom (Finsupp.single k m)) := by
    rw [hc, seqDelta_single, map_sub, hc, hc]
    dsimp only [δ, ModuleCat.hom_sub, ModuleCat.hom_ofHom]
    erw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    congr 1
    simpa only [pow_succ'] using ExtendScalars.smul_tmul ρ x (x ^ k) m
  have hδall (q : ℕ →₀ L) : δ (c.symm q) = c.symm (seqDelta t.hom q) := by
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add q q' hq hq' => simp [hq, hq']
    | single k m => exact hδ k m
  have hπall (q : ℕ →₀ L) : π (c.symm q) = seqEval t.hom q := by
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add q q' hq hq' => simp [hq, hq']
    | single k m => rw [hc, hπ, seqEval_single, ht]
  have hw : δ ≫ π = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    obtain ⟨q, rfl⟩ := c.symm.surjective y
    change π (δ (c.symm q)) = 0
    rw [hδall, hπall]
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add q q' hq hq' => simp [hq, hq']
    | single k m =>
      rw [seqDelta_single, map_sub, seqEval_single, seqEval_single]
      simp [pow_succ, Module.End.mul_apply]
  refine ⟨δ, π, hw, ?_⟩
  refine { mono_f := ?_, epi_g := ?_, exact := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    obtain ⟨q, rfl⟩ := c.symm.surjective y
    have hq : seqEval t.hom q = 0 := by
      change π (c.symm q) = 0 at hy
      rw [hπall] at hy
      exact hy
    obtain ⟨p, hp⟩ := seqDelta_correction t.hom q
    refine ⟨c.symm p, ?_⟩
    rw [hδall, hp, hq, Finsupp.single_zero, sub_zero]
  · apply (ModuleCat.mono_iff_injective δ).mpr
    intro y y' h
    obtain ⟨q, rfl⟩ := c.symm.surjective y
    obtain ⟨q', rfl⟩ := c.symm.surjective y'
    rw [hδall, hδall] at h
    exact congrArg c.symm (seqDelta_injective t.hom (c.symm.injective h))
  · apply (ModuleCat.epi_iff_surjective π).mpr
    intro m
    exact ⟨(1 : S) ⊗ₜ[R,ρ] (show L from m), by simpa using hπ 1 m⟩

end

end ModuleCat
