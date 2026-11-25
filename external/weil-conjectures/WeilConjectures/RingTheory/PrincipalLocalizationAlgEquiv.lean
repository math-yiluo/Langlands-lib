/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section
universe u
namespace Algebra

/-- The quotient presentation obtained by adjoining an inverse is isomorphic to the
principal localization. The isomorphism sends each old variable to its localization
image and the new variable to `Away.invSelf`; the relation `h * Away.invSelf = 1`
makes this map factor through the quotient, and the universal property of localization
gives the inverse map. These maps are inverse by the quotient and localization
induction principles, and the formulas follow on polynomial generators. Source:
Stacks Project, Algebra, Lemma Tag 00SS, part (2).
(blueprint: new-principal-localization-alg-equiv) -/
theorem principalLocalization_algEquiv
    (R : Type u) [CommRing R] (n c : ℕ)
    (f : Fin c → MvPolynomial (Fin n) R)
    (h : MvPolynomial (Fin n) R) :
      ∃ e :
          (MvPolynomial (Fin (n + 1)) R ⧸
              Ideal.span (Set.range
                (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin (n + 1)) R)
                  (fun i ↦ MvPolynomial.rename Fin.castSucc (f i))
                  (MvPolynomial.rename Fin.castSucc h * MvPolynomial.X (Fin.last n) - 1)))) ≃ₐ[R]
            Localization.Away
              (Ideal.Quotient.mk (Ideal.span (Set.range f)) h),
        (∀ i : Fin n,
          e (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.castSucc i))) =
            algebraMap
              (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
              (Localization.Away
                (Ideal.Quotient.mk (Ideal.span (Set.range f)) h))
              (Ideal.Quotient.mk _ (MvPolynomial.X i))) ∧
        e (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.last n))) =
          IsLocalization.Away.invSelf
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) h) := by
  classical
  let J : Ideal (MvPolynomial (Fin n) R) := Ideal.span (Set.range f)
  let A := (MvPolynomial (Fin n) R) ⧸ J
  let g : A := Ideal.Quotient.mk J h
  let S := Localization.Away g
  let F : Fin (c + 1) → (MvPolynomial (Fin (n + 1)) R) :=
    Fin.snoc (fun i ↦ MvPolynomial.rename Fin.castSucc (f i))
      (MvPolynomial.rename Fin.castSucc h * MvPolynomial.X (Fin.last n) - 1)
  let K : Ideal (MvPolynomial (Fin (n + 1)) R) := Ideal.span (Set.range F)
  let B := (MvPolynomial (Fin (n + 1)) R) ⧸ K
  let q : (MvPolynomial (Fin n) R) →ₐ[R] A := Ideal.Quotient.mkₐ R J
  let b : (MvPolynomial (Fin (n + 1)) R) →ₐ[R] B := Ideal.Quotient.mkₐ R K
  let a : A →ₐ[R] S := Algebra.algHom R A S
  let v : Fin (n + 1) → S :=
    Fin.snoc (fun i ↦ a (q (MvPolynomial.X i))) (IsLocalization.Away.invSelf g)
  let φ : (MvPolynomial (Fin (n + 1)) R) →ₐ[R] S := MvPolynomial.aeval v
  have hφ : φ.comp (MvPolynomial.rename Fin.castSucc) = a.comp q := by
    ext i
    simp only [AlgHom.comp_apply, φ, MvPolynomial.rename_X, MvPolynomial.aeval_X,
      v, Fin.snoc_castSucc]
  have hφK : ∀ p, p ∈ K → φ p = 0 := by
    have hle : K ≤ RingHom.ker φ.toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change φ (F i) = 0
      refine Fin.lastCases (motive := fun i ↦ φ (F i) = 0) ?_ (fun j ↦ ?_) i
      · simp only [F, Fin.snoc_last]
        have hh := AlgHom.congr_fun hφ h
        simp only [AlgHom.comp_apply] at hh
        rw [map_sub, map_mul, hh]
        simp only [φ, MvPolynomial.aeval_X, v, Fin.snoc_last, map_one]
        exact sub_eq_zero.mpr (IsLocalization.Away.mul_invSelf g)
      · simp only [F, Fin.snoc_castSucc]
        rw [← AlgHom.comp_apply, hφ, AlgHom.comp_apply]
        have hf : q (f j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span ⟨j, rfl⟩)
        simp [hf]
    exact fun p hp ↦ hle hp
  let forward : B →ₐ[R] S := Ideal.Quotient.liftₐ K φ hφK
  have hforward (p : MvPolynomial (Fin (n + 1)) R) : forward (b p) = φ p := rfl
  let ψ : MvPolynomial (Fin n) R →ₐ[R] B := b.comp (MvPolynomial.rename Fin.castSucc)
  have hψJ : ∀ p, p ∈ J → ψ p = 0 := by
    have hle : J ≤ RingHom.ker ψ.toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change b (MvPolynomial.rename Fin.castSucc (f i)) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span ⟨Fin.castSucc i, by simp [F]⟩
    exact fun p hp ↦ hle hp
  let base : A →ₐ[R] B := Ideal.Quotient.liftₐ J ψ hψJ
  have hbase (p : MvPolynomial (Fin n) R) :
      base (q p) = b (MvPolynomial.rename Fin.castSucc p) := rfl
  have hrel : base g * b (MvPolynomial.X (Fin.last n)) = 1 := by
    rw [show g = q h from rfl, hbase, ← map_mul, ← map_one b]
    change Ideal.Quotient.mk K _ = Ideal.Quotient.mk K _
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.subset_span ⟨Fin.last c, by simp [F]⟩
  have hunit : IsUnit (base g) := isUnit_iff_exists_inv.mpr
    ⟨b (MvPolynomial.X (Fin.last n)), hrel⟩
  let backward : S →ₐ[R] B := IsLocalization.Away.liftAlgHom g hunit
  have hbackward (x : A) : backward (a x) = base x := by
    exact IsLocalization.Away.lift_eq g hunit x
  have hinv : backward (IsLocalization.Away.invSelf g) =
      b (MvPolynomial.X (Fin.last n)) := by
    apply hunit.mul_left_cancel
    calc
      base g * backward (IsLocalization.Away.invSelf g) =
          backward (a g * IsLocalization.Away.invSelf g) := by
            rw [map_mul, hbackward]
      _ = 1 := by
        change backward (algebraMap A S g * IsLocalization.Away.invSelf g) = 1
        rw [IsLocalization.Away.mul_invSelf, map_one]
      _ = base g * b (MvPolynomial.X (Fin.last n)) := hrel.symm
  have hright : forward.comp backward = AlgHom.id R S := by
    apply IsLocalization.algHom_ext (Submonoid.powers g)
    apply Ideal.Quotient.algHom_ext
    ext i
    change forward (backward (a (q (MvPolynomial.X i)))) = a (q (MvPolynomial.X i))
    rw [hbackward, hbase, hforward]
    simp only [φ, MvPolynomial.rename_X, MvPolynomial.aeval_X, v, Fin.snoc_castSucc]
  have hleft : backward.comp forward = AlgHom.id R B := by
    apply Ideal.Quotient.algHom_ext
    ext i
    change backward (forward (b (MvPolynomial.X i))) = b (MvPolynomial.X i)
    refine Fin.lastCases (motive := fun i ↦
      backward (forward (b (MvPolynomial.X i))) = b (MvPolynomial.X i)) ?_ (fun j ↦ ?_) i
    · rw [hforward]
      simpa only [φ, MvPolynomial.aeval_X, v, Fin.snoc_last] using hinv
    · rw [hforward]
      simp only [φ, MvPolynomial.aeval_X, v, Fin.snoc_castSucc]
      rw [hbackward, hbase, MvPolynomial.rename_X]
  refine ⟨AlgEquiv.ofAlgHom forward backward hright hleft, ?_, ?_⟩
  · intro i
    change forward (b (MvPolynomial.X (Fin.castSucc i))) = a (q (MvPolynomial.X i))
    simp [hforward, φ, v]
  · change forward (b (MvPolynomial.X (Fin.last n))) = IsLocalization.Away.invSelf g
    simp [hforward, φ, v]

end Algebra
