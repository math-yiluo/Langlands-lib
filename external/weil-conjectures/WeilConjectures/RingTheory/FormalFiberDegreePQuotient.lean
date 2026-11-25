/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Base change of a simple degree-p field presentation

Source: Stacks Project, More on Algebra, Tag 07PR, binomial presentation paragraph.
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- Base change of a simple degree-p field presentation at its specified coefficient.
Source: Stacks Project, More on Algebra, Tag 07PR, binomial presentation paragraph.
(blueprint: new-lem-weil-pbc-degree-p-quotient-component)

Proof: The element z generates L over M, and its degree is p. The monic polynomial
X^p - a vanishes at z and has degree p, so it is the minimal polynomial of z.
Evaluation therefore identifies M[Z]/(Z^p-a) with L as an M-algebra. Tensor this
presentation over M with R = M tensor_K F. Polynomial base change and quotient
base change identify its source with R[Z]/(Z^p-i(a)), where i(a) = a tensor 1.
Tensor associativity identifies the target L tensor_M R with L tensor_K F.
Compose these algebra equivalences and forget their algebra structure.
This argument also holds when F is zero: both sides are zero rings. -/
theorem nonempty_quotient_X_pow_sub_C_ringEquiv_tensorProduct
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L)
    (F : Type u) [CommRing F] [Algebra K F]
    (p : ℕ) [Fact p.Prime] (z : L)
    (hz : IntermediateField.adjoin M ({z} : Set L) = ⊤)
    (a : M) (ha : z ^ p = (a : L)) (hdeg : Module.finrank M L = p) :
    Nonempty ((Polynomial (TensorProduct K M F) ⧸
      Ideal.span ({Polynomial.X ^ p - Polynomial.C
                    (Algebra.TensorProduct.includeLeftRingHom a)} :
          Set (Polynomial (TensorProduct K M F)))) ≃+* TensorProduct K L F) := by
  classical
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hm : (Polynomial.X ^ p - Polynomial.C a).Monic :=
    Polynomial.monic_X_pow_sub_C a hp
  have hv : Polynomial.aeval z (Polynomial.X ^ p - Polynomial.C a) = 0 := by
    simp [ha]
  have hi : IsIntegral M z := ⟨_, hm, hv⟩
  have hd : (minpoly M z).natDegree = p := by
    have h := IntermediateField.adjoin.finrank hi
    rw [hz, IntermediateField.finrank_top'] at h
    exact h.symm.trans hdeg
  have he : minpoly M z = Polynomial.X ^ p - Polynomial.C a := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) hm
    · exact minpoly.dvd M z hv
    · rw [Polynomial.natDegree_X_pow_sub_C, hd]
  let e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[M] L :=
    (AdjoinRoot.algEquivOfEq M _ _ he.symm).trans
      ((IntermediateField.adjoinRootEquivAdjoin M hi).trans
        ((IntermediateField.equivOfEq hz).trans IntermediateField.topEquiv))
  let q : Polynomial (TensorProduct K F M) :=
    Polynomial.X ^ p - Polynomial.C (Algebra.TensorProduct.includeRight a)
  let eb := AdjoinRoot.tensorAlgEquiv (R := K) (T := F)
    (Polynomial.X ^ p - Polynomial.C a) q (by simp [q])
  let ec := Algebra.TensorProduct.comm K F M
  let eq := AdjoinRoot.mapRingEquiv ec.toRingEquiv q
    (Polynomial.X ^ p - Polynomial.C
      (Algebra.TensorProduct.includeLeftRingHom a))
    (by
      apply Associated.of_eq
      simp [q, ec])
  let et := Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (e.restrictScalars K)
  exact ⟨eq.symm.trans (eb.symm.toRingEquiv.trans
    (et.toRingEquiv.trans (Algebra.TensorProduct.comm K F L).toRingEquiv))⟩

end MvPowerSeries
