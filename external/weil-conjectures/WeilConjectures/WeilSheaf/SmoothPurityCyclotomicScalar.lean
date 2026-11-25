/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.ConstantTwistCondensed
public import WeilConjectures.WeilSheaf.FrobeniusTwist

/-! # Cancellation of the Frobenius scalar against the cyclotomic unit -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k₀ ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Multiplication by q followed by the cyclotomic unit q⁻¹ is the identity. -/
lemma purity_regularSmulIso_cyclotomic_cancel :
    ((Nat.card k₀ : ℤ) • 𝟙 (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))) ≫
        (regularSmulIso k₀ ℓ X (WeilSheaf.cyclotomicUnit k₀ ℓ)).hom = 𝟙 _ := by
  let r := Mod.regularEndRingHom.comp (CondensedRing.constRingHom (Profinite.padicAlgClRingObj ℓ)
    (Profinite.PadicAlgCl.constRingHom ℓ) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  have hq : (Nat.card k₀ : PadicAlgCl ℓ) ≠ 0 := by
    have hc := (WeilSheaf.cyclotomicUnit k₀ ℓ).ne_zero
    rw [WeilSheaf.cyclotomicUnit_eq] at hc
    intro hz
    rw [hz, inv_zero] at hc
    exact hc rfl
  have h := congrArg r (inv_mul_cancel₀ hq)
  rw [r.map_mul, r.map_one] at h
  have hn : r (Nat.card k₀) = (Nat.card k₀ : ℤ) • 1 := by
    rw [map_natCast]
    rw [Nat.cast_smul_eq_nsmul]
    exact (nsmul_one (Nat.card k₀)).symm
  rw [hn] at h
  simpa only [r, RingHom.comp_apply, regularSmulIso_hom, WeilSheaf.cyclotomicUnit_eq,
    End.mul_asHom, End.zsmul_asHom, End.one_asHom] using congrArg End.asHom h

end AlgebraicGeometry.ProEtaleWeilSheaf
