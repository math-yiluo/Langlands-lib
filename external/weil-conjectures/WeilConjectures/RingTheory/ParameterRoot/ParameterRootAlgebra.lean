/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Explicit simultaneous-root algebras

Source: monic division (Stacks 00G3, 04GG) and polynomial quotient universal properties.
The constructions work over arbitrary commutative rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
namespace Algebra.ParameterRoot

variable {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) (n : ℕ)

abbrev Ring := pthRootAlgebra n r R t

abbrev root (i : Fin r) : Ring t n := Ideal.Quotient.mk _ (MvPolynomial.X i)

def lift {S : Type v} [CommRing S] [Algebra R S]
    (x : Fin r → S) (hx : ∀ i, x i ^ n = algebraMap R S (t i)) : Ring t n →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x) (by
    have hle : Ideal.span (Set.range (fun j : Fin r ↦
        MvPolynomial.X j ^ n - MvPolynomial.C (t j))) ≤
        RingHom.ker (MvPolynomial.aeval x).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simpa using sub_eq_zero.mpr (hx i)
    exact fun a ha ↦ hle ha)

@[ext] theorem hom_ext {S : Type v} [CommRing S] [Algebra R S]
    {f g : Ring t n →ₐ[R] S} (h : ∀ i, f (root t n i) = g (root t n i)) : f = g := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  exact h

end Algebra.ParameterRoot
