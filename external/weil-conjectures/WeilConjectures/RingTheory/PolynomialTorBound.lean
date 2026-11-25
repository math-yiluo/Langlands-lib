/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.MvPolynomial.Equiv
import WeilConjectures.RingTheory.PolynomialSuccessorTorBound
import WeilConjectures.RingTheory.TorVanishingLocalizedBase

/-! # Tor bounds for polynomial modules
Source: Weibel, An Introduction to Homological Algebra, Theorem 4.3.7, pp. 101–102.
(blueprint: lem-pc-polynomial-tor-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Polynomial extension increases flat dimension by at most the number of variables.
Source: Weibel, Theorem 4.3.7, pp. 101–102, its exact-sequence argument applied to Tor.
Proof: for one variable t, resolve a module L by the canonical exact sequence
0 → A[t] tensor_A L → A[t] tensor_A L → L → 0, where the first map sends
f tensor x to tf tensor x - f tensor tx, and the last map evaluates the action.
Injectivity follows by comparing the highest coefficient; the kernel of evaluation
is the image by recursively removing highest coefficients. The induced modules
have Tor_i over A[t] equal to Tor_i over A against the restricted test module:
extend an A-projective resolution, using freeness of A[t] over A, and tensor
associativity. The Tor long exact sequence therefore gives vanishing above d+1.
Iterate this construction over n variables, identifying the iterated polynomial
ring with MvPolynomial (Fin n) A. At n=0 use its canonical ring equivalence with A.
No finiteness or Noetherian hypothesis is needed. The argument includes the zero
module and d=0, because it only uses positive degrees above the indicated bounds.
(blueprint: lem-pc-polynomial-tor-bound). -/
theorem polynomial_tor_bound_of_base_tor_bound
    {A : Type u} [CommRing A]
    (n : ℕ) (M : ModuleCat.{u} (MvPolynomial (Fin n) A)) (d : ℕ)
    (hTor : ∀ N : ModuleCat.{u} A, ∀ i : ℕ, d < i →
      IsZero (((Tor' (ModuleCat.{u} A) i).obj
        ((restrictScalars MvPolynomial.C).obj M)).obj N)) :
    ∀ N : ModuleCat.{u} (MvPolynomial (Fin n) A), ∀ i : ℕ, d + n < i →
      IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin n) A)) i).obj M).obj N) := by
  induction n with
  | zero =>
    have hbij : Function.Bijective (algebraMap A (MvPolynomial (Fin 0) A)) := by
      change Function.Bijective (MvPolynomial.C : A → MvPolynomial (Fin 0) A)
      have he : (MvPolynomial.C : A → MvPolynomial (Fin 0) A) =
          (MvPolynomial.isEmptyRingEquiv A (Fin 0)).symm := by
        funext a
        exact (MvPolynomial.isEmptyRingEquiv_symm_apply A (Fin 0) a).symm
      rw [he]
      exact (MvPolynomial.isEmptyRingEquiv A (Fin 0)).symm.bijective
    let : IsLocalization (⊥ : Submonoid A) (MvPolynomial (Fin 0) A) :=
      IsLocalization.of_le_isUnit_of_bijective
        (by
          rintro x ⟨a, ha, rfl⟩
          have ha' : a = 1 := by simpa using ha
          subst a
          simp) hbij
    intro N i hi
    have h := hTor ((restrictScalars MvPolynomial.C).obj N) i hi
    apply isZero_tor_of_restrictScalars_localization A (MvPolynomial (Fin 0) A)
      (⊥ : Submonoid A) M N i
    exact h
  | succ n ih =>
    let ρ : MvPolynomial (Fin n) A →+* MvPolynomial (Fin (n + 1)) A :=
      (MvPolynomial.rename Fin.castSucc).toRingHom
    let L := (restrictScalars ρ).obj M
    have hC : (MvPolynomial.C : A →+* MvPolynomial (Fin (n + 1)) A) =
        ρ.comp MvPolynomial.C := by
      apply RingHom.ext
      intro a
      change MvPolynomial.C a = MvPolynomial.rename Fin.castSucc (MvPolynomial.C a)
      simp
    have hL : ∀ N : ModuleCat.{u} A, ∀ i : ℕ, d < i →
        IsZero (((Tor' (ModuleCat.{u} A) i).obj
          ((restrictScalars MvPolynomial.C).obj L)).obj N) := by
      intro N i hi
      let e := restrictScalarsComp'App MvPolynomial.C ρ MvPolynomial.C hC M
      exact (hTor N i hi).of_iso
        (((Tor' (ModuleCat.{u} A) i).mapIso e).app N).symm
    have hstep := polynomial_successor_tor_bound n M (d + n) (ih L hL)
    intro N i hi
    exact hstep N i (by omega)

end ModuleCat
