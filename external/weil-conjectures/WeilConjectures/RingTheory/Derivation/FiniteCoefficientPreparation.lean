/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.RingTheory.Derivation.PowerSeriesPolynomialNormalization
import WeilConjectures.RingTheory.Derivation.PowerSeriesPolynomialDifferential
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coefficient preparation for detecting derivations

Source: Stacks Project, More on Algebra, Lemma 07PH, steps 1--5.
(blueprint: lem-weil-pbc-finite-coefficient-detecting-derivation).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
namespace Derivation

/-- A detecting derivation can be chosen to kill a coefficient subring over which
`B` is finite type.
Source: Stacks Project, More on Algebra, Lemma 07PH (`lemma-find-D`).
(blueprint: lem-weil-pbc-finite-coefficient-detecting-derivation)
Proof: replace the complete local base by its image, a complete Noetherian local
characteristic-p domain. Cohen structure makes it finite over a power series ring
R over a field k. Noether normalization gives a polynomial ring A over R and a
subring B' of B finite over A, with B'_g = B_g and equal fraction fields M.
The given detecting derivation implies that f is not a pth power: the Leibniz
formula D(x^p) = p*x^(p-1)*D(x) is zero in characteristic p. Choose a p-basis
of k. The coefficient subfields of 07P5 give subrings A_J with A finite over A_J
and fraction subfields K_J whose intersection is K^p. By 07P4 in the finite
extension M/K, the intersection of M^p K_J is M^p. Since f is not a pth
power, it lies outside M^p K_J for some J. The kernel criterion for the
universal differential over K_J is M^p K_J, so this relative differential
of f is nonzero.
A linear functional nonzero on this relative differential, composed with the
universal derivation, gives δ on M killing A_J and nonzero on f. Regard A_J as a
subring of B. Since A is finite over A_J, and B is finite type over R and hence
over A (the original finite algebra generators still generate over the
larger subring A), transitivity makes B finite type over A_J. This gives the stated
coefficient subring and derivation. No denominator clearing is used here. -/
theorem exists_finite_coefficient_derivation
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [IsDomain B] [CharP B p]
    (M : Type v) [Field M] [Algebra B M] [IsFractionRing B M]
    (R₀ : Type w) [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀]
    [Algebra R₀ B] [Algebra.FiniteType R₀ B]
    (f : B) (D : Derivation ℤ M M) (hD : D (algebraMap B M f) ≠ 0) :
    ∃ A : Subring B, Algebra.FiniteType A B ∧
      ∃ δ : Derivation ℤ M M,
        (∀ a : A, δ (algebraMap B M a) = 0) ∧ δ (algebraMap B M f) ≠ 0 := by
  classical
  let : CharP M p := charP_of_injective_ringHom (IsFractionRing.injective B M) p
  have hf : ¬ ∃ x : M, x ^ p = algebraMap B M f := by
    rintro ⟨x, hx⟩
    apply hD
    rw [← hx, D.leibniz_pow, ← Nat.cast_smul_eq_nsmul M, CharP.cast_eq_zero]
    simp
  obtain ⟨C, hC, k, hk, n, m, hkp, ⟨e⟩, K, hK, aCK, hfrac, aKM, htower, hdim⟩ :=
    exists_powerSeries_polynomial_normalization p B M R₀
  let := hk
  let := hkp
  let := hK
  let := aCK
  let := hfrac
  let := aKM
  let : Algebra C M := ((algebraMap B M).comp C.subtype).toAlgebra
  let := htower
  let := hdim
  obtain ⟨A, hfinite, hdiff⟩ :=
    KaehlerDifferential.exists_finite_subring_nonzero_differential
      p k n m C e K M (algebraMap B M f) hf
  let : Algebra A M := ((algebraMap C M).comp A.subtype).toAlgebra
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero M hdiff
  let δ : Derivation ℤ M M := (φ.compDer (KaehlerDifferential.D A M)).restrictScalars ℤ
  let A' : Subring B := A.map C.subtype
  let eA : A ≃+* A' := A.equivMapOfInjective C.subtype Subtype.val_injective
  have hAC : A.subtype.FiniteType := by
    let : Module.Finite A C := hfinite
    exact (RingHom.finiteType_algebraMap).mpr inferInstance
  have hCB : C.subtype.FiniteType := (RingHom.finiteType_algebraMap).mpr hC
  have hcomp : (A'.subtype.comp eA.toRingHom).FiniteType := by
    convert hCB.comp hAC using 1
    ext a
    rfl
  have hA' : Algebra.FiniteType A' B :=
    (RingHom.finiteType_algebraMap).mp (RingHom.FiniteType.of_comp_finiteType hcomp)
  refine ⟨A', hA', δ, ?_, hφ⟩
  intro a
  obtain ⟨b, hb⟩ := eA.surjective a
  subst a
  change φ (KaehlerDifferential.D A M (algebraMap A M b)) = 0
  rw [Derivation.map_algebraMap, map_zero]

end Derivation
