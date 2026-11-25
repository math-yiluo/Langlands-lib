/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.TateRootIdealPrime
import WeilConjectures.RingTheory.PrincipalPrimeQuotientFractionFinite
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink

/-!
# Finiteness of the quotient by a root of the parameter

Source: Stacks Project, Algebra, Tag 032P (lemma-tate-japanese), the residue-field argument.
(blueprint: lem-weil-pbc-tate-root-closure-quotient-finite).
-/

@[expose] public section

universe u v

set_option autoImplicit false

private theorem finite_integral_algebra_of_isN2
    (A : Type u) (B : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [Algebra.IsIntegral A B]
    [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    (hA : IsN2 A (FractionRing A)) : Module.Finite A B := by
  have : Small.{u} (FractionRing B) := Module.Finite.small (FractionRing A) (FractionRing B)
  let : IsScalarTower A (FractionRing A) (Shrink.{u} (FractionRing B)) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      apply (Shrink.algEquiv A (FractionRing B)).injective
      rw [AlgEquiv.commutes]
      change algebraMap A (FractionRing B) a =
        (Shrink.algEquiv (FractionRing A) (FractionRing B))
          (algebraMap (FractionRing A) (Shrink.{u} (FractionRing B))
            (algebraMap A (FractionRing A) a))
      rw [AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B) a
  have : Module.Finite A (integralClosure A (Shrink.{u} (FractionRing B))) :=
    hA (Shrink.{u} (FractionRing B))
  have : Module.Finite A (integralClosure A (FractionRing B)) :=
    Module.Finite.equiv
      (Shrink.algEquiv A (FractionRing B)).mapIntegralClosure.toLinearEquiv
  let f : B →ₗ[A] integralClosure A (FractionRing B) :=
    { toFun := fun b ↦ ⟨algebraMap B (FractionRing B) b,
        (Algebra.IsIntegral.isIntegral b).map
          (IsScalarTower.toAlgHom A B (FractionRing B))⟩
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (map_smul
        (IsScalarTower.toAlgHom A B (FractionRing B)) _ _) }
  exact Module.Finite.of_injective f
    (fun a b h ↦ IsFractionRing.injective B (FractionRing B) (congrArg Subtype.val h))

/-- The quotient by a root of the prime parameter is finite.
Source: Stacks Project, Algebra, Tag 032P (lemma-tate-japanese), from the description
of the prime over `xR` through the finiteness of `S/yS`.
(blueprint: lem-weil-pbc-tate-root-closure-quotient-finite).

Proof: If x = 0, positivity of p^e gives y = 0. Transport the N-2 condition
along R/(0) = R and the unique equivalence of fraction fields; apply it to L.
For different universes replace the finite-dimensional extension by a small
isomorphic field, using a finite basis. Thus S itself is finite in this case.
Otherwise x and y are nonzero. For a in S, the common-power hypothesis puts
its p^e-th power in K, and integrality and normality put this power in R.
The ideal yS consists exactly of the a for which a^(p^e) lies in xR:
if a^(p^e) = xr, then (a/y)^(p^e) = r, so a/y is integral over R.
This description shows yS is prime and its contraction is xR. Localizing R
at xR gives a one-dimensional Noetherian local domain, by the principal
ideal height theorem and the nonzero chain (0) < xR. Apply Tag 031F to
R_(xR) -> S_(yS), whose fraction fields are K and L, to obtain finiteness
of kappa(yS) over kappa(xR). The latter is a fraction field of R/xR.
N-2, transported to this fraction field and a small isomorphic copy of the
finite residue extension if necessary, makes its integral closure finite.
Reducing integral equations embeds S/yS into that closure. Since R/xR is
Noetherian, this submodule is finite. Restrict scalars along the finite
quotient map R -> R/xR to obtain the assertion. -/
theorem tate_root_closure_quotient_finite
    (R : Type u) (K L : Type v) [CommRing R] [IsDomain R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsNoetherianRing R] (x : R) (hnormal : IsIntegrallyClosed R)
    (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K L]
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))]
    (hquot : IsN2 (R ⧸ Ideal.span ({x} : Set R))
      (FractionRing (R ⧸ Ideal.span ({x} : Set R))))
    (e : ℕ) (hpow : ∀ a : L, a ^ (p ^ e) ∈ (algebraMap K L).range)
    (y : integralClosure R L)
    (hy : y ^ (p ^ e) = algebraMap R (integralClosure R L) x) :
    Module.Finite R ((integralClosure R L) ⧸ Ideal.span ({y} : Set (integralClosure R L))) := by
  let S := integralClosure R L
  let Q : Ideal S := Ideal.span ({y} : Set S)
  obtain ⟨hprime, hcontract⟩ := tate_root_ideal_prime R K L x hnormal p e hpow y hy
  change Q.comap (algebraMap R S) = Ideal.span ({x} : Set R) at hcontract
  let : Q.IsPrime := hprime
  let A := R ⧸ Q.comap (algebraMap R S)
  let B := S ⧸ Q
  let : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  let : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr Ideal.algebraMap_quotient_injective
  let : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  let : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra _ _
  let : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  have : FiniteDimensional (FractionRing A) (FractionRing B) :=
    principal_prime_quotient_fraction_finite R S K L x Q hcontract
  have hA : IsN2 A (FractionRing A) := by
    have htransport : ∀ (I : Ideal R) (hI : IsDomain (R ⧸ I)),
        I = Ideal.span ({x} : Set R) → @IsN2 (R ⧸ I) (FractionRing (R ⧸ I))
          _ hI _ _ _ := by
      intro I hI h
      subst I
      exact hquot
    exact htransport _ inferInstance hcontract
  have : Module.Finite A B := finite_integral_algebra_of_isN2 A B hA
  let : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  exact Module.Finite.trans A B
