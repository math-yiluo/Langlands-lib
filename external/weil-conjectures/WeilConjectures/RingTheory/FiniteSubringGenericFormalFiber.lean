/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.RingTheory.FormalFibreQuasiFiniteAscent
import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import WeilConjectures.RingTheory.GenericFormalFiberFiniteSubringBase
import WeilConjectures.RingTheory.GenericFormalFiberFractionFieldTransport

/-!
# Generic formal fibres and finite subrings

Source: Stacks Project, More on Algebra, Proposition 07PS, second paragraph,
and Lemma 07PP(1)
(blueprint: lem-weil-pbc-finite-subring-generic-formal-fibre).
-/

@[expose] public section

universe u

/-- Geometric regularity of the generic formal fibre ascends from a finite Noetherian
subring of a domain, with any chosen fraction field for the resulting fibre.
Source: Stacks Project, More on Algebra, Proposition 07PS, second paragraph,
and Lemma 07PP(1).
(blueprint: lem-weil-pbc-finite-subring-generic-formal-fibre).

Proof: The subring inclusion is injective, so the zero prime of A contracts to the zero
prime of A0. Module finiteness implies finite type. For P0 = P intersect A0, its fibre
A tensor_A0 kappa(P0) is a finite-dimensional algebra over kappa(P0). Every prime quotient
is a finite-dimensional domain over a field and hence a field: multiplication by a
nonzero element is injective and therefore surjective. Its primes are maximal. The Chinese
remainder theorem bounds the number of distinct maximal ideals by the vector-space
dimension. Thus the spectrum is finite and discrete, and the inclusion is quasi-finite
at P. Apply 07PP(1) to the primes 0 contained in P and their contractions. This gives
geometric regularity of kappa_A(0) tensor_A completion(A_P). The universal property of
fraction fields gives an A-algebra isomorphism kappa_A(0) to K, since both localize A
at its nonzero elements. It induces the corresponding isomorphism of generic fibres.
For any finite purely inseparable extension L/K, regard L as an extension of kappa_A(0)
through this field isomorphism. Finiteness and pure inseparability are preserved, and
tensor cancellation identifies its base change of the old fibre with
L tensor_K (K tensor_A completion(A_P)). The old geometric regularity makes this ring
regular; Noetherianity transports through the fibre isomorphism. This proves the claim,
including the possible zero fibre. -/
theorem isGeometricallyRegular_genericFormalFiber_of_finite_subring
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (A₀ : Subring A) [IsNoetherianRing A₀] [Module.Finite A₀ A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (P : Ideal A) [P.IsPrime]
    (hbase :
      let P₀ := P.comap (algebraMap A₀ A)
      let C₀ := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P₀))
        (Localization.AtPrime P₀)
      Algebra.IsGeometricallyRegular (⊥ : Ideal A₀).ResidueField
        ((⊥ : Ideal A₀).Fiber C₀)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P)
    Algebra.IsGeometricallyRegular K (TensorProduct A K C) := by
  apply genericFormalFiber_geometricallyRegular_of_fractionField_transport A K P
  exact genericFormalFiber_bot_geometricallyRegular_of_finite_subring A A₀ P hbase
