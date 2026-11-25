/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.RingTheory.PopescuDelocalizeHeightZero
import WeilConjectures.RingTheory.PopescuResolutionIdentity
import WeilConjectures.RingTheory.PopescuParameterQuotientData
import WeilConjectures.RingTheory.PopescuParameterQuotientLocalResolution
import WeilConjectures.RingTheory.PopescuParameterQuotientPrimeGeometry

/-!
# Resolving the nilpotent parameter quotient

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FE, last paragraph.
-/

@[expose] public section

universe u v w

namespace Algebra

/-- The quotient by positive powers of a full system of parameters can be resolved over
the corresponding quotient of the polynomial base. No minimal-singular-prime assumption
on the unreduced algebra is needed.

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FE, steps 9--12 of the
repaired proof (blueprint: lem-weil-pbc-popescu-separable-parameter-quotient).

Proof: let `R = k[x_1,...,x_d]`, `e = 8c`, and `J = (x_i^e)`. The preimage `p` of `q`
in `R` is the origin ideal: it contains all variables, and that ideal is maximal with
quotient `k`. Localizing and then quotienting identifies the reduced local target with
`Λ_q/(π_i^e)`, and the reduced local base with `R_p/(x_i^e)`. Since the `d` images `π_i`
generate the maximal ideal of the regular local ring of dimension `d`, they are a regular
sequence. The polynomial-origin regular-local lemma and flat-over-regular lemma imply
that `R_p → Λ_q` is flat. Base change gives flatness of the reduced local map.
The maximal ideal of the reduced base is nilpotent: its power `d(e-1)+1` is zero because
every monomial of that degree is divisible by some `x_i^e`. Its residue field is `k`,
and the target reduction modulo that maximal ideal is `κ(q)`, with the original
`k`-algebra structure. Separability makes this field a filtered colimit of smooth
`k`-algebras. Nilpotent lifting therefore makes the reduced local target a filtered
colimit of smooth algebras over the reduced local base. Finite presentation factors
the map from the reduced localized `C` through a smooth algebra, giving a local resolution
whose extended singular ideal is the unit ideal.
There is only one prime in the reduced localized target, since any prime containing the
powers of the parameters contains every parameter and hence the maximal ideal. If the
reduced extended singular ideal already escapes the reduced prime, use the identity
resolution. Otherwise that prime is minimal over the ideal: localization gives a bijection
between primes below it and primes of its local ring. The height-zero delocalization lemma
then gives a resolution before localization. The quotient map and quotient prime are the
canonical ones, determined by the displayed compatibility equalities. This argument also
works for `d = 0`: both parameter ideals are zero and the local rings are fields. -/
theorem exists_popescu_resolution_parameter_quotient
    {k : Type u} {C : Type v} {Λ : Type w}
    [Field k] [CommRing C] [CommRing Λ] [Algebra k Λ]
    (d c : ℕ) (hc : 1 ≤ c) (φ : MvPolynomial (Fin d) k →ₐ[k] Λ)
    [Algebra (MvPolynomial (Fin d) k) C]
    [FinitePresentation (MvPolynomial (Fin d) k) C]
    (γ : letI := φ.toRingHom.toAlgebra; C →ₐ[MvPolynomial (Fin d) k] Λ)
    (q : PrimeSpectrum Λ) [IsNoetherianRing Λ]
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)]
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = (d : WithBot ℕ∞))
    (hgen : Ideal.span (Set.range (fun i : Fin d ↦
      algebraMap Λ (Localization.AtPrime q.asIdeal) (φ (MvPolynomial.X i)))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
    (hsep : IsSeparableExtension k q.asIdeal.ResidueField) :
    letI := φ.toRingHom.toAlgebra
    let J : Ideal (MvPolynomial (Fin d) k) :=
      Ideal.span (Set.range (fun i : Fin d ↦ (MvPolynomial.X i ^ c) ^ 8))
    let J_C := Ideal.map (algebraMap (MvPolynomial (Fin d) k) C) J
    let J_Λ := Ideal.map (algebraMap (MvPolynomial (Fin d) k) Λ) J
    ∃ (_ : FinitePresentation (MvPolynomial (Fin d) k ⧸ J) (C ⧸ J_C))
      (γ₀ : (C ⧸ J_C) →ₐ[MvPolynomial (Fin d) k ⧸ J] (Λ ⧸ J_Λ))
      (q₀ : PrimeSpectrum (Λ ⧸ J_Λ)),
      γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
        (Ideal.Quotient.mk J_Λ).comp γ.toRingHom ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
      CanBePopescuResolved γ₀ q₀ := by
  let := φ.toRingHom.toAlgebra
  dsimp
  obtain ⟨hfp, γ₀, q₀, hcompat, hcomap⟩ :=
    parameter_quotient_data d c hc φ γ q hgen
  refine ⟨hfp, γ₀, q₀, hcompat, hcomap, ?_⟩
  obtain ⟨hdim₀, hminimal⟩ :=
    parameter_quotient_prime_geometry d c φ q hgen hfp γ₀ q₀ hcomap
  by_cases hle : popescuIdeal γ₀ ≤ q₀.asIdeal
  · exact canBePopescuResolved_of_local_height_zero γ₀ q₀ (hminimal hle)
      (parameter_quotient_local_resolution d c hc φ γ q hdim hgen hsep
        hfp γ₀ q₀ hcompat hcomap) hdim₀
  · exact canBePopescuResolved_of_ideal_not_le γ₀ q₀ hle

end Algebra
