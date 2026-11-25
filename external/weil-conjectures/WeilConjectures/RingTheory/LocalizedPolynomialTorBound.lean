/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.RingTheory.PolynomialTorBound
import WeilConjectures.RingTheory.TorVanishingLocalizedBase

/-! # Transfer of Tor bounds to localized polynomial rings
Source: Stacks Project, Tag 068X.
(blueprint: lem-pc-localized-polynomial-tor-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Transfer the base Tor bound to a Tor bound over the localized polynomial ring.
Source: Stacks Project, Tag 068X, lemma-recognize-perfect-over-base.
Proof: restrict the localized module to the polynomial ring. The polynomial Tor bound
increases the base bound by at most n, without needing this restricted module to be finite.
For each localized test module, apply that bound to its polynomial-ring restriction.
The proved localization comparison then transfers this vanishing to the localized ring.
Successive restriction to the base is definitionally restriction along the composite in
hTor. This argument also covers n=0, d=0, and the zero module.
(blueprint: lem-pc-localized-polynomial-tor-bound)
-/
theorem localizedPolynomial_tor_bound_of_base_tor_bound
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) A))
    (M : ModuleCat.{u} (Localization p.asIdeal.primeCompl))
    [Module.Finite (Localization p.asIdeal.primeCompl) M]
    (d : ℕ)
    (hTor : ∀ N : ModuleCat.{u} A, ∀ i : ℕ, d < i →
      IsZero (((Tor' (ModuleCat.{u} A) i).obj
        ((ModuleCat.restrictScalars
          ((algebraMap (MvPolynomial (Fin n) A)
            (Localization p.asIdeal.primeCompl)).comp MvPolynomial.C)).obj M)).obj N)) :
    ∀ N : ModuleCat.{u} (Localization p.asIdeal.primeCompl), ∀ i : ℕ, d + n < i →
      IsZero (((Tor' (ModuleCat.{u} (Localization p.asIdeal.primeCompl)) i).obj M).obj N) := by
  intro N i hi
  apply isZero_tor_of_restrictScalars_localization
    (MvPolynomial (Fin n) A) (Localization p.asIdeal.primeCompl)
    p.asIdeal.primeCompl M N i
  apply polynomial_tor_bound_of_base_tor_bound n
    ((restrictScalars (algebraMap (MvPolynomial (Fin n) A)
      (Localization p.asIdeal.primeCompl))).obj M) d ?_ _ i hi
  intro L j hj
  exact hTor L j hj


end ModuleCat
