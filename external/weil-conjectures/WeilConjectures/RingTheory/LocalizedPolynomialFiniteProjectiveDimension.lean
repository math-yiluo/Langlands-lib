/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.LocalizedPolynomialTorBound
import WeilConjectures.RingTheory.FiniteProjectiveDimensionOfTorBound

/-! # Finite projective dimension over a localized polynomial ring
Source: Stacks Project, Tag 068X.
(blueprint: lem-pc-localized-polynomial-finite-projective-dimension)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A finite module over a prime localization of a polynomial ring is perfect if it
has finite Tor dimension over the base.
Source: Stacks Project, Tag 068X, applied to a module concentrated in degree zero.
Proof: the polynomial ring and its localization are Noetherian by the Hilbert basis
theorem. A finite module is thus pseudo-coherent. The map from the base ring to the
localized polynomial ring is flat. Each nonzero fibre is a localization of a polynomial
ring in n variables over a field and has global dimension at most n. Tag 068X therefore
makes the module perfect. Take its finite free resolution and a syzygy beyond its Tor
amplitude. Dimension shifting makes this syzygy flat; it is finitely presented by
Noetherianity, hence projective. Truncate there to obtain a bounded projective resolution.
Its Ext groups vanish above its length, giving the asserted natural bound. For the zero
module use bound zero; when n = 0 the same argument applies to a localization of the base.
(blueprint: lem-pc-localized-polynomial-finite-projective-dimension)
-/
theorem localizedPolynomial_finiteProjectiveDimension_of_finiteTor
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
    ∃ k : ℕ, HasProjectiveDimensionLE M k := by
  have hTorS := localizedPolynomial_tor_bound_of_base_tor_bound n p M d hTor
  refine ⟨d + n, ?_⟩
  exact finite_hasProjectiveDimensionLE_of_tor_bound M (d + n) hTorS

end ModuleCat
