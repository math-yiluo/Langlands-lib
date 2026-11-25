/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Order.RelSeries
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.FiniteTypeGRing

/-!
# Excellent rings

Following the Stacks Project we define:

* `IsCatenaryRing R`: for primes `𝔭 ⊆ 𝔮` the lengths of chains of primes from `𝔭` to `𝔮` are
  bounded and all maximal (saturated) such chains have the same length (Stacks, Tag 00NI).
* `IsUniversallyCatenary R`: `R` is Noetherian and every finite type `R`-algebra is catenary
  (Stacks, Tag 00NL).
* `IsJ1 R`: the regular locus of `Spec R` is open; `IsJ2 R`: every finite type `R`-algebra is
  J-1 (Stacks, Tag 07P7).
* `IsExcellentRing R`: `R` is a Noetherian, universally catenary, J-2 G-ring (Stacks, Tag 07QT).

Finite type algebras are quantified over the universe of `R`; as every finite type algebra is
isomorphic to a quotient of a polynomial ring `MvPolynomial (Fin n) R`, which lives in that
universe, this is no restriction.

We show that a finite type algebra over an excellent ring is excellent (Stacks, Tag 07QU,
`IsExcellentRing.of_finiteType`), in particular quotients of excellent rings are excellent.
-/

@[expose] public section

universe u

/-- The cover relation on the prime spectrum: the steps of a saturated chain of primes. -/
def PrimeSpectrum.coverRel (R : Type u) [CommRing R] :
    SetRel (PrimeSpectrum R) (PrimeSpectrum R) :=
  {x | x.1 ⋖ x.2}

/-- A ring `R` is catenary if for every pair of primes `𝔭 ⊆ 𝔮` there is a bound on the lengths
of the chains of primes `𝔭 = 𝔭₀ ⊊ ⋯ ⊊ 𝔭ₑ = 𝔮`, and all maximal such chains (those in which every
step `𝔭ᵢ ⊊ 𝔭ᵢ₊₁` is a cover, i.e. admits no prime strictly in between) have the same length.
Source: Stacks Project, Algebra, Definition 10.105.1 (Tag 00NI). -/
def IsCatenaryRing (R : Type u) [CommRing R] : Prop :=
  ∀ p q : PrimeSpectrum R, p ≤ q →
    (∃ N : ℕ, ∀ s : LTSeries (PrimeSpectrum R), s.head = p → s.last = q → s.length ≤ N) ∧
    ∀ s t : RelSeries (PrimeSpectrum.coverRel R), s.head = p → s.last = q → t.head = p →
      t.last = q → s.length = t.length

/-- A ring `R` is universally catenary if it is Noetherian and every finite type `R`-algebra is
catenary. Source: Stacks Project, Algebra, Definition 10.105.3 (Tag 00NL). -/
def IsUniversallyCatenary (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S], IsCatenaryRing S

/-- The regular locus `Reg(Spec R)`: the primes `𝔭` such that `R_𝔭` is a regular local ring.
Source: Stacks Project, More on Algebra, Section 15.47 (Tag 07P7). -/
def PrimeSpectrum.regularLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  {p | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

/-- A ring `R` is J-1 if its regular locus is open in `Spec R`.
Source: Stacks Project, More on Algebra, Definition 15.47.1 (Tag 07P7). -/
def IsJ1 (R : Type u) [CommRing R] : Prop :=
  IsOpen (PrimeSpectrum.regularLocus R)

/-- A ring `R` is J-2 if every finite type `R`-algebra is J-1.
Source: Stacks Project, More on Algebra, Definition 15.47.1 (Tag 07P7). -/
def IsJ2 (R : Type u) [CommRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S], IsJ1 S

/-- A ring `R` is excellent if it is Noetherian, universally catenary, a G-ring (`IsGRing`) and
J-2. Source: Stacks Project, More on Algebra, Definition 15.52.1 (Tag 07QT). -/
def IsExcellentRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ IsUniversallyCatenary R ∧ IsGRing R ∧ IsJ2 R

namespace IsExcellentRing

variable {R : Type u} [CommRing R]

theorem isNoetherianRing (hR : IsExcellentRing R) : IsNoetherianRing R := hR.1

theorem isUniversallyCatenary (hR : IsExcellentRing R) : IsUniversallyCatenary R := hR.2.1

theorem isGRing (hR : IsExcellentRing R) : IsGRing R := hR.2.2.1

theorem isJ2 (hR : IsExcellentRing R) : IsJ2 R := hR.2.2.2

end IsExcellentRing

section FiniteType

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

/-- A finite type algebra over a universally catenary ring is universally catenary: a finite
type algebra over it is of finite type over the base. -/
theorem IsUniversallyCatenary.of_finiteType (hR : IsUniversallyCatenary R) :
    IsUniversallyCatenary S := by
  have := hR.1
  refine ⟨Algebra.FiniteType.isNoetherianRing R S, fun T _ _ _ ↦ ?_⟩
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType R T := Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  exact hR.2 T

/-- A finite type algebra over a J-2 ring is J-2. -/
theorem IsJ2.of_finiteType (hR : IsJ2 R) : IsJ2 S := by
  intro T _ _ _
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType R T := Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  exact hR T

/-- A finite type algebra over an excellent ring is excellent.
Source: Stacks Project, More on Algebra, Lemma 15.52.2 (Tag 07QU). The G-ring part is
`isGRing_of_finiteType` (Stacks, Tag 07PV); the other conditions are formal. -/
theorem IsExcellentRing.of_finiteType (hR : IsExcellentRing R) : IsExcellentRing S :=
  have := hR.1
  ⟨Algebra.FiniteType.isNoetherianRing R S, hR.2.1.of_finiteType,
    isGRing_of_finiteType hR.2.2.1, hR.2.2.2.of_finiteType⟩

end FiniteType

/-- A quotient of an excellent ring is excellent (Stacks, Tag 07QU). -/
theorem IsExcellentRing.quotient {R : Type u} [CommRing R] (hR : IsExcellentRing R)
    (I : Ideal R) : IsExcellentRing (R ⧸ I) :=
  hR.of_finiteType
