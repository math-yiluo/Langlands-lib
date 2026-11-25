/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionFlat
import WeilConjectures.RingTheory.EquationCountLocalizeRelativeGlobalCompleteIntersection
public import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness from the number of equations and fibre dimension

Source: Stacks Project, Algebra, Tags 00ST (3), 00SW, 00QD and 00HT
(blueprint: lem-weil-pbc-equation-count-fibre-dimension-flat).
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- Stacks Project, Algebra, Tags 00ST (3), 00SW, 00QD and 00HT.
(blueprint: lem-weil-pbc-equation-count-fibre-dimension-flat)
A quotient by `c` equations in `N` variables is flat near a prime where its fibre has
local topological dimension `N - c`; both prime-localization flatness conclusions follow.

Proof: `lem-weil-pbc-fibre-dimension-neighborhood` supplies `g` outside the prime with
all nonempty fibres of dimension at most `N - c`. Lift `g` to a polynomial `h` and
present the localization by adding a variable `z` and the equation `h*z - 1`, using
`lem-weil-pbc-localization-away-universal-property`. Polynomial scalar extension and
quotient base change (`lem-weil-pbc-polynomial-scalar-extension` and
`lem-weil-pbc-tensor-quotient-base-change`) identify every fibre of this presentation.
The lower bound `lem-weil-pbc-polynomial-quotient-dimension-lower-bound` makes every
nonempty fibre have dimension exactly `N - c`, so the presentation is a relative global
complete intersection (`theorem-finite-etale-covers-proper-henselian--2`). It is flat
by `lem-weil-pbc-relative-global-complete-intersection-flat`. Localizing further at the
prime uses `lem-weil-pbc-localization-of-localization` and
`lem-weil-pbc-localization-flat`; transitivity of tensoring preserves injections and
therefore gives flatness over `R`. Finally `lem-weil-pbc-flat-local-ring-maps` gives
flatness of the induced map between the two prime localizations. -/
theorem exists_flat_away_of_fibre_dimension_eq
    (R : Type u) [CommRing R] (N c : ℕ) (hc : c ≤ N)
    (equations : Fin c → MvPolynomial (Fin N) R) :
    let S := MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range equations)
    ∀ q : PrimeSpectrum S,
      let p := PrimeSpectrum.comap (algebraMap R S) q
      let Q := PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
      topologicalKrullDimAt Q = ((N - c : ℕ) : WithBot ℕ∞) →
        (∃ g : S, g ∉ q.asIdeal ∧ Module.Flat R (Localization.Away g)) ∧
        Module.Flat R (Localization.AtPrime q.asIdeal) ∧
        (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) rfl).Flat := by
  let S := MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range equations)
  dsimp only
  intro q hdim
  -- The existing localization lemma packages the fibre-dimension argument.
  obtain ⟨h, hg, hci, _, e, _⟩ :=
    Algebra.exists_localization_relativeGlobalCompleteIntersection R N c equations q ⟨hc, hdim⟩
  let g : S := Ideal.Quotient.mk _ h
  -- Use a finite presentation supplied by the intrinsic complete-intersection predicate.
  rw [Algebra.IsRelativeGlobalCompleteIntersection, toAlgebra_algebraMap] at hci
  obtain ⟨n, t, f, e', hf⟩ := hci
  have hpres : Algebra.IsRelativeGlobalCompleteIntersectionPresentation f := by
    intro p hp
    exact hf p hp
  have hflat := Algebra.flat_of_isRelativeGlobalCompleteIntersection_quotient R n t f hpres
  have : Module.Flat R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) :=
    RingHom.flat_algebraMap_iff.mp hflat
  have haway : Module.Flat R (Localization.Away g) :=
    Module.Flat.of_linearEquiv (e'.trans e).symm.toLinearEquiv
  refine ⟨⟨g, hg, haway⟩, ?_⟩
  -- Since g is outside q, S_q is a further localization of S_g.
  have hle : Submonoid.powers g ≤ q.asIdeal.primeCompl := by
    apply Submonoid.powers_le.mpr
    exact hg
  let A := Localization.Away g
  let B := Localization.AtPrime q.asIdeal
  let : Algebra A B := IsLocalization.localizationAlgebraOfSubmonoidLe A B
    (Submonoid.powers g) q.asIdeal.primeCompl hle
  have : IsScalarTower S A B := IsLocalization.localization_isScalarTower_of_submonoid_le
    A B (Submonoid.powers g) q.asIdeal.primeCompl hle
  have : IsLocalization (q.asIdeal.primeCompl.map (algebraMap S A)) B :=
    IsLocalization.isLocalization_of_submonoid_le A B
      (Submonoid.powers g) q.asIdeal.primeCompl hle
  have : Module.Flat A B :=
    IsLocalization.flat B (q.asIdeal.primeCompl.map (algebraMap S A))
  have : IsScalarTower R A B := IsScalarTower.to₁₃₄ R S A B
  have hprime : Module.Flat R B := Module.Flat.trans R A B
  refine ⟨hprime, ?_⟩
  -- Restrict the flat S_q module along R → R_p using the canonical local map.
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let φ := Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) rfl
  let : Algebra (Localization.AtPrime p.asIdeal) B := φ.toAlgebra
  have : IsScalarTower R (Localization.AtPrime p.asIdeal) B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R S B]
      exact (Localization.localRingHom_to_map p.asIdeal q.asIdeal
        (algebraMap R S) rfl r).symm
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p.asIdeal)
    p.asIdeal.primeCompl B).mpr hprime

end MvPolynomial
