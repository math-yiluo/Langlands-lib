/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.AlgebraicGeometry.PBCNoetherianApproximation
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionBaseChange
import WeilConjectures.RingTheory.RelativeCompleteIntersectionClosedFiberRegularSequence
import WeilConjectures.RingTheory.PolynomialLocalFlatQuotientDescent
import WeilConjectures.RingTheory.RegularSequenceFlatClosedFiber
public import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness of successive localized complete-intersection quotients

Source: Stacks Project, Algebra, Lemma 00SV (2)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-partial-local-flat).
-/

@[expose] public section

universe v

namespace Algebra

private theorem noetherian_prefix_flat
    {R : Type v} [CommRing R] [IsNoetherianRing R] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) R)
    (_h : IsRelativeGlobalCompleteIntersectionPresentation f)
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime]
    (_hQ : Ideal.span (Set.range f) ≤ Q) (i : ℕ) (hi : i ≤ c) :
    Module.Flat R (Localization.AtPrime Q ⧸ Ideal.ofList
      (((List.ofFn f).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))).take i)) := by
  let P := MvPolynomial (Fin n) R
  let p := Q.comap (algebraMap R P)
  let S := Localization.AtPrime Q
  let φ := Localization.localRingHom p Q (algebraMap R P) rfl
  let : Algebra (Localization.AtPrime p) S := φ.toAlgebra
  have hflat : φ.Flat := RingHom.Flat.localRingHom
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R P)) Q p rfl
  have hquot := (RingTheory.Sequence.isRegular_and_flat_quotient_of_closedFiber φ hflat
    ((List.ofFn f).map (algebraMap P S))
      (isRegular_closedFiber_of_relativeCompleteIntersection f _h Q _hQ)).2 i
        (by simpa using hi)
  let J := Ideal.ofList (((List.ofFn f).map (algebraMap P S)).take i)
  have : IsScalarTower R (Localization.AtPrime p) S := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact (Localization.localRingHom_to_map p Q (algebraMap R P) rfl r).symm
  exact (Module.flat_iff_of_isLocalization
    (Localization.AtPrime p) p.primeCompl (S ⧸ J)).mp hquot

/-- Every initial quotient of the polynomial local ring at a prime of a relative global
complete intersection is flat over the base.
Source: Stacks Project, Algebra, Lemma 00SV (2)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-partial-local-flat).

Proof:
1. Over a Noetherian base, contract the polynomial prime to `p` in `R`. The canonical
   local map `R_p → R[x]_Q` is flat. The existing closed-fibre theorem supplies regularity
   of the equations; Grothendieck's lifting theorem gives flatness of every prefix quotient
   over `R_p`. Restrict scalars to `R`, using the canonical scalar tower.
2. Noetherian approximation supplies a finite type integer subring `R₀` and equations
   `f₀` whose coefficientwise images are `f`. For every finite type integer subring `B`
   containing `R₀`, base change preserves the specified complete-intersection condition.
3. Contract the polynomial prime to each `B[x]`. Composition of coefficient maps shows
   all equations lie in this contracted prime. Since `B` is Noetherian, step 1 makes its
   localized prefix quotient flat over `B`.
4. Apply finite-coefficient flatness descent to these prefix quotients. The initial list
   of equations generates exactly the displayed image-set ideal, by list membership and
   `Ideal.map_ofList`. This identifies the resulting flat quotient with the conclusion. -/
theorem relativeGlobalCompleteIntersection_partial_local_flat
    (R : Type v) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (i : ℕ) (hi : i ≤ c) :
    Module.Flat R
      (Localization.AtPrime
        (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f))) q).asIdeal ⧸
          Ideal.map
            (algebraMap (MvPolynomial (Fin n) R)
              (Localization.AtPrime
                (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f))) q).asIdeal))
            (Ideal.span (f '' {j : Fin c | j.val < i}))) := by
  classical
  let Q := (PrimeSpectrum.comap
    (Ideal.Quotient.mk (Ideal.span (Set.range f))) q).asIdeal
  have hQ : Ideal.span (Set.range f) ≤ Q := by
    intro x hx
    change Ideal.Quotient.mk (Ideal.span (Set.range f)) x ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.asIdeal.zero_mem
  obtain ⟨R₀, hR₀, f₀, hcoeff, hf₀⟩ :=
    exists_finiteType_subring_relativeGlobalCompleteIntersection R n c f h
  have hf : f = fun j ↦ MvPolynomial.map R₀.subtype (f₀ j) := by
    funext j
    ext d
    simpa only [MvPolynomial.coeff_map, Subring.subtype_apply] using hcoeff j d
  have hprefix : Ideal.ofList ((List.ofFn f).take i) =
      Ideal.span (f '' {j : Fin c | j.val < i}) := by
    change Ideal.span {x | x ∈ (List.ofFn f).take i} = _
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_take_iff_getElem, List.length_ofFn,
      Set.mem_image]
    constructor
    · rintro ⟨j, hj, hx⟩
      refine ⟨⟨j, (lt_min_iff.mp hj).2⟩, (lt_min_iff.mp hj).1, ?_⟩
      simpa only [List.getElem_ofFn] using hx
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j.val, lt_min hj j.isLt, ?_⟩
      simp
  have hideal : Ideal.ofList
      (((List.ofFn f).map (algebraMap (MvPolynomial (Fin n) R)
        (Localization.AtPrime Q))).take i) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))
        (Ideal.span (f '' {j : Fin c | j.val < i})) := by
    rw [← hprefix, Ideal.map_ofList, List.map_take]
  change Module.Flat R (Localization.AtPrime Q ⧸ _)
  have hlist := congrArg List.ofFn hf
  rw [← hideal, hlist]
  apply RingTheory.flat_polynomial_local_quotient_of_finiteType_subrings R₀ hR₀ f₀ Q i
  intro B hB hft
  let : Algebra R₀ B := (Subring.inclusion hB).toAlgebra
  have : Algebra.FiniteType ℤ B := hft
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  let fB := fun j ↦ MvPolynomial.map (Subring.inclusion hB) (f₀ j)
  have hfB : IsRelativeGlobalCompleteIntersectionPresentation fB :=
    (relativeGlobalCompleteIntersection_baseChange R₀ B n c f₀).2 hf₀
  have hQB : Ideal.span (Set.range fB) ≤ Q.comap (MvPolynomial.map B.subtype) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change MvPolynomial.map B.subtype (fB j) ∈ Q
    have hmap : MvPolynomial.map B.subtype (fB j) = f j := by
      rw [hf]
      dsimp [fB]
      rw [MvPolynomial.map_map]
      rfl
    rw [hmap]
    exact hQ (Ideal.subset_span ⟨j, rfl⟩)
  exact noetherian_prefix_flat fB hfB (Q.comap (MvPolynomial.map B.subtype)) hQB i hi

end Algebra
