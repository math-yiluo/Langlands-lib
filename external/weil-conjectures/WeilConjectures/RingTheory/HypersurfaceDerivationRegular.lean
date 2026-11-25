/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Localization.Ideal
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular hypersurfaces with a unit derivative

Source: Stacks Project, More on Algebra, Lemma Tag 07PF
(blueprint: lem-weil-pbc-hypersurface-derivation-regular).
-/

@[expose] public section

universe u

namespace IsRegularRing

/-- Stacks Project, More on Algebra, Lemma Tag 07PF:
(blueprint: lem-weil-pbc-hypersurface-derivation-regular).
The quotient of a regular ring by `f` is regular if an absolute derivation sends `f`
to a unit in the quotient. Absolute derivations are represented by `ℤ`-derivations:
additive maps are automatically `ℤ`-linear, and the Leibniz rule forces `D 1 = 0`.

Proof:
1. The quotient is Noetherian. For any prime `q` of the quotient, take its inverse
   image `p` in `R`. The element `f` lies in `p`, whereas `D(f)` does not: its
   image is a unit, and a proper prime ideal cannot contain a unit. This also
   covers a unit `f` vacuously, since its quotient has no primes.
2. Extend `D` to `R_p` using `theorem-finite-etale-covers-proper-henselian--2`. The image of `f`
   lies in the maximal ideal, and the derivative of this image is a unit because
   `D(f)` lies outside `p`. Induction on sums of products in the square of the
   maximal ideal, using additivity and Leibniz, shows that their derivatives lie
   in the maximal ideal. Therefore the image of `f` is outside that square.
   Apply `lem-weil-pbc-regular-local-hypersurface-criterion` to its local quotient.
3. Mathlib's quotient-localization instance and `IsLocalization.algEquiv` identify
   this regular local quotient with the localization of `R/(f)` at `q`, as in
   `lem-weil-pbc-localization-at-prime-of-quotient`. Transport regular localness
   along the equivalence. The regular-ring local criterion concludes.
-/
theorem quotient_span_singleton_of_isUnit_derivation
    (R : Type u) [CommRing R] [IsRegularRing R] (f : R) (D : Derivation ℤ R R)
    (hunit : IsUnit (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (D f))) :
    IsRegularRing (R ⧸ Ideal.span ({f} : Set R)) := by
  classical
  rw [isRegularRing_iff]
  intro q hq
  let I := Ideal.span ({f} : Set R)
  let p := q.comap (Ideal.Quotient.mk I)
  have hp : p.IsPrime := Ideal.comap_isPrime _ q
  let L := Localization.AtPrime p
  let a := algebraMap R L
  have hf : f ∈ p := by
    change Ideal.Quotient.mk I f ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
    exact q.zero_mem
  have hDf : D f ∉ p := Ideal.notMem_of_isUnit q hunit
  obtain ⟨Dl, hDl, -, -⟩ :=
    (D.exists_completion_and_unique_localization R).2 p.primeCompl
  have hx : a f ∈ IsLocalRing.maximalIdeal L :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L p f).mpr hf
  have hDx : IsUnit (Dl (a f)) := by
    rw [hDl]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff L p (D f)).mpr hDf
  have hx2 : a f ∉ IsLocalRing.maximalIdeal L ^ 2 := by
    intro h
    rw [pow_two] at h
    have hd : Dl (a f) ∈ IsLocalRing.maximalIdeal L := by
      refine Submodule.mul_induction_on h ?_ ?_
      · intro x hx y hy
        rw [Dl.leibniz]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_right _ _ hy)
      · intro x y hx hy
        rw [map_add]
        exact Ideal.add_mem _ hx hy
    exact (IsLocalRing.mem_maximalIdeal _).mp hd hDx
  obtain ⟨hloc, hreg, -⟩ := IsRegularLocalRing.quotient_span_singleton hx hx2
  have hmap : I.map a = Ideal.span ({a f} : Set L) := by
    rw [Ideal.map_span, Set.image_singleton]
  have : IsRegularLocalRing (L ⧸ I.map a) := by
    rw [hmap]
    exact hreg
  have hcompl : Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl = q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q
  have : IsLocalization q.primeCompl (L ⧸ I.map a) := by
    rw [← hcompl]
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (L ⧸ I.map a)
      (Localization.AtPrime q)).toRingEquiv

end IsRegularRing
