/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Quasi-finiteness along a four-ring square

Source: Stacks Project, Algebra, Lemma 10.122.7 (Tag 00PN)
(blueprint: lem-weil-pbc-quasi-finite-four-rings).
-/

@[expose] public section

universe u v w z

open scoped BigOperators

namespace Algebra

/-- (blueprint: lem-weil-pbc-quasi-finite-four-rings) In a commutative square of rings,
given by scalar towers `R → S → S'` and `R → R' → S'`, if `S` is of finite type over `R`
and every element of `S'` is a finite sum of products of images from `S` and `R'`, then
`S'` is of finite type over `R'`. Quasi-finiteness at the contraction of a prime of `S'`
passes to that prime (Stacks Project, Tag 00PN).

Proof: Images of finite algebra generators of `S` generate `S'` over `R'` by the
finite-sum hypothesis and the scalar-tower identities. This proves finite type directly.
The fibre-spectrum homeomorphism and Mathlib's
`quasiFiniteAt_iff_isOpen_singleton_fiber` convert the source isolated-point condition
into `QuasiFiniteAt`. The tensor universal property gives `R' ⊗[R] S →ₐ[R'] S'`;
the finite-sum hypothesis proves its surjectivity. Contract the target prime along
this map, apply `QuasiFiniteAt.baseChange`, and then apply
`QuasiFiniteAt.of_surjectiveOnStalks`, since a surjection is surjective on stalks.
Finally the same equivalence and the target fibre-spectrum homeomorphism recover the
required isolated-point condition. This implements Tag 00PN using Mathlib's
base-change and quotient permanence theorems instead of an explicit idempotent factor. -/
theorem finiteType_and_isQuasiFiniteAtPrime_of_four_rings
    (R : Type u) (S : Type v) (R' : Type w) (S' : Type z)
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra S S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S'] [Algebra.FiniteType R S]
    (hgen : ∀ x : S', ∃ (n : ℕ) (s : Fin n → S) (r : Fin n → R'),
      x = ∑ i : Fin n, algebraMap S S' (s i) * algebraMap R' S' (r i)) :
    ∃ hft : Algebra.FiniteType R' S', ∀ q' : PrimeSpectrum S',
      IsQuasiFiniteAtPrime R S (q'.comap (algebraMap S S')) →
        @IsQuasiFiniteAtPrime R' S' _ _ _ hft q' := by
  classical
  have hft : Algebra.FiniteType R' S' := by
    obtain ⟨⟨s, hs⟩⟩ := (inferInstance : Algebra.FiniteType R S)
    let t : Finset S' := s.image (algebraMap S S')
    let A : Subalgebra R' S' := Algebra.adjoin R' (t : Set S')
    have hmap : ∀ x : S, x ∈ Algebra.adjoin R (s : Set S) →
        algebraMap S S' x ∈ A := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
          exact Algebra.subset_adjoin (Finset.mem_image.2 ⟨x, hx, rfl⟩)
      | algebraMap r =>
          have hr : (algebraMap S S') ((algebraMap R S) r) =
              (algebraMap R' S') ((algebraMap R R') r) := by
            rw [← IsScalarTower.algebraMap_apply R S S' r,
              IsScalarTower.algebraMap_apply R R' S' r]
          rw [hr]
          exact A.algebraMap_mem _
      | add x y hx hy ihx ihy => simpa only [map_add] using A.add_mem ihx ihy
      | mul x y hx hy ihx ihy => simpa only [map_mul] using A.mul_mem ihx ihy
    refine ⟨⟨t, ?_⟩⟩
    apply top_unique
    intro x hx
    obtain ⟨n, ss, rr, rfl⟩ := hgen x
    apply A.sum_mem
    intro i hi
    apply A.mul_mem (hmap (ss i) (by rw [hs]; exact Set.mem_univ _))
    exact A.algebraMap_mem _
  refine ⟨hft, ?_⟩
  intro q' hq
  let _ : Algebra.FiniteType R' S' := hft
  let q := q'.comap (algebraMap S S')
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  have : QuasiFiniteAt R q.asIdeal := by
    apply (quasiFiniteAt_iff_isOpen_singleton_fiber q).mpr
    rw [← e.isOpen_image, Set.image_singleton]
    exact hq
  let f : TensorProduct R R' S →ₐ[R'] S' :=
    Algebra.TensorProduct.lift (Algebra.ofId R' S')
      (IsScalarTower.toAlgHom R S S') (fun _ _ => Commute.all _ _)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨n, ss, rr, rfl⟩ := hgen x
    refine ⟨∑ i, TensorProduct.tmul R (rr i) (ss i), ?_⟩
    simp [f, mul_comm]
  let Q := q'.asIdeal.comap f.toRingHom
  have : Q.IsPrime := Ideal.comap_isPrime f.toRingHom q'.asIdeal
  have hQ : q.asIdeal = Q.comap Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    simp [Q, q, f]
  have : QuasiFiniteAt R' Q := QuasiFiniteAt.baseChange q.asIdeal Q hQ
  have : QuasiFiniteAt R' q'.asIdeal :=
    QuasiFiniteAt.of_surjectiveOnStalks Q f
      (RingHom.surjectiveOnStalks_of_surjective hf) q'.asIdeal rfl
  let p' := q'.comap (algebraMap R' S')
  let e' := PrimeSpectrum.preimageHomeomorphFiber R' S' p'
  have ho := (quasiFiniteAt_iff_isOpen_singleton_fiber q').mp ‹QuasiFiniteAt R' q'.asIdeal›
  rw [← e'.isOpen_image, Set.image_singleton] at ho
  exact ho

end Algebra
