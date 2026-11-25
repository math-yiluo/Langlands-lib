/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The spectrum of a sequential colimit of rings

Let `G : ℕ ⥤ CommRingCat` be a sequence of rings whose transition maps induce surjections on
prime spectra. Then `Spec (colim G) ⟶ Spec (G 0)` is surjective
(`PrimeSpectrum.comap_colimit_ι_zero_surjective`): a prime `p` of `G 0` lifts to a compatible
sequence of primes `qₙ` of the `G n`, and the elements of `colim G` represented by elements of
some `qₙ` form a prime ideal lying over `p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PrimeSpectrum

local instance : PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u, u} (forget CommRingCat.{u})

variable (G : ℕ ⥤ CommRingCat.{u})
  (hG : ∀ n : ℕ, Function.Surjective (comap (G.map (homOfLE (Nat.le_succ n))).hom))

/-- A compatible sequence of primes lifting a prime of `G 0`. -/
noncomputable def liftSeq (p : PrimeSpectrum (G.obj 0)) : ∀ n, PrimeSpectrum (G.obj n)
  | 0 => p
  | n + 1 => (hG n (liftSeq p n)).choose

include hG in
lemma comap_liftSeq_succ (p : PrimeSpectrum (G.obj 0)) (n : ℕ) :
    comap (G.map (homOfLE n.le_succ)).hom (liftSeq G hG p (n + 1)) = liftSeq G hG p n :=
  (hG n (liftSeq G hG p n)).choose_spec

include hG in
lemma comap_liftSeq (p : PrimeSpectrum (G.obj 0)) {m n : ℕ} (h : m ≤ n) :
    comap (G.map (homOfLE h)).hom (liftSeq G hG p n) = liftSeq G hG p m := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have : homOfLE (hmn.trans n.le_succ) = homOfLE hmn ≫ homOfLE n.le_succ := rfl
    rw [this, Functor.map_comp, CommRingCat.hom_comp, comap_comp_apply,
      comap_liftSeq_succ, ih]

include hG in
lemma map_mem_liftSeq_iff (p : PrimeSpectrum (G.obj 0)) {m n : ℕ} (h : m ≤ n) (y : G.obj m) :
    G.map (homOfLE h) y ∈ (liftSeq G hG p n).asIdeal ↔ y ∈ (liftSeq G hG p m).asIdeal := by
  rw [← comap_liftSeq G hG p h]
  rfl

include hG in
/-- Membership of `ι_n y` in the prime ideal of `colim G` does not depend on the representative.
-/
lemma mem_liftSeq_iff_of_ι_eq (p : PrimeSpectrum (G.obj 0)) {m n : ℕ} (y : G.obj m)
    (z : G.obj n) (h : colimit.ι G m y = colimit.ι G n z) :
    y ∈ (liftSeq G hG p m).asIdeal ↔ z ∈ (liftSeq G hG p n).asIdeal := by
  obtain ⟨k, f, g, hk⟩ := (Concrete.colimit_rep_eq_iff_exists G y z).1 h
  rw [← map_mem_liftSeq_iff G hG p (leOfHom f) y, ← map_mem_liftSeq_iff G hG p (leOfHom g) z]
  exact Iff.of_eq (congrArg (· ∈ (liftSeq G hG p k).asIdeal) hk)

/-- The prime ideal of `colim G` lying over a prime `p` of `G 0`: the elements represented by an
element of some `qₙ`. -/
noncomputable def colimitIdeal (p : PrimeSpectrum (G.obj 0)) : Ideal (colimit G : CommRingCat) where
  carrier := {x | ∃ n y, colimit.ι G n y = x ∧ y ∈ (liftSeq G hG p n).asIdeal}
  add_mem' := by
    rintro _ _ ⟨m, y, rfl, hy⟩ ⟨n, z, rfl, hz⟩
    refine ⟨max m n, G.map (homOfLE (le_max_left m n)) y + G.map (homOfLE (le_max_right m n)) z,
      ?_, add_mem ((map_mem_liftSeq_iff G hG p _ y).2 hy) ((map_mem_liftSeq_iff G hG p _ z).2 hz)⟩
    rw [map_add, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, colimit.w, colimit.w]
  zero_mem' := ⟨0, 0, map_zero _, zero_mem _⟩
  smul_mem' := by
    rintro c _ ⟨n, z, rfl, hz⟩
    obtain ⟨m, y, rfl⟩ := Concrete.colimit_exists_rep G c
    refine ⟨max m n, G.map (homOfLE (le_max_left m n)) y * G.map (homOfLE (le_max_right m n)) z,
      ?_, Ideal.mul_mem_left _ _ ((map_mem_liftSeq_iff G hG p _ z).2 hz)⟩
    rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, colimit.w, colimit.w,
      smul_eq_mul]

include hG in
lemma ι_mem_colimitIdeal_iff (p : PrimeSpectrum (G.obj 0)) (n : ℕ) (y : G.obj n) :
    colimit.ι G n y ∈ colimitIdeal G hG p ↔ y ∈ (liftSeq G hG p n).asIdeal :=
  ⟨fun ⟨_, z, hz, hz'⟩ ↦ (mem_liftSeq_iff_of_ι_eq G hG p z y hz).1 hz', fun h ↦ ⟨n, y, rfl, h⟩⟩

include hG in
lemma isPrime_colimitIdeal (p : PrimeSpectrum (G.obj 0)) : (colimitIdeal G hG p).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one, ← map_one (colimit.ι G 0).hom, ι_mem_colimitIdeal_iff]
    exact fun h ↦ (liftSeq G hG p 0).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  mem_or_mem' := by
    intro a b hab
    obtain ⟨m, y, rfl⟩ := Concrete.colimit_exists_rep G a
    obtain ⟨n, z, rfl⟩ := Concrete.colimit_exists_rep G b
    rw [← colimit.w G (homOfLE (le_max_left m n)), ← colimit.w G (homOfLE (le_max_right m n)),
      CommRingCat.comp_apply, CommRingCat.comp_apply, ← map_mul, ι_mem_colimitIdeal_iff] at hab
    rw [← colimit.w G (homOfLE (le_max_left m n)), ← colimit.w G (homOfLE (le_max_right m n)),
      CommRingCat.comp_apply, CommRingCat.comp_apply, ι_mem_colimitIdeal_iff,
      ι_mem_colimitIdeal_iff]
    exact (liftSeq G hG p _).isPrime.mem_or_mem hab

include hG in
/-- If the transition maps of a sequence of rings `G` induce surjections on prime spectra, then so
does the colimit inclusion `G 0 ⟶ colim G`. -/
theorem comap_colimit_ι_zero_surjective :
    Function.Surjective (comap (colimit.ι G 0).hom) := by
  intro p
  refine ⟨⟨colimitIdeal G hG p, isPrime_colimitIdeal G hG p⟩, PrimeSpectrum.ext ?_⟩
  ext y
  exact ι_mem_colimitIdeal_iff G hG p 0 y

end PrimeSpectrum
