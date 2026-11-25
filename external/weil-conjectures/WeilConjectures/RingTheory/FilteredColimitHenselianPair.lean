/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RingTheory.HenselianFactorizationCriterion
import WeilConjectures.RingTheory.FilteredColimitFactorizationDescent
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Filtered colimits of henselian pairs

Source: Stacks Project, More on Algebra, Lemma 0FWT (blueprint:
lem-weil-pbc-filtered-colimit-henselian-pair).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

/-- A directed colimit of henselian pairs is a henselian pair: for a nonempty directed set
`Λ`, a directed system of commutative rings `F` with ideals `J i` carried into each other by
the transition maps, every `(F.obj i, J i)` henselian, the union `I` of the images of the
`J i` in `colimit F` is an ideal, contained in the Jacobson radical, and `(colimit F, I)` is
henselian.
Source: Stacks Project, More on Algebra, Lemma 0FWT.
(blueprint: lem-weil-pbc-filtered-colimit-henselian-pair)

Proof sketch:
1. `Λ` is a filtered category, so every element of the colimit comes from a stage, two
   elements of stages agreeing in the colimit agree at a later stage, and the union of the
   images of the stage ideals is an ideal; an element of a stage landing in it lands in a
   stage ideal later on.
2. Each stage pair satisfies the factorization criterion (Stacks 09XI): its ideal lies in
   the Jacobson radical and coprime monic factorizations modulo it lift.
3. An element `u ∈ 1 + I` comes from some `1 + x` with `x ∈ J λ`, a unit at that stage,
   so `u` is a unit; hence `I` lies in the Jacobson radical.
4. A monic `f` over the colimit with a coprime monic factorization modulo `I` (the case
   of a zero quotient being trivial) descends with its factors and Bezout coefficients to
   one stage, where the factorization holds modulo the stage ideal after passing further.
5. Lift the factorization at that stage and map it to the colimit; by the factorization
   criterion `(colimit F, I)` is henselian. -/
theorem filteredColimit_henselianPair
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) [HasColimit F]
    (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (f : i ⟶ j),
      Ideal.map (F.map f).hom (J i) ≤ J j)
    (hH : ∀ i : Λ, HenselianRing (F.obj i) (J i)) :
    ∃ I : Ideal (colimit F : CommRingCat.{u}), (I : Set (colimit F : CommRingCat.{u})) =
      {x | ∃ (i : Λ) (a : F.obj i), (colimit.ι F i).hom a = x ∧ a ∈ J i} ∧
      I ≤ Ideal.jacobson ⊥ ∧ HenselianRing (colimit F : CommRingCat.{u}) I := by
  classical
  have transport {i j : Λ} (t : i ⟶ j) (a : F.obj i) :
      (colimit.ι F j).hom ((F.map t).hom a) = (colimit.ι F i).hom a :=
    ConcreteCategory.congr_hom (colimit.w F t) a
  have mem_map {i j : Λ} (t : i ⟶ j) {a : F.obj i} (ha : a ∈ J i) :
      (F.map t).hom a ∈ J j := hJ t (Ideal.mem_map_of_mem _ ha)
  let I : Ideal (colimit F : CommRingCat.{u}) :=
    { carrier := {x | ∃ (i : Λ) (a : F.obj i), (colimit.ι F i).hom a = x ∧ a ∈ J i}
      zero_mem' := by
        obtain ⟨i⟩ := ‹Nonempty Λ›
        exact ⟨i, 0, map_zero _, (J i).zero_mem⟩
      add_mem' := by
        rintro x y ⟨i, a, rfl, ha⟩ ⟨j, b, rfl, hb⟩
        let k := IsFiltered.max i j
        let t := IsFiltered.leftToMax i j
        let s := IsFiltered.rightToMax i j
        refine ⟨k, (F.map t).hom a + (F.map s).hom b, ?_,
          (J k).add_mem (mem_map t ha) (mem_map s hb)⟩
        rw [map_add, transport, transport]
      smul_mem' := by
        rintro r x ⟨i, a, rfl, ha⟩
        obtain ⟨j, b, rfl⟩ := Concrete.colimit_exists_rep F r
        let k := IsFiltered.max i j
        let t := IsFiltered.leftToMax i j
        let s := IsFiltered.rightToMax i j
        refine ⟨k, (F.map s).hom b * (F.map t).hom a, ?_,
          (J k).mul_mem_left _ (mem_map t ha)⟩
        rw [map_mul, transport, transport]
        rfl }
  have hI : ∀ x, x ∈ I ↔
      ∃ (i : Λ) (a : F.obj i), (colimit.ι F i).hom a = x ∧ a ∈ J i := fun _ => Iff.rfl
  have hRad : I ≤ Ideal.jacobson ⊥ := by
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨k, c, hc, hmem⟩ := (hI (x * y)).mp (I.mul_mem_right y hx)
    have hu := (Ideal.mem_jacobson_bot.mp ((hH k).jac hmem)) 1
    have hu' : IsUnit (c + 1) := by simpa using hu
    have := hu'.map (colimit.ι F k).hom
    simpa only [map_add, map_one, hc] using this
  refine ⟨I, rfl, hRad, ?_⟩
  apply (henselianRing_iff_factorization_criterion (colimit F : CommRingCat.{u}) I).2 hRad |>.2
  intro f hf g₀ h₀ hg₀ hh₀ hcop hfact
  obtain ⟨i, fᵢ, gᵢ, hᵢ, hfᵢ, hgᵢ, hhᵢ, hfi, hcopi, hfacti, hgi, hhi⟩ :=
    filteredColimit_factorization_descent F J hJ I hI f hf g₀ h₀ hg₀ hh₀ hcop hfact
  obtain ⟨g, h, hg, hh, hgh, hgm, hhm⟩ :=
    (henselianRing_iff_factorization_criterion (F.obj i) (J i)).1.mp (hH i) |>.2
      fᵢ hfᵢ (gᵢ.map (Ideal.Quotient.mk (J i))) (hᵢ.map (Ideal.Quotient.mk (J i)))
      (hgᵢ.map _) (hhᵢ.map _) hcopi hfacti
  let q : (F.obj i ⧸ J i) →+* ((colimit F : CommRingCat.{u}) ⧸ I) :=
    Ideal.Quotient.lift (J i) ((Ideal.Quotient.mk I).comp (colimit.ι F i).hom) (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hI _).mpr ⟨i, a, rfl, ha⟩))
  have hq : q.comp (Ideal.Quotient.mk (J i)) =
      (Ideal.Quotient.mk I).comp (colimit.ι F i).hom := by
    ext a
    rfl
  refine ⟨g.map (colimit.ι F i).hom, h.map (colimit.ι F i).hom,
    hg.map _, hh.map _, ?_, ?_, ?_⟩
  · rw [← Polynomial.map_mul, ← hgh, hfi]
  · have he := congrArg (Polynomial.map q) hgm
    simpa only [Polynomial.map_map, hq, ← hgi] using he
  · have he := congrArg (Polynomial.map q) hhm
    simpa only [Polynomial.map_map, hq, ← hhi] using he
