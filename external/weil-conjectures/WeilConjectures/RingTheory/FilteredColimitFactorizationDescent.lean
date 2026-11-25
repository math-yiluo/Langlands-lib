/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Polynomial.Lifts

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

-- Move a finite set of coefficients to a common upper bound.
private theorem finite_elements_stage
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) [HasColimit F]
    (s : Finset (colimit F : CommRingCat.{u})) :
    ∃ i : Λ, ∀ x ∈ s, ∃ a : F.obj i, (colimit.ι F i).hom a = x := by
  classical
  choose k a ha using fun x : (colimit F : CommRingCat.{u}) ↦
    Concrete.colimit_exists_rep F x
  obtain ⟨i, hi⟩ := (s.image k).exists_le
  refine ⟨i, fun x hx ↦ ?_⟩
  let e : k x ⟶ i := homOfLE (hi _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  refine ⟨(F.map e).hom (a x), ?_⟩
  exact (ConcreteCategory.congr_hom (colimit.w F e) (a x)).trans (ha x)

-- Once all coefficients lift, Mathlib supplies lifts preserving monicity.
private theorem finite_polynomials_stage
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) [HasColimit F]
    {n : ℕ} (p : Fin n → (colimit F : CommRingCat.{u})[X]) :
    ∃ (i : Λ) (q : Fin n → (F.obj i)[X]),
      (∀ k, (q k).map (colimit.ι F i).hom = p k) ∧
      (∀ k, (p k).Monic → (q k).Monic) := by
  classical
  let s := Finset.univ.biUnion fun k : Fin n ↦ (p k).support.image (p k).coeff
  obtain ⟨i, hi⟩ := finite_elements_stage F s
  have hl (k : Fin n) : p k ∈ Polynomial.lifts (colimit.ι F i).hom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro m
    by_cases hm : (p k).coeff m = 0
    · exact ⟨0, by simp [hm]⟩
    · exact hi _ (Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_univ _, Finset.mem_image.mpr
          ⟨m, Polynomial.mem_support_iff.mpr hm, rfl⟩⟩)
  have hq (k : Fin n) : ∃ q : (F.obj i)[X],
      q.map (colimit.ι F i).hom = p k ∧ ((p k).Monic → q.Monic) := by
    by_cases hk : (p k).Monic
    · obtain ⟨q, hq, _, hmonic⟩ :=
        Polynomial.lifts_and_natDegree_eq_and_monic (hl k) hk
      exact ⟨q, hq, fun _ ↦ hmonic⟩
    · obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp (hl k)
      exact ⟨q, hq, fun h ↦ (hk h).elim⟩
  choose q hmap hmonic using hq
  exact ⟨i, q, hmap, hmonic⟩

-- Compare with an ideal representative in the colimit, then use compatibility.
private theorem eventually_mem_stage_ideal
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) [HasColimit F]
    (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (e : i ⟶ j), Ideal.map (F.map e).hom (J i) ≤ J j)
    (I : Ideal (colimit F : CommRingCat.{u}))
    (hI : ∀ x, x ∈ I ↔
      ∃ (i : Λ) (a : F.obj i), (colimit.ι F i).hom a = x ∧ a ∈ J i)
    {i : Λ} (x : F.obj i) (hx : (colimit.ι F i).hom x ∈ I) :
    ∃ (j : Λ) (e : i ⟶ j), (F.map e).hom x ∈ J j := by
  obtain ⟨k, a, ha, hak⟩ := (hI _).mp hx
  obtain ⟨j, e, e', he⟩ := Concrete.colimit_exists_of_rep_eq F x a ha.symm
  exact ⟨j, e, he ▸ hJ e' (Ideal.mem_map_of_mem (F.map e').hom hak)⟩

-- Make all coefficients of finitely many relations vanish in one stage quotient.
private theorem finite_polynomial_relations_stage
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) [HasColimit F]
    (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (e : i ⟶ j), Ideal.map (F.map e).hom (J i) ≤ J j)
    (I : Ideal (colimit F : CommRingCat.{u}))
    (hI : ∀ x, x ∈ I ↔
      ∃ (i : Λ) (a : F.obj i), (colimit.ι F i).hom a = x ∧ a ∈ J i)
    {i : Λ} {n : ℕ} (p : Fin n → (F.obj i)[X])
    (hp : ∀ k, ((p k).map (colimit.ι F i).hom).map (Ideal.Quotient.mk I) = 0) :
    ∃ (j : Λ) (e : i ⟶ j),
      ∀ k, ((p k).map (F.map e).hom).map (Ideal.Quotient.mk (J j)) = 0 := by
  classical
  let s := Finset.univ.biUnion fun k : Fin n ↦ (p k).support.image (p k).coeff
  have hs (x : F.obj i) (hx : x ∈ s) : (colimit.ι F i).hom x ∈ I := by
    obtain ⟨k, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa using congrArg (fun q ↦ q.coeff m) (hp k)
  choose j e hj using fun x : s ↦ eventually_mem_stage_ideal F J hJ I hI x.1 (hs _ x.2)
  obtain ⟨l, hl⟩ := (insert i (Finset.univ.image j)).exists_le
  let e₀ : i ⟶ l := homOfLE (hl i (Finset.mem_insert_self _ _))
  have hmem (x : F.obj i) (hx : x ∈ s) : (F.map e₀).hom x ∈ J l := by
    let e₁ : j ⟨x, hx⟩ ⟶ l := homOfLE
      (hl _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩)))
    have he : e ⟨x, hx⟩ ≫ e₁ = e₀ := Subsingleton.elim _ _
    have hm := hJ e₁ (Ideal.mem_map_of_mem (F.map e₁).hom (hj ⟨x, hx⟩))
    change (F.map (e ⟨x, hx⟩) ≫ F.map e₁).hom x ∈ J l at hm
    simpa only [← F.map_comp, he] using hm
  refine ⟨l, e₀, fun k ↦ ?_⟩
  ext m
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  by_cases hm : (p k).coeff m = 0
  · simp [hm]
  · exact hmem _ (Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_univ _, Finset.mem_image.mpr
        ⟨m, Polynomial.mem_support_iff.mpr hm, rfl⟩⟩)

/-- Finite monic factorization data modulo the union of compatible ideals descends to
one stage. No henselian hypothesis is needed.
Source: Stacks Project, More on Algebra, Lemma 0FWT, second paragraph of the proof.
(blueprint: lem-weil-pbc-filtered-colimit-factorization-descent)

Proof: every colimit element has a stage representative. Finitely many representatives
can be moved to one common stage. If a stage element maps into I, express its image as
the image of an element of some J j; equality in a filtered colimit holds at a later
stage, where compatibility puts the original element into the stage ideal. The same
holds simultaneously for finitely many elements.
If A/I is nonzero, write f and its two monic factors as powers of X plus lower terms.
Choose representatives in A of the lower coefficients of the factors and of two Bezout
polynomials witnessing coprimality. Descend these and the lower coefficients of f to
one stage, keeping the leading coefficients exactly 1. The coefficients of F-GH and
1-GG'-HH' map into I; move further until all lie in the stage ideal. Reduction there
gives the required factorization and Bezout relation. Mapping back gives the prescribed
factors. If A/I is zero, first move to a stage where 1 belongs to J (using the preceding
membership argument applied to 1); descend f monically and take G=H=1. The stage quotient
and A/I are zero rings, so all factorization, coprimality and image requirements hold.
If A itself is zero, f=0 and one can take F=1 at the chosen stage. -/
theorem filteredColimit_factorization_descent
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) [HasColimit F]
    (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (f : i ⟶ j), Ideal.map (F.map f).hom (J i) ≤ J j)
    (I : Ideal (colimit F : CommRingCat.{u}))
    (hI : ∀ x, x ∈ I ↔
      ∃ (i : Λ) (a : F.obj i), (colimit.ι F i).hom a = x ∧ a ∈ J i)
    (f : (colimit F : CommRingCat.{u})[X]) (hf : f.Monic)
    (g₀ h₀ : ((colimit F : CommRingCat.{u}) ⧸ I)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hfact : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ (i : Λ) (fᵢ gᵢ hᵢ : (F.obj i)[X]),
      fᵢ.Monic ∧ gᵢ.Monic ∧ hᵢ.Monic ∧ fᵢ.map (colimit.ι F i).hom = f ∧
      IsCoprime (gᵢ.map (Ideal.Quotient.mk (J i))) (hᵢ.map (Ideal.Quotient.mk (J i))) ∧
      fᵢ.map (Ideal.Quotient.mk (J i)) =
        gᵢ.map (Ideal.Quotient.mk (J i)) * hᵢ.map (Ideal.Quotient.mk (J i)) ∧
      (gᵢ.map (colimit.ι F i).hom).map (Ideal.Quotient.mk I) = g₀ ∧
      (hᵢ.map (colimit.ι F i).hom).map (Ideal.Quotient.mk I) = h₀ := by
  classical
  obtain ⟨g, hg, _, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (Ideal.Quotient.mk_surjective (I := I)) g₀) hg₀
  obtain ⟨h, hh, _, hhm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (Ideal.Quotient.mk_surjective (I := I)) h₀) hh₀
  obtain ⟨a₀, b₀, hbez⟩ := hcop
  obtain ⟨a, ha⟩ := Polynomial.map_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective a₀
  obtain ⟨b, hb⟩ := Polynomial.map_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective b₀
  -- Descend the polynomial, the two factors, and the two Bezout witnesses together.
  let p : Fin 5 → (colimit F : CommRingCat.{u})[X] := ![f, g, h, a, b]
  obtain ⟨i, q, hq, hqm⟩ := finite_polynomials_stage F p
  have hm₀ : (q 0).Monic := hqm 0 hf
  have hm₁ : (q 1).Monic := hqm 1 hgm
  have hm₂ : (q 2).Monic := hqm 2 hhm
  -- These two relations encode the factorization and the Bezout identity.
  let r : Fin 2 → (F.obj i)[X] :=
    ![q 0 - q 1 * q 2, q 3 * q 1 + q 4 * q 2 - 1]
  have hr (k : Fin 2) :
      ((r k).map (colimit.ι F i).hom).map (Ideal.Quotient.mk I) = 0 := by
    fin_cases k
    · simp [r, hq, p, hg, hh, hfact]
    · simp [r, hq, p, hg, hh, ha, hb, hbez]
  obtain ⟨j, e, hrel⟩ := finite_polynomial_relations_stage F J hJ I hI r hr
  have hmap (k : Fin 5) :
      ((q k).map (F.map e).hom).map (colimit.ι F j).hom = p k := by
    rw [Polynomial.map_map]
    have he : (colimit.ι F j).hom.comp (F.map e).hom = (colimit.ι F i).hom :=
      congrArg CommRingCat.Hom.hom (colimit.w F e)
    rw [he, hq]
  refine ⟨j, (q 0).map (F.map e).hom, (q 1).map (F.map e).hom,
    (q 2).map (F.map e).hom, hm₀.map _, hm₁.map _, hm₂.map _, hmap 0, ?_, ?_, ?_, ?_⟩
  · refine ⟨((q 3).map (F.map e).hom).map (Ideal.Quotient.mk (J j)),
      ((q 4).map (F.map e).hom).map (Ideal.Quotient.mk (J j)), ?_⟩
    have hr₁ := hrel 1
    simpa only [r, Matrix.cons_val_one, Matrix.cons_val_zero, Polynomial.map_sub,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, sub_eq_zero] using hr₁
  · have hr₀ := hrel 0
    simpa only [r, Matrix.cons_val_zero, Polynomial.map_sub, Polynomial.map_mul,
      sub_eq_zero] using hr₀
  · rw [hmap 1]
    exact hg
  · rw [hmap 2]
    exact hh
