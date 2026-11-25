/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # A flat stage from a persistent open cover

Source: Stacks Project, Tag 02JO (1), proof paragraphs 2--3.
(blueprint: lem-pc-finite-type-approximation-flat-stage)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

-- Descend ideal membership by lifting coefficients and taking common upper bounds.
private theorem ideal_mem_lift
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (F : Λ ⥤ CommRingCat.{u}) (S : Type u) [CommRing S]
    (κ : F ⟶ (Functor.const Λ).obj (CommRingCat.of S))
    (hc : IsColimit (Cocone.mk (CommRingCat.of S) κ))
    (i : Λ) (J : Ideal (F.obj i)) (s : S)
    (hs : s ∈ J.map (κ.app i).hom) :
    ∃ (j : Λ) (h : i ≤ j) (x : F.obj j),
      x ∈ J.map (F.map (homOfLE h)).hom ∧ (κ.app j).hom x = s := by
  classical
  change s ∈ Ideal.span ((κ.app i).hom '' (J : Set (F.obj i))) at hs
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨x, hx, rfl⟩ := hs
    refine ⟨i, le_refl i, x, ?_, rfl⟩
    simpa using hx
  | zero => exact ⟨i, le_refl i, 0, Ideal.zero_mem _, map_zero _⟩
  | add x y hx hy hx' hy' =>
    obtain ⟨j, hij, xj, hxj, exj⟩ := hx'
    obtain ⟨k, hik, yk, hyk, eyk⟩ := hy'
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
    refine ⟨l, hij.trans hjl,
      (F.map (homOfLE hjl)).hom xj + (F.map (homOfLE hkl)).hom yk, ?_, ?_⟩
    · apply Ideal.add_mem
      · have h := Ideal.mem_map_of_mem (F.map (homOfLE hjl)).hom hxj
        simpa only [Ideal.map_map, ← CommRingCat.hom_comp, ← F.map_comp,
          homOfLE_comp] using h
      · have h := Ideal.mem_map_of_mem (F.map (homOfLE hkl)).hom hyk
        simpa only [Ideal.map_map, ← CommRingCat.hom_comp, ← F.map_comp,
          homOfLE_comp] using h
    · rw [map_add]
      have ej := ConcreteCategory.congr_hom (κ.naturality (homOfLE hjl)) xj
      have ek := ConcreteCategory.congr_hom (κ.naturality (homOfLE hkl)) yk
      change (κ.app l).hom ((F.map (homOfLE hjl)).hom xj) = (κ.app j).hom xj at ej
      change (κ.app l).hom ((F.map (homOfLE hkl)).hom yk) = (κ.app k).hom yk at ek
      rw [ej, ek, exj, eyk]
  | smul r x hx hx' =>
    obtain ⟨j, hij, xj, hxj, exj⟩ := hx'
    obtain ⟨k, rk, erk⟩ := Concrete.isColimit_exists_rep F hc r
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
    refine ⟨l, hij.trans hjl,
      (F.map (homOfLE hkl)).hom rk * (F.map (homOfLE hjl)).hom xj, ?_, ?_⟩
    · apply Ideal.mul_mem_left
      have h := Ideal.mem_map_of_mem (F.map (homOfLE hjl)).hom hxj
      simpa only [Ideal.map_map, ← CommRingCat.hom_comp, ← F.map_comp,
        homOfLE_comp] using h
    · rw [map_mul]
      have ej := ConcreteCategory.congr_hom (κ.naturality (homOfLE hjl)) xj
      have ek := ConcreteCategory.congr_hom (κ.naturality (homOfLE hkl)) rk
      change (κ.app l).hom ((F.map (homOfLE hjl)).hom xj) = (κ.app j).hom xj at ej
      change (κ.app l).hom ((F.map (homOfLE hkl)).hom rk) = (κ.app k).hom rk at ek
      change (κ.app k).hom rk = r at erk
      rw [ej, ek, exj, erk]
      rfl

-- Descend the equality between the lifted unit-ideal element and one.
private theorem ideal_unit_descends
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (F : Λ ⥤ CommRingCat.{u}) (S : Type u) [CommRing S]
    (κ : F ⟶ (Functor.const Λ).obj (CommRingCat.of S))
    (hc : IsColimit (Cocone.mk (CommRingCat.of S) κ))
    (i : Λ) (J : Ideal (F.obj i)) (hJ : J.map (κ.app i).hom = ⊤) :
    ∃ (j : Λ) (h : i ≤ j), J.map (F.map (homOfLE h)).hom = ⊤ := by
  obtain ⟨j, hij, x, hx, ex⟩ := ideal_mem_lift F S κ hc i J 1
    (by rw [hJ]; trivial)
  obtain ⟨k, f, g, e⟩ := Concrete.isColimit_exists_of_rep_eq F hc x (1 : F.obj j)
    (by change (κ.app j).hom x = (κ.app j).hom 1; simpa only [map_one] using ex)
  refine ⟨k, hij.trans (leOfHom f), (Ideal.eq_top_iff_one _).mpr ?_⟩
  have h := Ideal.mem_map_of_mem (F.map f).hom hx
  have e' : (F.map f).hom x = 1 := by simpa using e
  rw [e'] at h
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, ← F.map_comp,
    Subsingleton.elim (homOfLE hij ≫ f) (homOfLE (hij.trans (leOfHom f)))] using h

/-- A persistent open flat cover at a ring colimit yields a globally flat stage.

Source: Stacks Project, Tag 02JO (1), proof paragraphs 2--3.
(blueprint: lem-pc-finite-type-approximation-flat-stage)

Proof:
Pull the supplied open sets U_i back to Spec(S). Cocone naturality and persistence
make these inverse images a directed open family; the supplied pointwise covering
and compactness select i whose inverse image is all Spec(S). Write the closed
complement of U_i as V(J). Its extension to S has empty zero locus, hence equals
the unit ideal. Induction on ideal-span membership lifts an element of the extended
ideal to the image ideal at a later stage: generators already come from stage i,
addition uses a common upper bound, and scalar multiplication lifts the coefficient
using ring-colimit representatives. Apply this to 1, then descend its equality to 1
using the eventual-equality criterion for the ring colimit. At this stage J is the
unit ideal. A prime outside its open set would contract into V(J) and therefore
contain this unit ideal, a contradiction. Thus every stage prime is in its open
set and its module localization is flat over its stage base. The maximal-prime
localization criterion gives the whole module flat. The restricted base action on
the localization agrees with the localization of the restricted action, checked
on fractions. This proof also handles empty limit spectra and zero stage rings.
-/
theorem exists_flat_finiteType_approximation_stage
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (S : Type u) [CommRing S]
    (A B : Λ ⥤ CommRingCat.{u}) (D : Λ ⥤ AddCommGrpCat.{v})
    [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
    (hc : IsColimit (Cocone.mk (CommRingCat.of S) κ))
    (U : (i : Λ) → Set (PrimeSpectrum (B.obj i)))
    (hUopen : ∀ i, IsOpen (U i))
    (hUflat : ∀ i (q : PrimeSpectrum (B.obj i)), q ∈ U i →
      letI : Module (A.obj i) (LocalizedModule q.asIdeal.primeCompl (D.obj i)) :=
        Module.compHom _ (φ i)
      Module.Flat (A.obj i) (LocalizedModule q.asIdeal.primeCompl (D.obj i)))
    (hUpersist : ∀ (i j : Λ) (h : i ≤ j),
      PrimeSpectrum.comap (B.map (homOfLE h)).hom ⁻¹' U i ⊆ U j)
    (hUcover : ∀ q : PrimeSpectrum S, ∃ i, PrimeSpectrum.comap (κ.app i).hom q ∈ U i) :
    ∃ i : Λ, letI : Module (A.obj i) (D.obj i) := Module.compHom (D.obj i) (φ i)
      Module.Flat (A.obj i) (D.obj i) := by
  classical
  let V (i : Λ) : Set (PrimeSpectrum S) := PrimeSpectrum.comap (κ.app i).hom ⁻¹' U i
  have hVo (i : Λ) : IsOpen (V i) :=
    (hUopen i).preimage (PrimeSpectrum.continuous_comap _)
  have hVmono {i j : Λ} (h : i ≤ j) : V i ⊆ V j := by
    intro q hq
    apply hUpersist i j h
    change PrimeSpectrum.comap (B.map (homOfLE h)).hom
      (PrimeSpectrum.comap (κ.app j).hom q) ∈ U i
    have hc := ConcreteCategory.congr_hom (κ.naturality (homOfLE h))
    have he : (κ.app j).hom.comp (B.map (homOfLE h)).hom = (κ.app i).hom := by
      ext x
      exact hc x
    have hcomp : PrimeSpectrum.comap (B.map (homOfLE h)).hom
        (PrimeSpectrum.comap (κ.app j).hom q) = PrimeSpectrum.comap (κ.app i).hom q := by
      apply PrimeSpectrum.ext
      change q.asIdeal.comap ((κ.app j).hom.comp (B.map (homOfLE h)).hom) = _
      rw [he]
      rfl
    rw [hcomp]
    exact hq
  obtain ⟨i, hi⟩ := isCompact_univ.elim_directed_cover V hVo
    (fun q _ ↦ Set.mem_iUnion.mpr (hUcover q)) (fun j k ↦ by
      obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
      exact ⟨l, hVmono hjl, hVmono hkl⟩)
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp (hUopen i).isClosed_compl
  have hJS : J.map (κ.app i).hom = ⊤ := by
    apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hle : J ≤ q.asIdeal.comap (κ.app i).hom :=
      Ideal.map_le_iff_le_comap.mp hq
    have hnot : PrimeSpectrum.comap (κ.app i).hom q ∈ (U i)ᶜ := by
      rw [hJ]
      exact hle
    exact hnot (hi (Set.mem_univ q))
  obtain ⟨j, hij, hJj⟩ := ideal_unit_descends B S κ hc i J hJS
  have hUj : ∀ q : PrimeSpectrum (B.obj j), q ∈ U j := by
    intro q
    apply hUpersist i j hij
    change PrimeSpectrum.comap (B.map (homOfLE hij)).hom q ∈ U i
    by_contra hn
    have hmem : PrimeSpectrum.comap (B.map (homOfLE hij)).hom q ∈
        PrimeSpectrum.zeroLocus (J : Set (B.obj i)) := by
      rw [← hJ]
      exact hn
    have hle : J.map (B.map (homOfLE hij)).hom ≤ q.asIdeal :=
      Ideal.map_le_iff_le_comap.mpr hmem
    rw [hJj] at hle
    exact q.isPrime.ne_top (top_le_iff.mp hle)
  refine ⟨j, ?_⟩
  let : Module (A.obj j) (D.obj j) := Module.compHom (D.obj j) (φ j)
  let : Algebra (A.obj j) (B.obj j) := (φ j).toAlgebra
  have : IsScalarTower (A.obj j) (B.obj j) (D.obj j) :=
    IsScalarTower.of_compHom _ _ _
  apply Module.flat_of_isLocalized_maximal (B.obj j) (D.obj j)
    (fun P _ ↦ LocalizedModule P.primeCompl (D.obj j))
    (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl (D.obj j))
  intro P hP
  let : P.IsPrime := hP.isPrime
  let μ' : Module (A.obj j) (LocalizedModule P.primeCompl (D.obj j)) := inferInstance
  let μ : Module (A.obj j) (LocalizedModule P.primeCompl (D.obj j)) :=
    Module.compHom _ (φ j)
  have hμ : μ = μ' := by
    apply Module.ext'
    intro a x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      change ((φ j) a) • LocalizedModule.mk m s =
        @HSMul.hSMul _ _ _ (@instHSMul _ _ μ'.toSMul) a (LocalizedModule.mk m s)
      simp only [LocalizedModule.smul'_mk]
      rfl
  have hf := hUflat j ⟨P, inferInstance⟩ (hUj ⟨P, inferInstance⟩)
  change @Module.Flat _ _ _ _ μ at hf
  rw [hμ] at hf
  exact hf

end Algebra
