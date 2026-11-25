/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.FiniteLocalizationFreeStep
import WeilConjectures.RingTheory.StabilizedFiniteFreeTower

/-! # Finite-free models at finitely many localizations

Source: Stacks Project, Tag 08EE, descending construction in the proof of
lemma-lift-pseudo-coherent (blueprint: lem-sc-finite-localization-free-model).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace DerivedCategory

/-- A finite family of pseudo-coherent localizations admits a single bounded-above
finite-free complex mapping to the original complex by a quasi-isomorphism at each
of those localizations. The elements need not generate the unit ideal.

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent, descending
construction and denominator clearing (blueprint: lem-sc-finite-localization-free-model).

Proof:
Choose a common upper cohomology bound b for the finitely many localized models.
Start at cutoff n = b+1 with F = 0 and its zero map to M. At degree n
maintain that F is zero below n, finite free and bounded above, and that its map
induces localized cohomology isomorphisms above n and surjections in degree n.
The cone has localized cohomology zero in degrees at least n. Its localizations
are (n-1)-pseudo-coherent by Tag 064R: localized F is n-pseudo-coherent
because it is bounded finite free, and truncation of each local finite-free
model of M gives (n-1)-pseudo-coherence. Tag 064S then
makes their degree-(n-1) cohomology finite. Choose finitely many generators at
all localizations. Clear denominators of representatives in the cone and multiply
by further powers of the corresponding element to make their differentials zero
globally. These powers are units at that localization, so the representatives
still generate there. Their direct sum defines a finite-free module F in degree
n-1 mapping to cone cycles. The two cone components define the new component
of the map to M and the negative of the new differential. The cycle equation
proves the chain-map and square-zero equations. The cone cohomology sequence
proves the induction invariant one degree lower. Iterate downward, keeping all
previously constructed degrees fixed. The resulting complex retains the initial
upper bound, has finite-free terms, and its localized map is an isomorphism on
cohomology in every degree. For an empty family take the zero complex; zero
localizations impose no conditions, and the same construction applies to a zero ring.
-/
theorem exists_finite_localization_free_model (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w} (ModuleCat.{u} (Localization.Away (f i)))]
    (hlocal : ∀ i : Fin r, IsPseudoCoherent
      (Q.obj ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
        (ComplexShape.up ℤ)).obj M))) :
    ∃ (F : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ), F.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free A (F.X i) ∧ Module.Finite A (F.X i)) ∧
      ∃ α : F ⟶ M, ∀ j : Fin r, QuasiIso
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
          (ComplexShape.up ℤ)).map α) := by
  classical
  by_cases hr : r = 0
  · subst r
    let Z : CochainComplex (ModuleCat.{u} A) ℤ := HomologicalComplex.zero
    refine ⟨Z, 0, ?_, ?_, 0, ?_⟩
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i _
      exact CategoryTheory.Limits.isZero_zero _
    · intro i
      have : Subsingleton (Z.X i) :=
        ModuleCat.subsingleton_of_isZero (CategoryTheory.Limits.isZero_zero _)
      exact ⟨Module.Free.of_subsingleton _ _, inferInstance⟩
    · intro j
      exact Fin.elim0 j
  let L (j : Fin r) := Functor.mapHomologicalComplex
    (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
    (ComplexShape.up ℤ)
  have hbound (j : Fin r) : ∃ b : ℤ, CochainComplex.IsLE ((L j).obj M) b := by
    obtain ⟨E, b, hb, _, ⟨e⟩⟩ := hlocal j
    have : (Q.obj E).IsLE b := by
      have : E.IsStrictlyLE b := hb
      infer_instance
    have : (Q.obj ((L j).obj M)).IsLE b := TStructure.t.isLE_of_iso e b
    exact ⟨b, (isLE_Q_obj_iff _ _).mp this⟩
  choose bounds hbounds using hbound
  obtain ⟨b, hb⟩ := (Set.finite_range bounds).bddAbove
  have hvan (j : Fin r) (i : ℤ) (hi : b < i) : ((L j).obj M).ExactAt i := by
    have : CochainComplex.IsLE ((L j).obj M) (bounds j) := hbounds j
    exact CochainComplex.exactAt_of_isLE ((L j).obj M) (bounds j) i
      (lt_of_le_of_lt (hb (Set.mem_range_self j)) hi)
  let S (k : ℕ) := {p : Σ F : CochainComplex (ModuleCat.{u} A) ℤ, F ⟶ M //
    p.1.IsStrictlyLE b ∧ p.1.IsStrictlyGE (b + 1 - (k : ℤ)) ∧
    (∀ i : ℤ, Module.Free A (p.1.X i) ∧ Module.Finite A (p.1.X i)) ∧
    (∀ j : Fin r, ∀ i : ℤ, b + 1 - (k : ℤ) < i → QuasiIsoAt ((L j).map p.2) i) ∧
    (∀ j : Fin r, Epi (HomologicalComplex.homologyMap
      ((L j).map p.2) (b + 1 - (k : ℤ))))}
  let Z : CochainComplex (ModuleCat.{u} A) ℤ := HomologicalComplex.zero
  have hZ : CategoryTheory.Limits.IsZero Z := HomologicalComplex.isZero_zero
  have hzterm (i : ℤ) : CategoryTheory.Limits.IsZero (Z.X i) := CategoryTheory.Limits.isZero_zero _
  have hzfinite (i : ℤ) : Module.Free A (Z.X i) ∧ Module.Finite A (Z.X i) := by
    have : Subsingleton (Z.X i) := ModuleCat.subsingleton_of_isZero (hzterm i)
    exact ⟨Module.Free.of_subsingleton _ _, inferInstance⟩
  have hzexact (j : Fin r) (i : ℤ) : ((L j).obj Z).ExactAt i := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (HomologicalComplex.homologyFunctor _ _ i).map_isZero ((L j).map_isZero hZ)
  let s₀ : S 0 := ⟨⟨Z, 0⟩, by
    refine ⟨?_, ?_, hzfinite, ?_, ?_⟩
    · rw [CochainComplex.isStrictlyLE_iff]
      exact fun i _ ↦ hzterm i
    · rw [CochainComplex.isStrictlyGE_iff]
      exact fun i _ ↦ hzterm i
    · intro j i hi
      apply (quasiIsoAt_iff_exactAt _ i (hzexact j i)).mpr
      exact hvan j i (by omega)
    · intro j
      exact (hvan j _ (by omega)).isZero_homology.epi _⟩
  have hnext (k : ℕ) (s : S k) : ∃ t : S (k + 1),
      ∃ τ : s.val.1 ⟶ t.val.1, τ ≫ t.val.2 = s.val.2 ∧
        ∀ i : ℤ, b + 1 - (k : ℤ) ≤ i → IsIso (τ.f i) := by
    obtain ⟨G, β, hu, hl, hf, hi, he, τ, hc, ht⟩ :=
      exists_finite_localization_free_step A M r f hlocal b (b + 1 - (k : ℤ))
        (by omega) s.val.1 s.val.2 s.property.1 s.property.2.1 s.property.2.2.1
        s.property.2.2.2.1 s.property.2.2.2.2
    have hcut : b + 1 - ((k + 1 : ℕ) : ℤ) = b + 1 - (k : ℤ) - 1 := by omega
    refine ⟨⟨⟨G, β⟩, ?_⟩, τ, hc, ht⟩
    exact ⟨hu, hcut.symm ▸ hl, hf, hcut.symm ▸ hi, hcut.symm ▸ he⟩
  let next (k : ℕ) (s : S k) : S (k + 1) := Classical.choose (hnext k s)
  let seq : (k : ℕ) → S k := fun k ↦ Nat.rec s₀ (fun k s ↦ next k s) k
  have htrans (k : ℕ) : ∃ τ : (seq k).val.1 ⟶ (seq (k + 1)).val.1,
      τ ≫ (seq (k + 1)).val.2 = (seq k).val.2 ∧
        ∀ i : ℤ, b + 1 - (k : ℤ) ≤ i → IsIso (τ.f i) :=
    Classical.choose_spec (hnext k (seq k))
  choose τ hcomm hstable using htrans
  obtain ⟨F, hF, hfin, α, hα⟩ :=
    CochainComplex.exists_model_of_stabilized_finite_free_tower A M r f b
    (fun k ↦ (seq k).val.1) (fun k ↦ (seq k).val.2) τ
    (fun k ↦ (seq k).property.1) (fun k ↦ (seq k).property.2.2.1)
    hcomm hstable (fun k ↦ (seq k).property.2.2.2.1)
  exact ⟨F, b, hF, hfin, α, hα⟩

end DerivedCategory
