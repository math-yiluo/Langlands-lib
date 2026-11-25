/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Finite top cohomology of an m-pseudo-coherent complex

Source: Stacks Project, More on Algebra, Lemma 15.66.3 (1), Tag 064S
(blueprint: lem-sc-finite-cohomology).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- An `m`-pseudo-coherent complex with zero cohomology above `m` has finite type
cohomology in degree `m`. Rings are commutative with identity, including the zero ring,
as in the Stacks conventions (Tag 00AQ).
Source: Stacks Project, More on Algebra, Tag 064S (1)
(blueprint: lem-sc-finite-cohomology).

Proof:
1. Choose the bounded finite-free witness `E` mapping to `Q.obj K` supplied by
   `IsMPseudoCoherent`. Finite free modules are finite projective. The isomorphisms on
   cohomology above `m` and the vanishing hypothesis give zero cohomology of `E` above `m`.
2. If the top nonzero term of `E` is in degree `b > m`, vanishing of its top cohomology
   makes the differential to `E.X b` surjective. Projectivity splits it, so the
   preceding term is a direct sum of its kernel and `E.X b`. Cancel the resulting
   contractible two-term summand. The remaining terms are finite projective (they need
   not be free). Repeat until all terms above `m` vanish. If all terms vanish, or the
   top degree is below `m`, degree-`m` cohomology is zero. Otherwise it is a quotient
   of the finite module in degree `m`, hence is finite.
3. The witness map surjects on degree-`m` cohomology of `K`. A quotient of a finite
   module is finite. All three steps are the elementary steps of Tag 064S (1). -/
theorem finite_homology_of_isMPseudoCoherent {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ) (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hK : IsMPseudoCoherent m (Q.obj K))
    (hvan : ∀ i : ℤ, m < i →
      IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj K))) :
    Module.Finite R ((homologyFunctor (ModuleCat.{v} R) m).obj (Q.obj K)) := by
  obtain ⟨E, a, b, ha, hb, hfin, f, hiso, hepi⟩ := hK
  have hfree (i : ℤ) : Module.Free R (E.X i) := (hfin i).1
  have hfinite (i : ℤ) : Module.Finite R (E.X i) := (hfin i).2
  have hproj (i : ℤ) : Projective (E.X i) := inferInstance
  have hexact (i : ℤ) (hi : m < i) : E.ExactAt i := by
    have := hiso i hi
    have hz : IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj E)) :=
      (hvan i hi).of_iso (asIso ((homologyFunctor (ModuleCat.{v} R) i).map f))
    exact (E.exactAt_iff_isZero_homology i).2
      (hz.of_iso ((homologyFunctorFactors (ModuleCat.{v} R) i).app E).symm)
  -- Above m the witness is exact. Split the maps onto its cycles, descending
  -- from an upper bound, to make the degree-m cycles a retract of E.X m.
  let B := max m b
  have hB : E.IsStrictlyLE B := E.isStrictlyLE_of_le b B (le_max_right _ _)
  have hretract : ∀ (i : ℤ), i ≤ B → m ≤ i →
      Nonempty (Retract (E.cycles i) (E.X i)) := by
    apply Int.leInductionDown
    · intro _
      exact ⟨Retract.ofIso (E.iCyclesIso B (B + 1) (by simp)
        ((E.isZero_of_isStrictlyLE B (B + 1) (by omega)).eq_of_tgt _ _))⟩
    · intro n hn ih hmn
      obtain ⟨r⟩ := ih (by omega)
      have : Projective (E.cycles n) := r.projective
      have he : (E.sc' (n - 1) n (n + 1)).Exact :=
        (E.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).1
          (hexact n (by omega))
      have hep : Epi (E.toCycles (n - 1) n) := by
        have := he.epi_toCycles
        have hcomp := E.toCycles_cyclesIsoSc'_hom (n - 1) n (n + 1)
          (by simp) (by simp)
        have hc : Epi (E.toCycles (n - 1) n ≫
            (E.cyclesIsoSc' (n - 1) n (n + 1) (by simp) (by simp)).hom) :=
          hcomp.symm ▸ he.epi_toCycles
        exact (epi_comp_iff_of_isIso _ _).1 hc
      let s := Projective.factorThru (𝟙 (E.cycles n)) (E.toCycles (n - 1) n)
      have hs : s ≫ E.toCycles (n - 1) n = 𝟙 _ := by
        exact Projective.factorThru_comp _ _
      have hz : (𝟙 (E.X (n - 1)) - E.toCycles (n - 1) n ≫ s) ≫
          E.d (n - 1) n = 0 := by
        rw [Preadditive.sub_comp, Category.id_comp]
        have hd : s ≫ E.d (n - 1) n = E.iCycles n := by
          rw [← E.toCycles_i (n - 1) n, ← Category.assoc, hs, Category.id_comp]
        rw [Category.assoc, hd, E.toCycles_i, sub_self]
      let t := E.liftCycles (𝟙 (E.X (n - 1)) - E.toCycles (n - 1) n ≫ s)
        n (by simp) hz
      refine ⟨⟨E.iCycles (n - 1), t, ?_⟩⟩
      apply (cancel_mono (E.iCycles (n - 1))).1
      dsimp [t]
      rw [Category.assoc, E.liftCycles_i]
      have hz' : E.iCycles (n - 1) ≫ E.toCycles (n - 1) n = 0 := by
        apply (cancel_mono (E.iCycles n)).1
        simp
      simp [Preadditive.comp_sub, ← Category.assoc, hz']
  -- Cycles are finite as a retract of a finite term. Both homology and the
  -- target homology are quotients of these cycles.
  obtain ⟨r⟩ := hretract m (le_max_left _ _) le_rfl
  have : Module.Finite R (E.cycles m) :=
    Module.Finite.of_surjective r.r.hom ((ModuleCat.epi_iff_surjective r.r).1 inferInstance)
  have : Module.Finite R (E.homology m) :=
    Module.Finite.of_surjective (E.homologyπ m).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  have : Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℤ) m).obj E) :=
    ‹Module.Finite R (E.homology m)›
  have : Module.Finite R ((homologyFunctor (ModuleCat.{v} R) m).obj (Q.obj E)) :=
    Module.Finite.of_surjective ((homologyFunctorFactors (ModuleCat.{v} R) m).inv.app E).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.Finite.of_surjective ((homologyFunctor (ModuleCat.{v} R) m).map f).hom
    ((ModuleCat.epi_iff_surjective _).1 hepi)

end DerivedCategory
