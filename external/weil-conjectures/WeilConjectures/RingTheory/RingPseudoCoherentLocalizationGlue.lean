/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.HomologyVanishingLocalizationSpan
import WeilConjectures.RingTheory.MPseudoCoherentLocalizationConeStep

/-!
# Gluing pseudo-coherence over a finite standard-open cover

Source: Stacks Project, More on Algebra, Lemma 15.66.14 (Tag 066D), with Definition 064P
and Lemma 064U (blueprint: lem-pc-ring-pseudo-coherent-localization-glue).
-/

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory

namespace DerivedCategory

private theorem isMPseudoCoherent_boundedAbove
    {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    (m : ℤ) (C : DerivedCategory (ModuleCat.{v₁} R)) (hC : IsMPseudoCoherent m C) :
    ∃ n : ℤ, ∀ j : ℤ, n < j → Limits.IsZero ((homologyFunctor (ModuleCat.{v₁} R) j).obj C) := by
  obtain ⟨E, a, b, hge, hle, hfree, α, hiso, hepi⟩ := hC
  have : E.IsStrictlyLE b := hle
  have : (Q.obj E).IsLE b := inferInstance
  refine ⟨max m b, fun j hj ↦ ?_⟩
  have : IsIso ((homologyFunctor (ModuleCat.{v₁} R) j).map α) :=
    hiso j (lt_of_le_of_lt (le_max_left m b) hj)
  exact (isZero_of_isLE (Q.obj E) b j
    (lt_of_le_of_lt (le_max_right m b) hj)).of_iso
      (asIso ((homologyFunctor (ModuleCat.{v₁} R) j).map α)).symm

/-- Pseudo-coherence, including fixed-degree pseudo-coherence, glues under localization at
finitely many elements generating the unit ideal. Rings are commutative, as in Stacks.
Source: Stacks Project, Tag 066D
(blueprint: lem-pc-ring-pseudo-coherent-localization-glue).

Proof:
1. Fix `m`. Exactness of localization identifies localized cohomology with the cohomology of
   the localized complex. The finitely many bounded approximations give a common upper bound
   for local cohomology; unit-ideal generation detects vanishing globally. Induct on the top
   degree minus `m`. If all cohomology in degrees at least `m` vanishes, use
   `lem-pc-ring-m-pseudo-coherent-vanishing-base` (Tag 064W).
2. Otherwise let `n` be the top degree. Each local object is `n`-pseudo-coherent, so
   `lem-sc-finite-cohomology` makes its top cohomology finite. Apply
   `lem-weil-pbc-module-finite-of-localization-span` to obtain global finiteness. Lift a finite
   free surjection onto top cohomology to cycles, obtaining a map `E[-n]` to the complex.
3. Its cone has vanishing cohomology in degrees at least `n`. Localization commutes with this
   cone triangle. The localized `E[-n]` is finite free and bounded. Clause one of
   `lem-pc-ring-pseudo-coherent-distinguished-triangle` (Tag 064R) makes the localized cones
   `m`-pseudo-coherent. Induction gives global `m`-pseudo-coherence of the cone, and clause two
   of the same triangle lemma gives `m`-pseudo-coherence of the original complex.
4. If every localization is pseudo-coherent, apply
   `lem-pc-ring-pseudo-coherent-iff-all-m` (Tag 064U) locally to get every fixed-degree condition,
   use the first assertion for each integer, then apply the same equivalence globally. -/
theorem ringPseudoCoherent_localization_glue
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (m : ℤ) (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁} (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤) :
    ((∀ i : Fin r, IsMPseudoCoherent m
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M))) →
      IsMPseudoCoherent m (Q.obj M)) ∧
    ((∀ i : Fin r, IsPseudoCoherent
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M))) →
      IsPseudoCoherent (Q.obj M)) := by
  classical
  have glue (m : ℤ) (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
      (hlocal : ∀ i : Fin r, IsMPseudoCoherent m
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M))) : IsMPseudoCoherent m (Q.obj M) := by
    have bounded : ∃ n : ℤ, ∀ j : ℤ, n < j →
        Limits.IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj M)) := by
      have hb (i : Fin r) := isMPseudoCoherent_boundedAbove m _ (hlocal i)
      choose bound hbound using hb
      obtain ⟨n, hn⟩ := (Set.finite_range bound).bddAbove
      refine ⟨n, fun j hj ↦ homology_vanishes_of_localization_span M r f hf j ?_⟩
      intro i
      exact hbound i j (lt_of_le_of_lt (hn (Set.mem_range_self i)) hj)
    have descent (k : ℕ) :
        ∀ (K : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ),
        (∀ i : Fin r, IsMPseudoCoherent m
          (Q.obj ((Functor.mapHomologicalComplex
            (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
            (ComplexShape.up ℤ)).obj K))) →
        (∀ j : ℤ, m + (k : ℤ) ≤ j →
          Limits.IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj K))) →
        IsMPseudoCoherent m (Q.obj K) := by
      induction k with
      | zero =>
        intro K hK hvan
        exact isMPseudoCoherent_of_homology_vanishes m (Q.obj K)
          (fun j hj ↦ hvan j (by simpa using hj))
      | succ k ih =>
        intro K hK hvan
        obtain ⟨E, N, a, b, c, hT, hE, hNvan, hNlocal⟩ :=
          isMPseudoCoherent_localization_cone_step K r f hf m (m + (k : ℤ))
            (by omega) (fun j hj ↦ hvan j (by omega)) hK
        have hN := ih N hNlocal (fun j hj ↦ hNvan j (by omega))
        exact (isMPseudoCoherent_of_distinguished_triangle A m
          (Pretriangulated.Triangle.mk a b c) hT).2.1 hE hN
    obtain ⟨n, hn⟩ := bounded
    exact descent (n - m + 1).toNat M hlocal (fun j hj ↦ hn j (by omega))
  refine ⟨glue m M, ?_⟩
  intro hlocal
  apply (isPseudoCoherent_iff_forall_isMPseudoCoherent A M).2
  intro k
  apply glue k M
  intro i
  exact (isPseudoCoherent_iff_forall_isMPseudoCoherent (Localization.Away (f i))
    ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
      (ComplexShape.up ℤ)).obj M)).1 (hlocal i) k

end DerivedCategory
