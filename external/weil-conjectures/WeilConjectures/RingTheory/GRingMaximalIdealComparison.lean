/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompleteLocalGRing
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.RingTheory.RegularThroughLocalization
import WeilConjectures.RingTheory.FibreRingNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# A comparison local ring for the maximal-ideal G-ring criterion

Source: Stacks Project, More on Algebra, proof of Lemma 07PT, up to the
regularity of the map from the prime localization into the comparison completion.
(blueprint: lem-weil-pbc-g-ring-maximal-ideal-comparison).
-/

@[expose] public section

universe w

/-- Maximal-local regularity supplies a flat local comparison map whose composite
with the comparison ring's completion map is regular.

Source: Stacks Project, More on Algebra, proof of Lemma 07PT, the diagram and
argument preceding the final application of Lemma 07NT.
(blueprint: lem-weil-pbc-g-ring-maximal-ideal-comparison).

Proof: Choose a maximal ideal m containing p, and put A = R_m. Extend p to
its prime ideal pA in A; it contracts to p because p misses the denominators.
The completion Ahat is Noetherian, local, and complete at its maximal ideal.
Faithful flatness of A → Ahat gives a prime q lying over pA, hence contracting
along R → Ahat to p. Put B = Ahat_q, and let φ : R_p → B be the localRingHom
induced by R → Ahat and this contraction identity.

The localization R → A is regular. By hypothesis A → Ahat is regular, so
R → Ahat is regular by Tag 07QI. In particular it is flat, and localRingHom
is flat and local. Since Ahat is complete Noetherian local, Tag 07PS makes
it a G-ring, giving regularity of B → Bhat. The localization Ahat → B is
regular. Compose R → Ahat → B → Bhat using Tag 07QI twice more. All needed
fibres are Noetherian by the Noetherian fibre theorem, since Ahat, B, and
Bhat are Noetherian. Finally the induced map φ commutes with R → R_p and
R → B. Thus R → Bhat factors as R → R_p → Bhat, and regularity through
localization proves regularity of the latter map. Together with flatness
and locality of φ this proves the assertion. -/
theorem exists_flat_local_regular_completion_comparison
    (R : Type w) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      RingHom.IsRegular
        (algebraMap (Localization.AtPrime m)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime m))
            (Localization.AtPrime m))))
    (p : Ideal R) [p.IsPrime] :
    ∃ (B : Type w) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B),
      ∃ φ : Localization.AtPrime p →+* B,
        φ.Flat ∧
        (∀ x : Localization.AtPrime p,
          x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) →
            φ x ∈ IsLocalRing.maximalIdeal B) ∧
        ((algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp φ).IsRegular := by
  classical
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p (Ideal.IsPrime.ne_top ‹_›)
  let : m.IsMaximal := hm
  let A := Localization.AtPrime m
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have : IsNoetherianRing A := inferInstance
  have : IsNoetherianRing Ahat := AdicCompletion.isNoetherianRing _
  have : Module.FaithfullyFlat A Ahat := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hd : Disjoint (m.primeCompl : Set R) (p : Set R) :=
    Set.disjoint_left.mpr (fun x hx hp ↦ hx (hpm hp))
  let pA : Ideal A := p.map (algebraMap R A)
  have : pA.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl A p
    inferInstance hd
  have hpA : pA.comap (algebraMap R A) = p :=
    IsLocalization.under_map_of_isPrime_disjoint m.primeCompl A inferInstance hd
  obtain ⟨q, hq, hqA⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := Ahat) pA
  let : q.IsPrime := hq
  have hqR : p = q.comap (algebraMap R Ahat) := by
    have hqA' : q.comap (algebraMap A Ahat) = pA := hqA.over.symm
    rw [IsScalarTower.algebraMap_eq R A Ahat, ← Ideal.comap_comap, hqA', hpA]
  let B := Localization.AtPrime q
  let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
  have : IsNoetherianRing B := inferInstance
  have : IsNoetherianRing Bhat := AdicCompletion.isNoetherianRing _
  let φ := Localization.localRingHom p q (algebraMap R Ahat) hqR
  have hc : (algebraMap A Ahat).IsRegular := h m
  have hRA : (algebraMap R A).IsRegular :=
    (IsLocalization.isRegular_and_fiber m.primeCompl).1
  have hRAhat : (algebraMap R Ahat).IsRegular :=
    hRA.comp_of_fiber_noetherian hc (fun p ↦ Ideal.isNoetherianRing_fiber p)
  have hAB : (algebraMap Ahat B).IsRegular :=
    (IsLocalization.isRegular_and_fiber q.primeCompl).1
  have hRB : (algebraMap R B).IsRegular :=
    hRAhat.comp_of_fiber_noetherian hAB (fun p ↦ Ideal.isNoetherianRing_fiber p)
  have hcB : (algebraMap B Bhat).IsRegular :=
    (isGRing_of_isNoetherianRing_of_isAdicComplete Ahat).2 q
  have hRBhat : (algebraMap R Bhat).IsRegular :=
    hRB.comp_of_fiber_noetherian hcB (fun p ↦ Ideal.isNoetherianRing_fiber p)
  have hflat : φ.Flat := hRAhat.1.localRingHom q p hqR
  have hlocal : ∀ x : Localization.AtPrime p,
      x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) →
        φ x ∈ IsLocalRing.maximalIdeal B := by
    intro x hx
    exact map_nonunit φ x hx
  let : Algebra (Localization.AtPrime p) Bhat :=
    ((algebraMap B Bhat).comp φ).toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) Bhat :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      change algebraMap R Bhat x = algebraMap B Bhat (φ (algebraMap R _ x))
      rw [Localization.localRingHom_to_map]
      exact IsScalarTower.algebraMap_apply R Ahat Bhat x)
  refine ⟨B, inferInstance, inferInstance, inferInstance, φ, hflat, hlocal, ?_⟩
  exact RingHom.isRegular_of_comp_algebraMap_localization p.primeCompl hRBhat
