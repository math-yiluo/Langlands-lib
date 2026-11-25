/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.CmModuleGoodElementNonzerodivisor
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.RingTheory.DepthOverQuotientRing
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.LinearAlgebra.Dimension.Free
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# Maximal Cohen–Macaulay modules over regular local rings

Source: Stacks Project, Algebra, Lemma 10.106.6 (Tag 00NT) and Definition 10.103.8
(Tag 00NF) (blueprint: lem-weil-pbc-regular-local-mcm-free).
-/

@[expose] public section

universe u v

namespace IsRegularLocalRing

/-- A finite module of depth `d` over a regular local ring of dimension `d` is free,
with a finite basis (Stacks, Tags 00NT and 00NF)
(blueprint: lem-weil-pbc-regular-local-mcm-free).

Proof, following the node's split of Stacks 00NT:
1. Induct on `d`, quantifying over all regular local rings of that dimension.
   The depth definition (def-weil-pbc-depth) gives depth infinity for the zero module,
   so the depth hypothesis makes `M` nonzero.
2. For `d = 0`, the maximal ideal is zero and `R` is a field. Thus `M` is free by
   lem-weil-pbc-vector-space-free. Finite generation makes its basis finite: the union
   of the supports of finitely many generators spans, so independence excludes other vectors.
3. For `d > 0`, choose the first element `x` of a regular system of parameters.
   By lem-weil-pbc-regular-local-generators-regular-sequence, `R/xR` is regular local
   of dimension `d - 1`.
4. By lem-weil-pbc-depth-le-support-dimension, the support of `M` has dimension `d`.
   The support intersected with `V(x)` has dimension at most `d - 1` by step 3 and
   at least `d - 1` by lem-weil-pbc-support-dimension-quotient-element-bound and
   the inclusion of the support of `M/xM` in that intersection. Hence equality holds.
5. Apply lem-weil-pbc-cm-module-good-element-nonzerodivisor: `x` is a nonzerodivisor
   on `M` and the depth over `R` of `M/xM` is `d - 1`.
6. The quotient is finite over `R/xR`. Its depths over `R` and `R/xR` agree by
   lem-weil-pbc-depth-over-quotient-ring: scalar multiplication on
   all successive quotients is the same, and sequences in the quotient maximal ideal lift.
7. Induction makes `M/xM` free over `R/xR`. Then lem-weil-pbc-free-mod-nonzerodivisor
   makes `M` free over `R`; its basis is finite by the argument of step 2, giving
   the displayed isomorphism with a finite direct sum of copies of `R`. -/
theorem free_of_depth_eq_ringKrullDim
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (hdepth : IsLocalRing.depth (R := R) M = (d : ℕ∞)) :
    Module.Free R M ∧ ∃ r : ℕ, Nonempty (M ≃ₗ[R] (Fin r →₀ R)) := by
  classical
  have hfree : Module.Free R M := by
    induction d generalizing R M with
    | zero =>
      have hrank : (IsLocalRing.maximalIdeal R).spanFinrank = 0 := by
        have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
        rw [hdim] at h
        exact_mod_cast h
      have hm : IsLocalRing.maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot
          (IsNoetherian.noetherian _)).mp hrank
      let : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm).toField
      infer_instance
    | succ n ih =>
      have : Nontrivial M := by
        by_contra h
        have : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
        have ht : IsLocalRing.depth (R := R) M = ⊤ := by
          have hm : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤ :=
            Subsingleton.elim _ _
          simp only [IsLocalRing.depth, Ideal.depth, hm, ite_eq_left]
        rw [hdepth] at ht
        exact ENat.natCast_ne_top _ ht
      have hCM : (IsLocalRing.depth (R := R) M : WithBot ℕ∞) =
          Module.supportDim R M := by
        apply le_antisymm
        · exact IsLocalRing.depth_le_supportDim M
        · rw [hdepth]
          exact (Module.supportDim_le_ringKrullDim R M).trans_eq hdim
      obtain ⟨s, hcard, hspan⟩ :=
        Submodule.FG.exists_span_finset_card_eq_spanFinrank
          (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R))
      have hlen : s.toList.length = n + 1 := by
        have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
        rw [hdim, ← hcard] at h
        exact_mod_cast (show (s.toList.length : WithBot ℕ∞) =
          ((n + 1 : ℕ) : WithBot ℕ∞) by simpa using h)
      have hrs : IsLocalRing.IsRegularSystemOfParameters s.toList :=
        ⟨by simpa using hspan, by simpa [hlen] using hdim.symm⟩
      cases he : s.toList with
      | nil => simp [he] at hlen
      | cons x xs =>
        have hx : x ∈ IsLocalRing.maximalIdeal R := by
          rw [← hrs.1]
          exact Ideal.subset_span (by simp [he])
        obtain ⟨_, hquot, _⟩ := isRegular_and_quotients_of_generators
          R (n + 1) hdim s.toList hrs
        have hq := hquot 1 (by omega)
        have htake : Ideal.ofList (s.toList.take 1) = Ideal.span {x} := by
          simp [he]
        rw [htake] at hq
        simp only [Nat.add_sub_cancel] at hq
        have : IsRegularLocalRing (R ⧸ Ideal.span {x}) := hq.1
        have hupper : Module.supportDim R (QuotSMulTop x M) ≤
            (n : WithBot ℕ∞) := by
          rw [Module.supportDim, Module.support_quotSMulTop]
          calc
            Order.krullDim (Module.support R M ∩
                PrimeSpectrum.zeroLocus ({x} : Set R) : Set (PrimeSpectrum R)) ≤
                Order.krullDim (PrimeSpectrum.zeroLocus ({x} : Set R) :
                  Set (PrimeSpectrum R)) :=
              Order.krullDim_le_of_strictMono
                (fun p => ⟨p.1, p.2.2⟩) (fun _ _ h => h)
            _ = ringKrullDim (R ⧸ Ideal.span {x}) := by
              rw [ringKrullDim_quotient, PrimeSpectrum.zeroLocus_span]
            _ = (n : WithBot ℕ∞) := hq.2
        have hdrop : Module.supportDim R (QuotSMulTop x M) + 1 =
            Module.supportDim R M := by
          apply le_antisymm
          · rw [← hCM, hdepth]
            simpa only [Nat.cast_add, Nat.cast_one, WithBot.coe_add,
              WithBot.coe_natCast, WithBot.coe_one, add_comm] using
              add_le_add_right hupper (1 : WithBot ℕ∞)
          · exact Module.supportDim_le_supportDim_quotSMulTop_succ hx
        have hcut : Order.krullDim (Module.support R M ∩
            PrimeSpectrum.zeroLocus ({x} : Set R) : Set (PrimeSpectrum R)) + 1 =
            Module.supportDim R M := by
          change Order.krullDim (Module.support R (QuotSMulTop x M) :
            Set (PrimeSpectrum R)) + 1 = Module.supportDim R M at hdrop
          rwa [Module.support_quotSMulTop] at hdrop
        obtain ⟨hreg, _, hdep⟩ :=
          Module.cm_module_good_element_nonzerodivisor M hCM x hx hcut
        have hdepR : IsLocalRing.depth (R := R) (QuotSMulTop x M) = (n : ℕ∞) := by
          apply ENat.add_left_injective_of_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
          simpa only [hdepth, Nat.cast_add, Nat.cast_one] using hdep
        have hI : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R :=
          Ideal.span_le.mpr (by simpa using hx)
        have htors : Module.IsTorsionBySet R (QuotSMulTop x M)
            (Ideal.span {x} : Set R) :=
          (Module.isTorsionBySet_span_singleton_iff x).mpr
            (Module.isTorsionBy_quotient_element_smul M x)
        have : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
          Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) _
        have hdepQ : IsLocalRing.depth (R := R ⧸ Ideal.span {x})
            (QuotSMulTop x M) = (n : ℕ∞) :=
          (IsLocalRing.depth_over_quotient_ring R (Ideal.span {x}) hI
            (QuotSMulTop x M) htors).1.trans hdepR
        have : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
          ih (R ⧸ Ideal.span {x}) (QuotSMulTop x M) hq.2 hdepQ
        have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
        exact (Module.free_quotSMulTop_iff_free R M
          (by rwa [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]) hreg).mp
            inferInstance
  have : Module.Free R M := hfree
  exact ⟨hfree, Module.finrank R M, ⟨(Module.finBasis R M).repr⟩⟩

end IsRegularLocalRing
