/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.CompletionMapForLocalHom
import WeilConjectures.RingTheory.FormallySmoothAdicCompletionTransfer

/-!
# Adic formal smoothness after completing source and target

Source: Stacks Project, More on Algebra, Lemma 15.38.4 (Tag 07ED), (1) implies (3)
(blueprint: lem-weil-pbc-fs-adic-complete-source-target).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A local map of Noetherian local rings induces a map between their maximal-ideal
completions, specified on every quotient coordinate. Formal smoothness for the target's
maximal-ideal adic topology passes to this map, with the extended target ideal.
Source: Stacks Project, Tag 07ED, (1) implies (3).
(blueprint: lem-weil-pbc-fs-adic-complete-source-target)

Proof: (1) Noetherianity makes both maximal ideals finitely generated. Locality sends
powers of the source maximal ideal into the corresponding target powers, so the induced
quotient maps form a compatible family and define the displayed completion homomorphism.
(2) By lem-weil-pbc-fs-adic-completion, completion of the target preserves adic formal
smoothness over the original source (07ED, (1) implies (2)).
(3) In a lifting problem over the completed source with square-zero ideal J, if the map
from the completed target to D/J kills the k-th power of the extended target ideal, the
structure map from the completed source to D kills its extended maximal ideal to power
2k: its k-th power maps into J and J squared is zero (07EC).
(4) Restrict the lifting problem to the original source and use step (2). The resulting
lift likewise kills the 2k-th power of the extended target ideal.
(5) By lem-weil-pbc-adic-completion-mod-power (05GG), every element of the completed
source agrees modulo its extended maximal ideal to power 2k with an original-source
element. The two maps to D agree on the original source and kill that power, hence agree
everywhere. The lift is therefore linear over the completed source, as required. -/
theorem exists_formallySmoothAdic_completeSourceTarget
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ] :
    ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
        AdicCompletion (IsLocalRing.maximalIdeal B) B,
      (∀ (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) (a : A),
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a →
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal B) n (ψ x) =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B) ^ n) (φ a)) ∧
      (letI := φ.toAlgebra
       FormallySmoothAdic A B (IsLocalRing.maximalIdeal B) →
         letI := ψ.toAlgebra
         FormallySmoothAdic (AdicCompletion (IsLocalRing.maximalIdeal A) A)
           (AdicCompletion (IsLocalRing.maximalIdeal B) B)
           ((IsLocalRing.maximalIdeal B).map
             (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)))) := by
  obtain ⟨ψ, hψ⟩ := RingHom.exists_adicCompletion_map_of_local φ
  refine ⟨ψ, hψ, ?_⟩
  exact formallySmoothAdic_completion_transfer A B φ ψ hψ

end Algebra
