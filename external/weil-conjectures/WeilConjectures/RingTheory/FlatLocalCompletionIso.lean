/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.CompletionMapBijective

/-!
# Flat local maps induce isomorphisms on adic completions

Source: literature/stacks-project/more-algebra.tex, More on Algebra, Lemma Tag 0AGX
(blueprint: lem-weil-pbc-flat-local-completion-iso)
-/

@[expose] public section

universe u v

namespace RingHom

/--
A flat local homomorphism of Noetherian local rings inducing an isomorphism on
residue fields induces an isomorphism on the corresponding adic completions.
Source: More on Algebra, Lemma Tag 0AGX (blueprint: lem-weil-pbc-flat-local-completion-iso).
Proof:
1. The completions are local with the same residue fields, by
   `lem-weil-pbc-local-completion-local-ring`.
2. Since the extended maximal ideal equals that of B, their powers agree after
   extension. Thus B's completion is also its completion as an A-module.
3. The residue field has dimension one over A's residue field, so
   `lem-weil-pbc-finite-after-completion` makes B's completion finite over A's.
4. Flatness gives vanishing of Tor with the residue field;
   `lem-weil-pbc-flat-module-completion-flat` makes the completed module flat.
5. `lem-weil-pbc-finite-flat-local-free` makes this finite flat module free.
6. By `lem-weil-pbc-adic-completion-mod-ideal` and the local structure from step 1,
   reduction modulo the maximal ideal identifies its fibre with the residue field.
   The residue-field isomorphism therefore forces the free rank to be one.
7. Write 1 = u e in a one-element basis. If u were in the maximal ideal, 1 would
   reduce to zero in the residue field. Thus u is a unit; 1 is itself a basis,
   and the induced ring homomorphism is bijective.
-/
theorem flat_local_completion_iso
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) (hflat : φ.Flat) [IsLocalHom φ]
    (hmax : Ideal.map φ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B)
    (hres : Function.Bijective (Ideal.quotientMap (IsLocalRing.maximalIdeal B) φ
      (IsLocalRing.maximalIdeal_comap φ).ge)) :
    ∃ (φhat : AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
        AdicCompletion (IsLocalRing.maximalIdeal B) B),
      (∀ (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) (a : A),
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n) a →
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal B) n (φhat x) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal B ^ n) (φ a)) ∧
      Function.Bijective φhat ∧
        φhat.comp (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
          (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp φ := by
  obtain ⟨φhat, heval, hcomp, hflat⟩ :=
    flat_adicCompletion_of_flat_local A B φ hflat (fun x hx => map_nonunit φ x hx)
  have hbij := completion_map_bijective φ hmax hres φhat hcomp hflat
  refine ⟨φhat, ?_, hbij, hcomp⟩
  intro n x a hx
  have hx' := congrArg (fun f => f x) (heval n)
  dsimp at hx'
  rw [hx] at hx'
  exact hx'

end RingHom
