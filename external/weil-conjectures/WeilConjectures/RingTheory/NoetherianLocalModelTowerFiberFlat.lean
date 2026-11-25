/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberFlatStage
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberFlatPersistence

/-!
# Closed-fibre flatness eventually holds in a Noetherian local model tower

Source: Stacks Project, Algebra, proof of Tag 00R7, second paragraph, the quotient
systems and the second application of Tag 00R6.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-flat).
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Module

set_option linter.style.haveILetI false in
/-- Flatness of the limit closed fibre descends to a tail of the model tower.
Source: Stacks Project, Algebra, proof of Tag 00R7, second paragraph, the quotient
systems and the second application of Tag 00R6.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-flat).

Proof:
1. Write `mᵢ` for the maximal ideal of `Rᵢ`. A local map of local rings pulls the
   target maximal ideal back to the source maximal ideal. Thus the base transition
   maps send `mᵢ` into `mⱼ`, and membership of a represented limit element in `m_R`
   already holds at its representing stage.
2. Form `Aᵢ = Sᵢ/mᵢSᵢ`, `Bᵢ = Tᵢ/mᵢTᵢ` and `Dᵢ = Nᵢ/mᵢNᵢ`. These are
   Noetherian local rings and finite top-ring modules: the extended ideals are contained
   in the respective maximal ideals, and quotients preserve Noetherianity and finiteness.
   The compatible stage maps descend to local maps and semilinear module maps.
3. Tensor-over-quotient and localization base change identify the new transition
   tensor maps with quotients of `fibreTransition` and `moduleTransition`. Thus the
   former are localizations and the latter are module base-change isomorphisms.
4. The quotient-system limits are `S/m_RS`, `S'/m_RS'` and `M/m_RM`. Surjectivity
   follows by representing elements at a stage. For injectivity, represent a finite
   expression in an extended maximal ideal at a common later stage. Its coefficients
   lie in that stage's maximal ideal by step 1. Descend equality with the given element
   using the eventual-equality clauses of the tower. The element is then zero in that
   quotient stage. The same argument works for modules and preserves scalar actions.
5. The quotient-tensor isomorphism identifies `M/m_RM` with the given closed-fibre
   tensor module. Apply `RingTheory.exists_flat_stage` to the quotient system and the
   limit fibre-flatness hypothesis. This gives a fibre-flat stage. At every later stage,
   base change preserves flatness; tensor associativity and the quotient transition
   localization identify the later module with a localization of that base change.
   `Module.Flat.localizedModule_of_algebra` preserves base flatness, completing the tail
   assertion. No base-flatness hypothesis is needed, and the zero module is allowed.
-/
theorem NoetherianLocalModelTower.eventually_fiberFlat
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M)
    (h_fibre : Module.Flat
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M)) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    ∃ i : X.ι, ∀ j : X.ι, i ≤ j → Module.Flat
      (X.S₀ j ⧸ Ideal.map (algebraMap (X.R₀ j) (X.S₀ j))
        (IsLocalRing.maximalIdeal (X.R₀ j)))
      ((X.S₀ j ⧸ Ideal.map (algebraMap (X.R₀ j) (X.S₀ j))
        (IsLocalRing.maximalIdeal (X.R₀ j))) ⊗[X.S₀ j] X.N₀ j) := by
  letI := X.preorder
  letI := X.commR
  letI := X.commS
  letI := X.localR
  letI := X.algRS
  letI := X.addN
  letI := X.moduleS
  obtain ⟨i, hi⟩ := X.exists_fiberFlat_stage h_fibre
  refine ⟨i, fun j hij ↦ X.fiberFlat_of_le i j hij hi⟩

end Module
