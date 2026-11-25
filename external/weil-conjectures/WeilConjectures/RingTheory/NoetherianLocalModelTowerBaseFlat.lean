/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.NoetherianLocalModelTowerBaseFlatStage

/-!
# Base flatness eventually holds in a Noetherian local model tower

Source: Stacks Project, Algebra, proof of Tag 00R7, second paragraph, application
of Tag 00R6 to the base and top rings.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-base-flat).
-/

@[expose] public section

universe u v w t

open scoped TensorProduct
open TensorProduct

namespace Module

private theorem flat_tensor_over_algebra
    {A C B P : Type*} [CommRing A] [CommRing C] [CommRing B]
    [Algebra A C] [Algebra C B] [Algebra A B] [IsScalarTower A C B]
    [AddCommGroup P] [Module A P] [Module C P] [IsScalarTower A C P]
    [Module.Flat A P] [Module.Flat C B] : Module.Flat A (B ⊗[C] P) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro Q _ _ N
  let eN := AlgebraTensorModule.assoc A C C B P N
  let eQ := AlgebraTensorModule.assoc A C C B P Q
  let f := AlgebraTensorModule.lTensor C P N.subtype
  have hf : Function.Injective f := by
    simpa only [f, AlgebraTensorModule.coe_lTensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := P) N.subtype
        N.subtype_injective)
  have hB := Module.Flat.lTensor_preserves_injective_linearMap (M := B) f hf
  have hcomm : ∀ z, (LinearMap.lTensor B f) (eN z) =
      eQ (LinearMap.lTensor (B ⊗[C] P) N.subtype z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b n =>
      induction b using TensorProduct.inductionOn with
      | tmul b p => rfl
      | add b b' hb hb' => simp only [add_tmul, map_add, hb, hb']
    | add z z' hz hz' => simp only [map_add, hz, hz']
  intro z z' h
  apply eN.injective
  apply hB
  rw [hcomm, hcomm, h]


private theorem flat_of_localized_baseChange
    {A B A' B' N N' : Type*}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [AddCommGroup N'] [Module A' N'] [Module B' N'] [IsScalarTower A' B' N']
    [Module.Flat A N]
    (hloc : ∃ (q : B ⊗[A] A' →+* B') (U : Submonoid (B ⊗[A] A')),
      (∀ (b : B) (a : A'), q (b ⊗ₜ[A] a) =
        algebraMap B B' b * algebraMap A' B' a) ∧
      (letI := q.toAlgebra; IsLocalization U B'))
    (e : (B' ⊗[B] N) ≃ₗ[B'] N') : Module.Flat A' N' := by
  obtain ⟨q, U, hq, hloc⟩ := hloc
  let C := B ⊗[A] A'
  let : Algebra A' C := Algebra.TensorProduct.rightAlgebra
  let : Algebra C B' := q.toAlgebra
  have : IsScalarTower B C B' := IsScalarTower.of_algebraMap_eq fun b ↦ by
    change algebraMap B B' b = q (b ⊗ₜ[A] (1 : A'))
    rw [hq, map_one, mul_one]
  have : IsScalarTower A' C B' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A' B' a = q ((1 : B) ⊗ₜ[A] a)
    rw [hq, map_one, one_mul]
  have : IsScalarTower A C B' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B B',
      IsScalarTower.algebraMap_apply A B C, IsScalarTower.algebraMap_apply B C B']
  have : IsLocalization U B' := hloc
  have : Module.Flat C B' := IsLocalization.flat B' U
  let P := C ⊗[B] N
  have : Module.Flat A' P := Module.Flat.of_linearEquiv
    (Algebra.IsPushout.cancelBaseChange A A' B C N)
  have : Module.Flat A' (B' ⊗[C] P) := flat_tensor_over_algebra
  let ec := (AlgebraTensorModule.cancelBaseChange B C B' B' N).restrictScalars A'
  exact Module.Flat.of_linearEquiv (ec.trans (e.restrictScalars A')).symm

/-- Base flatness of the limit module descends to a tail of the model tower.
Source: Stacks Project, Algebra, proof of Tag 00R7, second paragraph, application
of Tag 00R6 to the base and top rings.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-base-flat).

Proof:
1. Apply `exists_baseFlat_stage` to the tower. Its proof constructs categorical colimits,
   transports the assumed limit flatness, and applies `RingTheory.exists_flat_stage`.
   It gives an index whose stage module is flat over the stage base ring.
2. For any later index, form C = T_i tensor_{R_i} R_j. Base change makes
   C tensor_{T_i} N_i flat over R_j, using `Algebra.IsPushout.cancelBaseChange`.
   The canonical map C to T_j is a localization by `baseTransition`, so T_j is
   flat over C. Tensor associativity and the injectivity criterion for flatness show
   that extending a module flat over R_j along this flat C-algebra remains flat over R_j.
3. Cancel the iterated tensor product and compose with `moduleTransition` to identify
   the extension with N_j. The commuting ring squares and scalar towers identify the
   resulting R_j-action with its specified action. Linear equivalences transport
   flatness, proving the tail assertion, including its first index and the zero module.
-/
theorem NoetherianLocalModelTower.eventually_baseFlat
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [Module S' M] [Module S M] [Module R M]
    [IsScalarTower S S' M] [IsScalarTower R S M]
    (X : NoetherianLocalModelTower R S S' M) [Module.Flat R M] :
    letI := X.preorder
    letI := X.commR
    letI := X.addN
    letI := X.moduleR
    ∃ i : X.ι, ∀ j : X.ι, i ≤ j → Module.Flat (X.R₀ j) (X.N₀ j) := by
  let := X.preorder
  let := X.commR
  let := X.commS
  let := X.commT
  let := X.algRS
  let := X.algST
  let := X.algRT
  let := X.towerRST
  let := X.addN
  let := X.moduleR
  let := X.moduleS
  let := X.moduleT
  let := X.towerSTN
  let := X.towerRSN
  obtain ⟨i, hi⟩ := X.exists_baseFlat_stage
  refine ⟨i, fun j hij ↦ ?_⟩
  have : Module.Flat (X.R₀ i) (X.N₀ i) := hi
  let : Algebra (X.R₀ i) (X.R₀ j) := (X.rmap i j hij).toAlgebra
  let : Algebra (X.T₀ i) (X.T₀ j) := (X.tmap i j hij).toAlgebra
  let : Algebra (X.R₀ i) (X.T₀ j) :=
    ((algebraMap (X.R₀ j) (X.T₀ j)).comp (X.rmap i j hij)).toAlgebra
  have : IsScalarTower (X.R₀ i) (X.R₀ j) (X.T₀ j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (X.R₀ i) (X.T₀ i) (X.N₀ i) :=
    IsScalarTower.to₁₃₄ (X.R₀ i) (X.S₀ i) (X.T₀ i) (X.N₀ i)
  have : IsScalarTower (X.R₀ j) (X.T₀ j) (X.N₀ j) :=
    IsScalarTower.to₁₃₄ (X.R₀ j) (X.S₀ j) (X.T₀ j) (X.N₀ j)
  have hcomm : (X.tmap i j hij).comp (algebraMap (X.R₀ i) (X.T₀ i)) =
      (algebraMap (X.R₀ j) (X.T₀ j)).comp (X.rmap i j hij) := by
    rw [IsScalarTower.algebraMap_eq (X.R₀ i) (X.S₀ i) (X.T₀ i),
      ← RingHom.comp_assoc, X.st_comm, RingHom.comp_assoc, X.rs_comm,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq (X.R₀ j) (X.S₀ j) (X.T₀ j)]
  have : IsScalarTower (X.R₀ i) (X.T₀ i) (X.T₀ j) :=
    IsScalarTower.of_algebraMap_eq' hcomm.symm
  obtain ⟨e, _⟩ := X.moduleTransition i j hij
  exact flat_of_localized_baseChange (X.baseTransition i j hij) e

end Module
