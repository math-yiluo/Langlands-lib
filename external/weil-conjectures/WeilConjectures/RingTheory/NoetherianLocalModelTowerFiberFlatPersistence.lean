/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.LocalizedBaseChangeQuotientFlat

/-!
# Persistence of closed-fibre flatness in a local model tower

Source: Stacks Project, Algebra, proof of Tag 00R7, second paragraph.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-flat-persistence).
-/

@[expose] public section

universe u v w t
open scoped TensorProduct
namespace Module

/-- Fibre flatness persists after a transition in a Noetherian local model tower.
Source: Stacks Project, Algebra, proof of Tag 00R7, second paragraph.
Base change, tensor associativity, and localization identify the later fibre module with
a localization of the base change of the earlier one, and localization preserves flatness.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-flat-persistence) -/
theorem NoetherianLocalModelTower.fiberFlat_of_le
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    ∀ (i j : X.ι), i ≤ j →
      Module.Flat
        (X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
          (IsLocalRing.maximalIdeal (X.R₀ i)))
        ((X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
          (IsLocalRing.maximalIdeal (X.R₀ i))) ⊗[X.S₀ i] X.N₀ i) →
      Module.Flat
        (X.S₀ j ⧸ Ideal.map (algebraMap (X.R₀ j) (X.S₀ j))
          (IsLocalRing.maximalIdeal (X.R₀ j)))
        ((X.S₀ j ⧸ Ideal.map (algebraMap (X.R₀ j) (X.S₀ j))
          (IsLocalRing.maximalIdeal (X.R₀ j))) ⊗[X.S₀ j] X.N₀ j) := by
  let := X.preorder
  let := X.commR
  let := X.commS
  let := X.commT
  let := X.localR
  let := X.algRS
  let := X.algST
  let := X.addN
  let := X.moduleS
  let := X.moduleT
  let := X.towerSTN
  intro i j hij hi
  let : Algebra (X.S₀ i) (X.S₀ j) := (X.smap i j hij).toAlgebra
  let : Algebra (X.T₀ i) (X.T₀ j) := (X.tmap i j hij).toAlgebra
  let : Algebra (X.S₀ i) (X.T₀ j) :=
    ((algebraMap (X.S₀ j) (X.T₀ j)).comp (X.smap i j hij)).toAlgebra
  have : IsScalarTower (X.S₀ i) (X.S₀ j) (X.T₀ j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (X.S₀ i) (X.T₀ i) (X.T₀ j) :=
    IsScalarTower.of_algebraMap_eq' (X.st_comm i j hij).symm
  let I : Ideal (X.S₀ i) :=
    Ideal.map (algebraMap (X.R₀ i) (X.S₀ i)) (IsLocalRing.maximalIdeal (X.R₀ i))
  let K : Ideal (X.S₀ j) := I.map (algebraMap (X.S₀ i) (X.S₀ j))
  let J : Ideal (X.S₀ j) :=
    Ideal.map (algebraMap (X.R₀ j) (X.S₀ j)) (IsLocalRing.maximalIdeal (X.R₀ j))
  -- Local transitions send the earlier maximal ideal into the later one.
  have hKJ : K ≤ J := by
    change ((IsLocalRing.maximalIdeal (X.R₀ i)).map
      (algebraMap (X.R₀ i) (X.S₀ i))).map (X.smap i j hij) ≤ J
    rw [Ideal.map_map, X.rs_comm i j hij, ← Ideal.map_map]
    have : IsLocalHom (X.rmap i j hij) := X.rmap_local i j hij
    exact Ideal.map_mono (f := algebraMap (X.R₀ j) (X.S₀ j))
      (IsLocalRing.map_maximalIdeal_le (X.rmap i j hij))
  -- First quotient by the extended earlier ideal, then by the later ideal.
  have hflat := flat_quotient_localized_baseChange
    (R := X.S₀ i) (S := X.T₀ i) (R' := X.S₀ j) (S' := X.T₀ j) I (X.N₀ i)
    (X.fibreTransition i j hij) hi
  let Q := X.S₀ j ⧸ K
  let Q' := X.S₀ j ⧸ J
  let : Algebra Q Q' := Ideal.Quotient.algebraQuotientOfLEComap
    (R := X.S₀ j) (A := X.S₀ j) (p := K) (P := J)
    (by simpa only [Algebra.algebraMap_self, Ideal.comap_id] using hKJ)
  have : IsScalarTower (X.S₀ j) Q Q' := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Flat Q (Q ⊗[X.S₀ j] (X.T₀ j ⊗[X.T₀ i] X.N₀ i)) := hflat
  have : Module.Flat Q'
      (Q' ⊗[Q] (Q ⊗[X.S₀ j] (X.T₀ j ⊗[X.T₀ i] X.N₀ i))) := inferInstance
  have hfinal : Module.Flat Q' (Q' ⊗[X.S₀ j] (X.T₀ j ⊗[X.T₀ i] X.N₀ i)) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (X.S₀ j) Q Q' Q'
        (X.T₀ j ⊗[X.T₀ i] X.N₀ i)).symm
  -- The specified module transition identifies the resulting tensor module.
  obtain ⟨e, _⟩ := X.moduleTransition i j hij
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Q' Q')
      (e.restrictScalars (X.S₀ j))).symm

end Module
