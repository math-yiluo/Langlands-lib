/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Module localization from a lifted tensor comparison

Source: Stacks Project, Algebra, proof of Tag 00R7, first two paragraphs;
localization and tensor products (Tag 00DK).
(blueprint: lem-weil-pbc-localized-module-lifted-tensor-comparison).
-/

@[expose] public section

universe u v w t z

open scoped TensorProduct

namespace Module

/-- A localization comparison for rings and a module base-change isomorphism give
localization of the base-changed module, even when the limit rings were lifted.
Source: Stacks Project, Algebra, proof of Tag 00R7, first two paragraphs, and Tag 00DK.
(blueprint: lem-weil-pbc-localized-module-lifted-tensor-comparison).

Proof: put E = S tensor over B C, with C acting through the right factor. Tensor
symmetry and the lift equivalence identify C tensor over B ULift S with E. Transport
φ and its inverted submonoid to obtain a localization E → ULift T at W. The two formulas
for φ prove the scalar towers with S and C. Pushout tensor cancellation gives the explicit
S-linear equivalence eL : E tensor over C N ≃ S tensor over B N. Transport the E-action
through eL to L = S tensor over B N; since eL is S-linear, this action is compatible with S.
The localized-module tensor theorem applied to E → ULift T, tensoring over C with N,
shows that E tensor over C N → ULift T tensor over C N is localization at W. Precompose
with the E-linear version of eL.symm. The canonical localization isomorphism now gives
W⁻¹L ≃ ULift T tensor over C N. Restrict scalars to S and compose with the supplied
module equivalence, also restricted to S. All module structures used here are explicit
transports through specified tensor equivalences, and no arbitrary witness is chosen. -/
theorem localizedModule_of_liftedTensorComparison
    (S : Type v) (T : Type w) (B C : Type u) (N : Type t) (M : Type t)
    [CommRing S] [CommRing T] [CommRing B] [CommRing C]
    [Algebra B C] [Algebra B S] [Algebra S T]
    [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]
    [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower S T M]
    (κ : C →+* ULift.{z} T)
    (φ : C ⊗[B] ULift.{z} S →+* ULift.{z} T)
    (hφC : ∀ c : C, φ (c ⊗ₜ[B] 1) = κ c)
    (hφS : ∀ s : S, φ (1 ⊗ₜ[B] ULift.up s) = ULift.up (algebraMap S T s))
    (hloc : letI := φ.toAlgebra;
      ∃ U : Submonoid (C ⊗[B] ULift.{z} S), IsLocalization U (ULift.{z} T))
    (hM : letI := κ.toAlgebra; Nonempty (ULift.{z} T ⊗[C] N ≃ₗ[ULift.{z} T] M)) :
    ∃ (_ : Module (S ⊗[B] C) (S ⊗[B] N))
      (_ : IsScalarTower S (S ⊗[B] C) (S ⊗[B] N)) (U : Submonoid (S ⊗[B] C)),
      Nonempty (LocalizedModule U (S ⊗[B] N) ≃ₗ[S] M)  := by
  classical
  let E := S ⊗[B] C
  let : Algebra C E := Algebra.TensorProduct.rightAlgebra
  let : Algebra C (ULift.{z} T) := κ.toAlgebra
  let eR : C ⊗[B] ULift.{z} S ≃+* E :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[B] C)
      (ULift.algEquiv : ULift.{z} S ≃ₐ[B] S)).trans
      (Algebra.TensorProduct.comm B C S)).toRingEquiv
  let ψ : E →+* ULift.{z} T := φ.comp eR.symm.toRingHom
  let : Algebra E (ULift.{z} T) := ψ.toAlgebra
  obtain ⟨U, hU⟩ := hloc
  let W := U.map eR
  have hloc' : IsLocalization W (ULift.{z} T) := by
    let : Algebra (C ⊗[B] ULift.{z} S) (ULift.{z} T) := φ.toAlgebra
    have : IsLocalization U (ULift.{z} T) := hU
    exact IsLocalization.isLocalization_of_base_ringEquiv U (ULift.{z} T) eR
  have hSC : IsScalarTower S E (ULift.{z} T) := by
    apply IsScalarTower.of_algebraMap_eq
    intro s
    change ULift.up (algebraMap S T s) = ψ (s ⊗ₜ[B] 1)
    exact (hφS s).symm
  have hCC : IsScalarTower C E (ULift.{z} T) := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    change κ c = ψ (1 ⊗ₜ[B] c)
    exact (hφC c).symm
  let L₀ := E ⊗[C] N
  let eL : L₀ ≃ₗ[S] S ⊗[B] N := Algebra.IsPushout.cancelBaseChange B S C E N
  let : Module E (S ⊗[B] N) := eL.symm.toAddEquiv.module E
  have : IsScalarTower S E (S ⊗[B] N) := eL.symm.isScalarTower E
  let eL' : S ⊗[B] N ≃ₗ[E] L₀ := eL.symm.toAddEquiv.linearEquiv E
  let g : L₀ →ₗ[E] ULift.{z} T ⊗[C] N :=
    TensorProduct.AlgebraTensorModule.rTensor C N (Algebra.linearMap E (ULift.{z} T))
  have : IsLocalizedModule W g := inferInstance
  let gL := g.comp eL'.toLinearMap
  have : IsLocalizedModule W gL :=
    IsLocalizedModule.of_linearEquiv_right W g eL'
  obtain ⟨eM⟩ := hM
  exact ⟨inferInstance, inferInstance, W,
    ⟨(IsLocalizedModule.iso W gL).restrictScalars S ≪≫ₗ eM.restrictScalars S⟩⟩


end Module
