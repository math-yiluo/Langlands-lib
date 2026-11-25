/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! # Reduced differentials of a tensor product

Source: Stacks Project, Tags 07M7 and 00RO; restriction of derivations to the factors.
-/

@[expose] public section

universe u
open scoped TensorProduct
namespace AlgebraicGeometry

private local instance tensorOppositeModule (S N : Type u) [CommRing S] [AddCommGroup N]
    [Module S N] : Module Sᵐᵒᵖ N :=
  Module.compHom N ((RingHom.id S).fromOpposite fun a b => mul_comm a b)

private local instance tensorCentralModule (S N : Type u) [CommRing S] [AddCommGroup N]
    [Module S N] : IsCentralScalar S N := ⟨fun _ _ => rfl⟩

private local instance tensorOppositeTower (R S N : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] : IsScalarTower R Sᵐᵒᵖ N :=
  ⟨fun r s n => smul_assoc r (MulOpposite.unop s) n⟩

private def derivationLift
    (R S Q N : Type u) [CommRing R] [CommRing S] [CommRing Q]
    [Algebra R S] [Algebra R Q] [Algebra S Q] [IsScalarTower R S Q]
    [AddCommGroup N] [Module R N] [Module S N] [Module Q N]
    [IsScalarTower R Q N] [IsScalarTower S Q N]
    (d : Derivation R S N) : S →ₐ[R] TrivSqZeroExt Q N where
  toFun s := ⟨algebraMap S Q s, d s⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, ← algebraMap_smul Q, op_smul_eq_smul]
  commutes' r := by
    ext
    · exact (IsScalarTower.algebraMap_apply R S Q r).symm
    · simp
      rfl

/-- Restricting a derivation on a tensor product to its two factors splits reduced
relative differentials, before calculating either factor.

Source: Stacks Project, Tag 07M7, first paragraph, differential calculation;
Tag 00RO, universal property of differentials.
(blueprint: lem-weil-pbc-reduced-tensor-differentials)

Proof: put D = S tensor_A B. For each Q-module N, an R-derivation on D restricts
along s -> s tensor 1 and b -> 1 tensor b to an R-derivation on S and an
A-derivation on B, with N acted on through tau. Conversely define the derivation
of a pure tensor by sigma(b) dS(s) + tau(s tensor 1) dB(b). The restrictions kill
A, so this formula is A-balanced. Expanding the product of two pure tensors
proves Leibniz; killing R follows from the R-linearity of dS and the fact that
R maps into the S factor. Pure tensors span D, so extension and restriction
are inverse. The differential and base-change universal properties turn this
natural bijection into a Q-linear equivalence. Explicitly its inverse sends
(q tensor ds, q' tensor db) to q tensor d(s tensor 1) + q' tensor d(1 tensor b).
The forward and inverse maps agree on these differential generators, proving
the two inverse identities. The hypotheses identify the B and R actions with
sigma and eta, respectively. The calculation allows zero rings and zero
modules and does not assume flatness, smoothness or finite generation.
-/
theorem reduced_tensor_differentials
    (A R S B Q : Type u)
    [CommRing A] [CommRing R] [CommRing S] [CommRing B] [CommRing Q]
    [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    [Algebra A B] [Algebra A Q]
    (σ : B →ₐ[A] Q) (η : R →ₐ[A] Q) (τ : (S ⊗[A] B) →ₐ[A] Q)
    (hσ : τ.comp Algebra.TensorProduct.includeRight = σ)
    (hη : ∀ r : R, τ (algebraMap R (S ⊗[A] B) r) = η r) :
    letI : Algebra B Q := σ.toRingHom.toAlgebra
    letI : Algebra R Q := η.toRingHom.toAlgebra
    letI : Algebra S Q := (τ.comp Algebra.TensorProduct.includeLeft).toRingHom.toAlgebra
    letI : Algebra (S ⊗[A] B) Q := τ.toRingHom.toAlgebra
    Nonempty ((Q ⊗[S ⊗[A] B] KaehlerDifferential R (S ⊗[A] B)) ≃ₗ[Q]
      ((Q ⊗[B] KaehlerDifferential A B) × (Q ⊗[S] KaehlerDifferential R S))) := by
  let D := S ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : Algebra B Q := σ.toRingHom.toAlgebra
  let : Algebra R Q := η.toRingHom.toAlgebra
  let : Algebra S Q := (τ.comp Algebra.TensorProduct.includeLeft).toRingHom.toAlgebra
  let : Algebra D Q := τ.toRingHom.toAlgebra
  have : IsScalarTower A B Q := IsScalarTower.of_algebraMap_eq fun a =>
    (σ.commutes a).symm
  have : IsScalarTower A R Q := IsScalarTower.of_algebraMap_eq fun a =>
    (η.commutes a).symm
  have : IsScalarTower A S Q := IsScalarTower.of_algebraMap_eq fun a =>
    ((τ.comp Algebra.TensorProduct.includeLeft).commutes a).symm
  have : IsScalarTower A D Q := IsScalarTower.of_algebraMap_eq fun a =>
    (τ.commutes a).symm
  have : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq fun r => by
    change η r = τ (algebraMap R S r ⊗ₜ[A] (1 : B))
    exact (hη r).symm
  have : IsScalarTower R D Q := IsScalarTower.of_algebraMap_eq fun r => (hη r).symm
  have : IsScalarTower S D Q := IsScalarTower.of_algebraMap_eq fun s => rfl
  have : IsScalarTower B D Q := IsScalarTower.of_algebraMap_eq fun b =>
    (DFunLike.congr_fun hσ b).symm
  let X := (Q ⊗[B] KaehlerDifferential A B) × (Q ⊗[S] KaehlerDifferential R S)
  have : IsScalarTower A Q X := inferInstance
  have : IsScalarTower R Q X := inferInstance
  have : IsScalarTower S Q X := inferInstance
  have : IsScalarTower B Q X := inferInstance
  have : IsScalarTower D Q X := inferInstance
  have : IsScalarTower A S X := inferInstance
  have : IsScalarTower R S X := inferInstance
  have : IsScalarTower A B X := inferInstance
  let dS : Derivation R S X :=
    (LinearMap.inr S _ _).compDer
      ((TensorProduct.mk S Q (KaehlerDifferential R S) 1).compDer
        (KaehlerDifferential.D R S))
  let dB : Derivation A B X :=
    (LinearMap.inl B _ _).compDer
      ((TensorProduct.mk B Q (KaehlerDifferential A B) 1).compDer
        (KaehlerDifferential.D A B))
  let H : D →ₐ[R] TrivSqZeroExt Q X := Algebra.TensorProduct.lift
    (derivationLift R S Q X dS) (derivationLift A B Q X dB) (fun _ _ => Commute.all _ _)
  have Hfst : (TrivSqZeroExt.fstHom R Q X).comp H = IsScalarTower.toAlgHom R D Q := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.AlgebraTensorModule.ext
    intro s b
    change algebraMap S Q s * algebraMap B Q b = τ (s ⊗ₜ[A] b)
    change τ (s ⊗ₜ[A] 1) * σ b = τ (s ⊗ₜ[A] b)
    rw [← DFunLike.congr_fun hσ b]
    change τ (s ⊗ₜ[A] 1) * τ (1 ⊗ₜ[A] b) = _
    rw [← map_mul]
    simp
  have Hfst' (t : D) : (H t).fst = τ t := DFunLike.congr_fun Hfst t
  let d : Derivation R D X :=
    { toLinearMap := ((TrivSqZeroExt.sndHom Q X).restrictScalars R).comp H.toLinearMap
      map_one_eq_zero' := by simp
      leibniz' := by
        intro a b
        change (H (a * b)).snd = a • (H b).snd + b • (H a).snd
        rw [map_mul, TrivSqZeroExt.snd_mul, Hfst', Hfst']
        simp only [op_smul_eq_smul]
        change (algebraMap D Q a) • (H b).snd +
          (algebraMap D Q b) • (H a).snd = _
        rw [algebraMap_smul Q, algebraMap_smul Q] }
  let Y := Q ⊗[D] KaehlerDifferential R D
  let dD : Derivation R D Y :=
    (TensorProduct.mk D Q (KaehlerDifferential R D) 1).compDer
      (KaehlerDifferential.D R D)
  let f : Y →ₗ[Q] X := d.liftKaehlerDifferential.liftBaseChange Q
  let gS : (Q ⊗[S] KaehlerDifferential R S) →ₗ[Q] Y :=
    (dD.compAlgebraMap S).liftKaehlerDifferential.liftBaseChange Q
  let gB : (Q ⊗[B] KaehlerDifferential A B) →ₗ[Q] Y :=
    ((dD.restrictScalars A).compAlgebraMap B).liftKaehlerDifferential.liftBaseChange Q
  let g : X →ₗ[Q] Y := gB.coprod gS
  have hdS (s : S) : d (s ⊗ₜ[A] 1) =
      (0, 1 ⊗ₜ[S] KaehlerDifferential.D R S s) := by
    change (H (s ⊗ₜ[A] 1)).snd = _
    dsimp only [H]
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    change dS s = _
    rfl
  have hdB (b : B) : d (1 ⊗ₜ[A] b) =
      (1 ⊗ₜ[B] KaehlerDifferential.D A B b, 0) := by
    change (H (1 ⊗ₜ[A] b)).snd = _
    dsimp only [H]
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    change dB b = _
    rfl
  have hf (q : Q) (t : D) : f (q ⊗ₜ[D] KaehlerDifferential.D R D t) = q • d t := by
    change q • d.liftKaehlerDifferential (KaehlerDifferential.D R D t) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
  have hgS (q : Q) (s : S) : gS (q ⊗ₜ[S] KaehlerDifferential.D R S s) =
      q ⊗ₜ[D] KaehlerDifferential.D R D (s ⊗ₜ[A] 1) := by
    change q • (dD.compAlgebraMap S).liftKaehlerDifferential
      (KaehlerDifferential.D R S s) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    change q • ((1 : Q) ⊗ₜ[D] KaehlerDifferential.D R D (s ⊗ₜ[A] 1)) = _
    simp [TensorProduct.smul_tmul']
  have hgB (q : Q) (b : B) : gB (q ⊗ₜ[B] KaehlerDifferential.D A B b) =
      q ⊗ₜ[D] KaehlerDifferential.D R D (1 ⊗ₜ[A] b) := by
    change q • ((dD.restrictScalars A).compAlgebraMap B).liftKaehlerDifferential
      (KaehlerDifferential.D A B b) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    change q • ((1 : Q) ⊗ₜ[D] KaehlerDifferential.D R D (1 ⊗ₜ[A] b)) = _
    simp [TensorProduct.smul_tmul']
  have hgL (b : B) : g (1 ⊗ₜ[B] KaehlerDifferential.D A B b, 0) =
      1 ⊗ₜ[D] KaehlerDifferential.D R D (1 ⊗ₜ[A] b) := by
    change gB (1 ⊗ₜ[B] KaehlerDifferential.D A B b) + gS 0 = _
    rw [map_zero, add_zero, hgB]
  have hgR (s : S) : g (0, 1 ⊗ₜ[S] KaehlerDifferential.D R S s) =
      1 ⊗ₜ[D] KaehlerDifferential.D R D (s ⊗ₜ[A] 1) := by
    change gB 0 + gS (1 ⊗ₜ[S] KaehlerDifferential.D R S s) = _
    rw [map_zero, zero_add, hgS]
  have hfg : f.comp g = LinearMap.id := by
    apply LinearMap.prod_ext
    · ext b : 4
      change f (g (1 ⊗ₜ[B] KaehlerDifferential.D A B b, 0)) =
        (1 ⊗ₜ[B] KaehlerDifferential.D A B b, 0)
      rw [hgL, hf, one_smul, hdB]
    · ext s : 4
      change f (g (0, 1 ⊗ₜ[S] KaehlerDifferential.D R S s)) =
        (0, 1 ⊗ₜ[S] KaehlerDifferential.D R S s)
      rw [hgR, hf, one_smul, hdS]
  let eDer := (g.restrictScalars D).compDer d
  have heB (b : B) : eDer (1 ⊗ₜ[A] b) = dD (1 ⊗ₜ[A] b) := by
    change g (d (1 ⊗ₜ[A] b)) = _
    rw [hdB, hgL]
    rfl
  have heS (s : S) : eDer (s ⊗ₜ[A] 1) = dD (s ⊗ₜ[A] 1) := by
    change g (d (s ⊗ₜ[A] 1)) = _
    rw [hdS, hgR]
    rfl
  have hder : eDer = dD := by
    ext t
    induction t using TensorProduct.inductionOn with
    | tmul s b =>
      have ht : s ⊗ₜ[A] b = (s ⊗ₜ[A] (1 : B)) * (1 ⊗ₜ[A] b) := by simp
      rw [ht, Derivation.leibniz, Derivation.leibniz, heB, heS]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hgf : g.comp f = LinearMap.id := by
    ext t : 4
    change g (f (1 ⊗ₜ[D] KaehlerDifferential.D R D t)) =
      1 ⊗ₜ[D] KaehlerDifferential.D R D t
    rw [hf, one_smul]
    exact DFunLike.congr_fun hder t
  exact ⟨{ f with
    invFun := g
    left_inv := fun y => DFunLike.congr_fun hgf y
    right_inv := fun x => DFunLike.congr_fun hfg x }⟩

end AlgebraicGeometry
