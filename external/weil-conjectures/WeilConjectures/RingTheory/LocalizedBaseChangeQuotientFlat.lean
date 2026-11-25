/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness

/-!
# Flat quotients after localized base change

Source: Stacks Project, Algebra, Tag 00MO.
(blueprint: lem-weil-pbc-localized-base-change-quotient-flat)
-/

@[expose] public section

universe u v w z t

open scoped TensorProduct

namespace Module

private noncomputable def baseChangeTensorCancel
    {R : Type u} {S : Type v} {C : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing C] [Algebra R S] [Algebra R C]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    : letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
      (C ⊗[R] S) ⊗[S] M ≃ₗ[C] C ⊗[R] M := by
  let : Algebra S (C ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let e₀ : (C ⊗[R] S) ⊗[S] M ≃ₗ[R] C ⊗[R] M :=
    ((TensorProduct.congr (Algebra.TensorProduct.commRight R S C).symm.toLinearEquiv
      (LinearEquiv.refl S M)).trans
      ((TensorProduct.comm S (S ⊗[R] C) M).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M C))).restrictScalars R
      ≪≫ₗ TensorProduct.comm R M C
  refine { e₀ with map_smul' := ?_ }
  intro c x
  change e₀ (c • x) = c • e₀ x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul b m =>
    induction b using TensorProduct.inductionOn with
    | add b d hb hd => simp [smul_add, TensorProduct.add_tmul, hb, hd]
    | tmul c' s =>
      simp [e₀, TensorProduct.smul_tmul', Algebra.smul_def,
        Algebra.TensorProduct.commRight]


/-- Flatness of the quotient after localized base change.
Source: Stacks Project, Algebra, Tag 00MO, proof, first paragraph; Tags 00HI, 00CS, 00DK.
(blueprint: lem-weil-pbc-localized-base-change-quotient-flat)

Proof:
1. Put Q = R/I and Q' = R'/IR'. Give Q' its algebra structure over Q through
   the quotient map. Flat base change and tensor cancellation make Q' tensor_R M
   flat over Q'.
2. Put A = S tensor_R R', B = Q' tensor_R' A and D = Q' tensor_R' S'.
   The localization witness q is R'-linear by its pure-tensor formula.
   Localization base change makes D a localization of B at the image of W.
3. Tensor cancellation identifies B with C = Q' tensor_R S, preserving both the
   S-action and the Q'-action. The proved helper identifies C tensor_S M with
   Q' tensor_R M. Thus B tensor_S M is Q'-flat.
4. Localization commutes with tensoring over S, so D tensor_S M is the localization
   of B tensor_S M and is Q'-flat by localization preservation of base flatness.
   Tensor symmetry and the heterobasic right-commutation equivalence identify the
   stated module with D tensor_S M. The equivalence is Q'-linear because R' maps
   surjectively onto Q'.

Neither finiteness, Noetherianity, locality, nor properness of I is needed. -/
theorem flat_quotient_localized_baseChange
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type z}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    (I : Ideal R)
    (M : Type t) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M]
    (hloc : ∃ (q : S ⊗[R] R' →+* S') (W : Submonoid (S ⊗[R] R')),
      (∀ (s : S) (r' : R'), q (s ⊗ₜ[R] r') =
        algebraMap S S' s * algebraMap R' S' r') ∧
      (letI := q.toAlgebra; IsLocalization W S'))
    (hquot : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)) :
    Module.Flat (R' ⧸ I.map (algebraMap R R'))
      ((R' ⧸ I.map (algebraMap R R')) ⊗[R'] (S' ⊗[S] M)) := by
  have hbase : Module.Flat (R' ⧸ I.map (algebraMap R R'))
      ((R' ⧸ I.map (algebraMap R R')) ⊗[R] M) := by
    let Q := R ⧸ I
    let Q' := R' ⧸ I.map (algebraMap R R')
    let : Algebra Q Q' := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    have h₁ : Module.Flat Q' (Q' ⊗[Q] (Q ⊗[R] M)) := inferInstance
    exact Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R Q Q' Q' M).symm
  obtain ⟨q, W, hq, hloc⟩ := hloc
  let A := S ⊗[R] R'
  let : Algebra R' A := Algebra.TensorProduct.rightAlgebra
  let : Algebra A S' := q.toAlgebra
  have : IsLocalization W S' := hloc
  have : IsScalarTower R' A S' := IsScalarTower.of_algebraMap_eq fun r' => by
    change algebraMap R' S' r' = q (1 ⊗ₜ[R] r')
    simp [hq]
  let q' : A →ₐ[R'] S' := IsScalarTower.toAlgHom R' A S'
  let Q' := R' ⧸ I.map (algebraMap R R')
  let B := Q' ⊗[R'] A
  let : Algebra A B := Algebra.TensorProduct.rightAlgebra
  let D := Q' ⊗[R'] S'
  let : Algebra S' D := Algebra.TensorProduct.rightAlgebra
  let g : B →ₐ[Q'] D := Algebra.TensorProduct.map (AlgHom.id Q' Q') q'
  let : Algebra B D := g.toRingHom.toAlgebra
  have : IsScalarTower Q' B D := IsScalarTower.of_algebraMap_eq fun x => by
    exact (g.commutes x).symm
  have hlocD : IsLocalization
      (W.map (Algebra.TensorProduct.includeRight (R := R') (A := Q'))) D := by
    apply IsLocalization.tensorProduct_tensorProduct_right R' Q' W S'
    apply RingHom.ext
    intro a
    change g (1 ⊗ₜ[R'] a) = 1 ⊗ₜ[R'] q' a
    exact Algebra.TensorProduct.map_tmul _ _ _ _
  let C := Q' ⊗[R] S
  let : Algebra S C := Algebra.TensorProduct.rightAlgebra
  let eB : B ≃ₐ[Q'] C :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : Q' ≃ₐ[Q'] Q')
      (Algebra.TensorProduct.commRight R R' S).symm).trans
      (Algebra.TensorProduct.cancelBaseChange R R' Q' Q' S)
  let : Algebra S B :=
    ((Algebra.TensorProduct.includeRight (R := R')
    (A := Q') (B := A)).toRingHom.comp (algebraMap S A)).toAlgebra
  let : Algebra S D :=
    ((Algebra.TensorProduct.includeRight (R := R')
    (A := Q') (B := S')).toRingHom.comp (algebraMap S S')).toAlgebra
  have : IsScalarTower S A S' := IsScalarTower.of_algebraMap_eq fun s => by
    change algebraMap S S' s = q (s ⊗ₜ[R] 1)
    simp [hq]
  have : IsScalarTower S A B := IsScalarTower.of_algebraMap_eq fun s => rfl
  have : IsScalarTower S S' D := IsScalarTower.of_algebraMap_eq fun s => rfl
  have : IsScalarTower S B D := IsScalarTower.of_algebraMap_eq fun s => by
    change (1 : Q') ⊗ₜ[R'] algebraMap S S' s = g (1 ⊗ₜ[R'] (s ⊗ₜ[R] 1))
    rw [Algebra.TensorProduct.map_tmul]
    change 1 ⊗ₜ[R'] algebraMap S S' s = 1 ⊗ₜ[R'] q (s ⊗ₜ[R] 1)
    simp [hq]
  let g₀ : B →ₗ[B] D := Algebra.linearMap B D
  have : IsLocalizedModule
      (W.map (Algebra.TensorProduct.includeRight (R := R') (A := Q'))) g₀ := by
    exact (isLocalizedModule_iff_isLocalization' _ D).mpr hlocD
  let U := W.map (Algebra.TensorProduct.includeRight (R := R') (A := Q'))
  let f := TensorProduct.AlgebraTensorModule.rTensor S M g₀
  have heq := (IsLocalizedModule.iso U f).restrictScalars Q'
  let eBS : B ≃ₐ[S] C := { eB with
    commutes' := fun s => by
      change eB (1 ⊗ₜ[R'] (s ⊗ₜ[R] 1)) = 1 ⊗ₜ[R] s
      change (Algebra.TensorProduct.cancelBaseChange R R' Q' Q' S)
        (1 ⊗ₜ[R'] (1 ⊗ₜ[R] s)) = 1 ⊗ₜ[R] s
      simp only [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul] }
  let eN₀ : B ⊗[S] M ≃ₗ[S] C ⊗[S] M :=
    TensorProduct.congr eBS.toLinearEquiv (LinearEquiv.refl S M)
  let eN : B ⊗[S] M ≃ₗ[Q'] C ⊗[S] M := { eN₀ with
    map_smul' := by
      intro c x
      change eN₀ (c • x) = c • eN₀ x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp [smul_add, hx, hy]
      | tmul b m =>
        simp only [eN₀, TensorProduct.smul_tmul', TensorProduct.congr_tmul]
        exact congrArg (fun y => y ⊗ₜ[S] m) (eB.toLinearEquiv.map_smul c b) }
  have hN : Module.Flat Q' (B ⊗[S] M) :=
    (Module.Flat.equiv_iff
      (eN.trans (baseChangeTensorCancel (R := R) (S := S)
        (C := Q') (M := M)))).mpr hbase
  have hD : Module.Flat Q' (D ⊗[S] M) :=
    (Module.Flat.equiv_iff heq).mp (Module.Flat.localizedModule_of_algebra U hN)
  let e₀ : (Q' ⊗[R'] (S' ⊗[S] M)) ≃ₗ[R'] D ⊗[S] M :=
    (TensorProduct.comm R' Q' (S' ⊗[S] M)) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.rightComm R' S S' S' M Q').restrictScalars R' ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.congr
        (Algebra.TensorProduct.commRight R' S' Q').toLinearEquiv
        (LinearEquiv.refl S M)).restrictScalars R'
  exact (Module.Flat.equiv_iff
    (e₀.extendScalarsOfSurjective Ideal.Quotient.mk_surjective)).mpr hD

end Module
