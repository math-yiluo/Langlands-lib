/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs


import WeilConjectures.RingTheory.ComparisonTensorStageDiagrams

import WeilConjectures.RingTheory.ComparisonTensorNaturalExtension

import WeilConjectures.RingTheory.ComparisonTensorTransitionPushout

/-! # Finite-stage tensor comparison diagrams
Source: Stacks Project, Algebra, Tag 02JO (3), construction of Ψ, and Tag 00DD.
(blueprint: lem-weil-pbc-comparison-tensor-diagrams-b4)
-/
@[expose] public section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
universe v w x y
namespace RingHom
/-- Construct just the finite-stage comparison diagrams, without cocones.
Source: Stacks Project, Algebra, Tags 02JO (3) and 00DD.
(blueprint: lem-weil-pbc-comparison-tensor-diagrams-b4)

Proof: induce the P-action on B_j from B_i along the canonical transition.
The initial transitions B_i to B_j are P-linear by construction.
Use ULift ring equivalences to put all stage tensor rings in one universe.
Conjugate the tensor transition maps to form D and E. Extend ψ by scalar
extension from F(i) to F(j), cancelling
iterated tensor products. Its value on b tensor q is the canonical φ_j(b)
times the transition image of ψ(1 tensor q). The hypothesis hψ gives the
balancing identity. This formula proves naturality, compatibility on the
left inclusion, and the finite-stage Q-coordinate formula. Cancellation
identifies the square at j to k with a tensor base-change square, so the
tensor universal property proves it is a pushout. No limiting cocone is
constructed here. Trivial rings and singleton index types cause no exception.
-/
theorem exists_comparison_tensor_diagrams
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v})
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (i : I) (hi : i₀ ≤ i)
    (aPi : letI := (F.map (homOfLE hi)).hom.toAlgebra
      Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀))
    (ψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ((↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q) →+* (↥(F.obj i) ⊗[F.obj i₀] C₀))
    (hψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ψ.comp (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(F.obj i) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom) :
      let J := {j : I // i ≤ j}
      ∃ (aPs : ∀ j : J,
          letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
          Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀)),
        ∃ (D E : J ⥤ CommRingCat.{max v w x y}) (α : D ⟶ E),
          ∃ (d : ∀ j : J,
              letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
              letI := aPs j
              ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q),
            ∃ (c : ∀ j : J,
                letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀)),
                  ∃ (βs : ∀ j : J,
                    letI := (F.map (homOfLE hi)).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := aPi
                    letI := aPs j
                    (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P]
                      (↥(F.obj j.val) ⊗[F.obj i₀] B₀)),
                  (∀ j : J,
                    letI := (F.map (homOfLE hi)).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    let αij : F.obj i →ₐ[F.obj i₀] F.obj j.val :=
                      { (F.map (homOfLE j.property)).hom with
                        commutes' := fun s ↦
                          congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f s)
                            (F.map_comp (homOfLE hi) (homOfLE j.property)).symm }
                    (βs j).toRingHom =
                      (Algebra.TensorProduct.map αij (AlgHom.id (F.obj i₀) B₀)).toRingHom) ∧
                  (∀ {j k : J} (r : j ⟶ k),
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
                    letI := aPs j
                    letI := aPs k
                    ∃ β : (↥(F.obj j.val) ⊗[F.obj i₀] B₀) →ₐ[P]
                        (↥(F.obj k.val) ⊗[F.obj i₀] B₀),
                      (let αjk : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
                        { (F.map (homOfLE (leOfHom r))).hom with
                          commutes' := fun s ↦
                            congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
                              (F.map_comp (homOfLE (hi.trans j.property))
                                (homOfLE (leOfHom r))).symm };
                        β.toRingHom =
                          (Algebra.TensorProduct.map αjk
                            (AlgHom.id (F.obj i₀) B₀)).toRingHom) ∧
                      (d k).toRingHom.comp (D.map r).hom =
                        (Algebra.TensorProduct.map β (AlgHom.id P Q)).toRingHom.comp
                          (d j).toRingHom) ∧
                  (∀ {j k : J} (r : j ⟶ k),
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
                    let αjk : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
                        { (F.map (homOfLE (leOfHom r))).hom with
                          commutes' := fun s ↦
                            congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
                              (F.map_comp (homOfLE (hi.trans j.property))
                                (homOfLE (leOfHom r))).symm }
                    (c k).toRingHom.comp (E.map r).hom =
                      (Algebra.TensorProduct.map αjk (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp
                        (c j).toRingHom) ∧
                  (∀ {j k} (r : j ⟶ k), IsPushout (α.app j) (D.map r)
                    (E.map r) (α.app k)) ∧
                  (∀ j : J,
                  letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                  letI := aPs j
                  ((c j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)).comp
                    (Algebra.TensorProduct.includeLeftRingHom (R := P)
                      (A := ↥(F.obj j.val) ⊗[F.obj i₀] B₀) (B := Q)) =
                    (Algebra.TensorProduct.map (Algebra.ofId (F.obj j.val) (F.obj j.val))
                      φ₀).toRingHom) ∧
                  (∀ (j : J) (q : Q),
                    letI := (F.map (homOfLE hi)).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := aPi
                    letI := aPs j
                    let αij : F.obj i →ₐ[F.obj i₀] F.obj j.val :=
                      { (F.map (homOfLE j.property)).hom with
                        commutes' := fun s ↦
                          congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f s)
                            (F.map_comp (homOfLE hi) (homOfLE j.property)).symm }
                    c j ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q))) =
                      Algebra.TensorProduct.map αij (AlgHom.id (F.obj i₀) C₀)
                        (ψ (1 ⊗ₜ[P] q))) := by
  obtain ⟨aPs, D, E, d, c, βs, hβs, hDt, hEt⟩ :=
    exists_comparison_tensor_stage_diagrams F i₀ B₀ C₀ P Q i hi aPi
  obtain ⟨α, hcompat, hQ⟩ :=
    exists_comparison_tensor_natural_extension F i₀ B₀ C₀ φ₀ P Q i hi aPi ψ hψ
      aPs D E d c βs hβs hDt hEt
  refine ⟨aPs, D, E, α, d, c, βs, hβs, hDt, hEt, ?_, hcompat, hQ⟩
  intro j k r
  exact comparison_tensor_transition_isPushout F i₀ B₀ C₀ φ₀ P Q i hi aPi
    aPs D E α d c hDt hEt hcompat r

end RingHom
