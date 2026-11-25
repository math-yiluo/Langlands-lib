/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

import WeilConjectures.RingTheory.ComparisonTensorDiagrams
import WeilConjectures.RingTheory.ComparisonTensorCanonicalMaps
import WeilConjectures.RingTheory.ComparisonTensorCanonicalCocones

/-! # Local tensor comparison system
Source: Stacks Project, Algebra, Tag 02JO (3), construction of Ψ, and Tag 00DD.
(blueprint: lem-weil-pbc-comparison-tensor-local-system-j3)
-/
@[expose] public section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
universe v w x y
namespace RingHom
/-- Construct the comparison system without a global comparison map.
Source: Stacks Project, Algebra, Tags 02JO (3) and 00DD.
(blueprint: lem-weil-pbc-comparison-tensor-local-system-j3)

Proof: give B_j the P-structure induced from B_i by the tensor transition.
Lift the tensor rings to the common universe and conjugate their canonical
transition maps by the ULift equivalences. Base-change ψ from F(i) to F(j)
and cancel the iterated tensors to obtain the comparison components.
On b tensor q the component is φ_j(b) times the image of ψ(1 tensor q).
The identity hψ gives P-balancedness, left compatibility and naturality.
Take the cocone points to be the ULifts of the limit tensor rings, with legs
the canonical tensor maps. If t_ij : B_i → B_j is the canonical transition,
the P-action on B_j is p ↦ t_ij(algebraMap P B_i p). Cocone naturality gives
μ_j composed with t_ij = μB, so μB's P-linearity proves μ_j's P-linearity.
The tensor-map composition formulas
prove the leg and transition identities. On the Q-inclusion every comparison
has the same image in the limit, namely μC_i(ψ(1 tensor q)), proving the last
clause. Finally tensor cancellation identifies both vertices at k with base
changes of the vertices at j along B_j to B_k; the tensor universal property
therefore proves the transition squares are pushouts. No global ζ is used.
-/
theorem exists_comparison_tensor_local_system
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (i : I) (hi : i₀ ≤ i)
    (aPi : letI := (F.map (homOfLE hi)).hom.toAlgebra
      Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀))
    (μB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] B₀))
    (hμB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      μB.toRingHom =
        (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀)).toRingHom)
    (ψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ((↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q) →+* (↥(F.obj i) ⊗[F.obj i₀] C₀))
    (hψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ψ.comp (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(F.obj i) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom)
 :
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
              ∃ (cD : Cocone D) (cE : Cocone E),
                ∃ (dLim : letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := aP
                    ↥cD.pt ≃+* (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q)
                  (cLim : letI := (colimit.ι F i₀).hom.toAlgebra
                    ↥cE.pt ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀)),
                  ∃ (μs : ∀ j : J,
                    letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := aPs j
                    letI := aP
                    (↥(F.obj j.val) ⊗[F.obj i₀] B₀) →ₐ[P]
                      (↥(colimit F) ⊗[F.obj i₀] B₀)),
                  (∀ j : J,
                    letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
                      { (colimit.ι F j.val).hom with
                        commutes' := fun s ↦
                          congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
                            (colimit.w F (homOfLE (hi.trans j.property))) }
                    (μs j).toRingHom =
                      (Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) B₀)).toRingHom) ∧
                  (∀ j : J,
                    letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := aPs j
                    letI := aP
                    dLim.toRingHom.comp (cD.ι.app j).hom =
                      (Algebra.TensorProduct.map (μs j) (AlgHom.id P Q)).toRingHom.comp
                        (d j).toRingHom) ∧
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
                  (∀ j : J,
                    letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
                      { (colimit.ι F j.val).hom with
                        commutes' := fun s ↦
                          congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
                            (colimit.w F (homOfLE (hi.trans j.property))) }
                    cLim.toRingHom.comp (cE.ι.app j).hom =
                      (Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp
                        (c j).toRingHom) ∧
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
                      φ₀).toRingHom)
 ∧
                  (∀ (j : J) (q : Q),
                    letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := (F.map (homOfLE hi)).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := aPi
                    letI := aPs j
                    let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
                      { (colimit.ι F i).hom with
                        commutes' := fun s ↦
                          congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
                            (colimit.w F (homOfLE hi)) }
                    cLim ((cE.ι.app j).hom ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q)))) =
                      Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)
                        (ψ (1 ⊗ₜ[P] q))) := by
  classical
  obtain ⟨aPs, D, E, α, d, c, βs, hβs, hDt, hEt, hpush, hcompat, hQ⟩ :=
    exists_comparison_tensor_diagrams F i₀ B₀ C₀ φ₀ P Q i hi aPi ψ hψ
  obtain ⟨μs, hμs⟩ :=
    exists_comparison_tensor_canonical_maps F i₀ B₀ P aP i hi aPi μB hμB aPs βs hβs
  obtain ⟨cD, cE, dLim, cLim, hcD, hcE⟩ :=
    exists_comparison_tensor_canonical_cocones F i₀ B₀ C₀ P Q aP i hi
      aPs D E d c μs hμs hDt hEt
  refine ⟨aPs, D, E, α, d, c, cD, cE, dLim, cLim, μs,
    hμs, hcD, hDt, hcE, hEt, hpush, hcompat, ?_⟩
  intro j q
  let := (colimit.ι F i₀).hom.toAlgebra
  let := (F.map (homOfLE hi)).hom.toAlgebra
  let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
  let := aPi
  let := aPs j
  have hc := DFunLike.congr_fun (hcE j)
    ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q)))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hc
  dsimp only
  erw [hc, hQ j q]
  clear hc
  let αij : F.obj i →ₐ[F.obj i₀] F.obj j.val :=
    { (F.map (homOfLE j.property)).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f s)
        (F.map_comp (homOfLE hi) (homOfLE j.property)).symm }
  let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
    { (colimit.ι F j.val).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
        (colimit.w F (homOfLE (hi.trans j.property))) }
  let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
    { (colimit.ι F i).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
        (colimit.w F (homOfLE hi)) }
  have hcomp : αj.comp αij = αi := by
    ext z
    exact congrArg (fun f : F.obj i ⟶ colimit F ↦ f z)
      (colimit.w F (homOfLE j.property))
  change Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) C₀)
    (Algebra.TensorProduct.map αij (AlgHom.id (F.obj i₀) C₀) (ψ (1 ⊗ₜ[P] q))) = _
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hcomp]
  rfl


end RingHom
