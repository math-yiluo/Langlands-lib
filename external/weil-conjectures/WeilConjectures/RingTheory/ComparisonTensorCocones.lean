/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

import WeilConjectures.RingTheory.ComparisonTensorLocalSystem

/-! # Coherent cocones for a base-changed tensor comparison

Source: Stacks Project, Algebra, Tag 02JO (3), construction of Ψ;
Tag 00DD for the tensor identifications.
(blueprint: lem-weil-pbc-comparison-tensor-cocones-n3)
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- Construct the comparison diagrams and their canonical tensor cocones, without
claiming that the cocones are colimits or that the limiting comparison is bijective.

Source: Stacks Project, Algebra, Tag 02JO (3), the displayed comparison maps Ψ.
(blueprint: lem-weil-pbc-comparison-tensor-cocones-n3)

Proof: write Bⱼ = F(j) tensor_{F(i₀)} B₀ and similarly Cⱼ. Transport P to Bⱼ
through the canonical Bᵢ → Bⱼ. Take Dⱼ = ULift (Bⱼ tensor_P Q), Eⱼ = ULift Cⱼ,
and conjugate their tensor transition maps by the ULift ring equivalences.
The identity hψ makes ψ F(i)-linear. Tensor ψ with F(j) over F(i), and use
cancellation to obtain αⱼ. Equivalently αⱼ(b tensor q) is φⱼ(b) times the image
of ψ(1 tensor q) in Cⱼ. This is P-balanced because hψ identifies the P-images.
This formula on pure tensors proves naturality and the left-inclusion identity.
The canonical maps Bⱼ → B are P-linear by hμB and cocone naturality; call them
μs. The maps μs tensor id_Q and Cⱼ → C define the two cocones, with points the
ULifts of B tensor_P Q and C and with equivalences dLim and cLim given by down.
The identities for their legs and transitions follow on pure tensors. The
identity hlim checks their comparison on the Q-inclusion; the global
left-inclusion identity he checks it on Bⱼ, including the new F(j) elements.
Tensor extensionality then gives the stated identity
with ζ at every stage. Finally cancellation identifies both vertices at k
with base changes of the vertices at j along Bⱼ → Bₖ, so the tensor universal
property proves each transition square is a pushout. No use of invertibility
of ζ, finite presentation, or nontriviality of any ring occurs.
-/
theorem exists_comparison_tensor_cocones
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (ζ : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q →+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (he : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      ζ.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(colimit F) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom)
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
    (hlim : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp ψ =
        ζ.comp (Algebra.TensorProduct.map μB (AlgHom.id P Q)).toRingHom) :
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
                  (∀ j : J, cLim.toRingHom.comp
                    ((cE.ι.app j).hom.comp (α.app j).hom) =
                    ζ.comp (dLim.toRingHom.comp (cD.ι.app j).hom)) ∧
                  (∀ {j k} (r : j ⟶ k), IsPushout (α.app j) (D.map r)
                    (E.map r) (α.app k)) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                  letI := aPs j
                  ((c j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)).comp
                    (Algebra.TensorProduct.includeLeftRingHom (R := P)
                      (A := ↥(F.obj j.val) ⊗[F.obj i₀] B₀) (B := Q)) =
                    (Algebra.TensorProduct.map (Algebra.ofId (F.obj j.val) (F.obj j.val))
                      φ₀).toRingHom) := by
  classical
  obtain ⟨aPs, D, E, α, d, c, cD, cE, dLim, cLim, μs,
      hμs, hcD, hDt, hcE, hEt, hpush, hcompat, hQ⟩ :=
    exists_comparison_tensor_local_system F i₀ B₀ C₀ φ₀ P Q aP i hi aPi μB hμB ψ hψ
  refine ⟨aPs, D, E, α, d, c, cD, cE, dLim, cLim, μs,
    hμs, hcD, hDt, hcE, hEt, ?_, hpush, hcompat⟩
  intro j
  let := (colimit.ι F i₀).hom.toAlgebra
  let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
  let := aP
  let := aPs j
  have hcomp :
      (cLim.toRingHom.comp ((cE.ι.app j).hom.comp (α.app j).hom)).comp
        (d j).symm.toRingHom =
      ζ.comp (Algebra.TensorProduct.map (μs j) (AlgHom.id P Q)).toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro b
      have hc := DFunLike.congr_fun (hcE j)
        ((α.app j).hom ((d j).symm (b ⊗ₜ[P] 1)))
      have hb := DFunLike.congr_fun (hcompat j) b
      have hd := DFunLike.congr_fun he (μs j b)
      have hm := DFunLike.congr_fun (hμs j) b
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeLeftRingHom_apply] at hc hb hd hm
      change cLim ((cE.ι.app j).hom ((α.app j).hom
        ((d j).symm (b ⊗ₜ[P] 1)))) = ζ (μs j b ⊗ₜ[P] 1)
      erw [hc, hb, hd, hm]
      clear hc hb hd hm
      induction b using TensorProduct.inductionOn with
      | tmul a b => simp
      | add b₁ b₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    · apply RingHom.ext
      intro q
      have hq := hQ j q
      have hl := DFunLike.congr_fun hlim (1 ⊗ₜ[P] q)
      simpa using hq.trans hl
  apply RingHom.ext
  intro z
  have hz := DFunLike.congr_fun hcomp (d j z)
  have hd := DFunLike.congr_fun (hcD j) z
  simpa using hz.trans (congrArg ζ hd.symm)


end RingHom
