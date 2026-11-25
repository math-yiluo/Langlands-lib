/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits


/-! # Canonical limiting tensor cocones
Source: Stacks Project, Algebra, Tag 02JO (3), construction of Ψ, and Tag 00DD.
(blueprint: lem-weil-pbc-comparison-tensor-canonical-cocones-b4)
-/
@[expose] public section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
universe v w x y
namespace RingHom
/-- Attach canonical limiting tensor cocones to arbitrary stage diagrams.
Source: Stacks Project, Algebra, Tag 00DD; canonical cocones in Tag 02JO (3).
(blueprint: lem-weil-pbc-comparison-tensor-canonical-cocones-b4)

Proof: take the points to be ULifts of B tensor_P Q and C, with down ring
equivalences. Define source legs by conjugating μ_j tensor id_Q and target
legs by conjugating the canonical tensor maps to C. The hypotheses identify
stage transitions with the canonical maps. The canonical maps to the colimit
compose with those transitions, by colimit.w and tensor-map composition.
For the source maps the ring-hom identities also give equality of P-algebra
maps, hence equality after tensoring with Q. Thus the legs are natural and
form cocones. Cancellation of the up/down equivalences proves both displayed
leg identities. This uses no comparison transformation and no property of ψ.
-/
theorem exists_comparison_tensor_canonical_cocones
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (i : I) (hi : i₀ ≤ i)
    (aPs : ∀ j : {j : I // i ≤ j},
          letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
          Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀))
        (D E : {j : I // i ≤ j} ⥤ CommRingCat.{max v w x y})
    (d : ∀ j : {j : I // i ≤ j},
              letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
              letI := aPs j
              ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q)
    (c : ∀ j : {j : I // i ≤ j},
                letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀))
    (μs : ∀ j : {j : I // i ≤ j},
                    letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := aPs j
                    letI := aP
                    (↥(F.obj j.val) ⊗[F.obj i₀] B₀) →ₐ[P]
                      (↥(colimit F) ⊗[F.obj i₀] B₀))
    (hμs : (∀ j : {j : I // i ≤ j},
                    letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
                      { (colimit.ι F j.val).hom with
                        commutes' := fun s ↦
                          congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
                            (colimit.w F (homOfLE (hi.trans j.property))) }
                    (μs j).toRingHom =
                      (Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) B₀)).toRingHom))
    (hDt : (∀ {j k : {j : I // i ≤ j}} (r : j ⟶ k),
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
                          (d j).toRingHom))
    (hEt : (∀ {j k : {j : I // i ≤ j}} (r : j ⟶ k),
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
                        (c j).toRingHom)) :
      let J := {j : I // i ≤ j}
              ∃ (cD : Cocone D) (cE : Cocone E),
                ∃ (dLim : letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := aP
                    ↥cD.pt ≃+* (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q)
                  (cLim : letI := (colimit.ι F i₀).hom.toAlgebra
                    ↥cE.pt ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀)),
                  (∀ j : J,
                    letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := aPs j
                    letI := aP
                    dLim.toRingHom.comp (cD.ι.app j).hom =
                      (Algebra.TensorProduct.map (μs j) (AlgHom.id P Q)).toRingHom.comp
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
                        (c j).toRingHom) := by
  classical
  let J := {j : I // i ≤ j}
  let := (colimit.ι F i₀).hom.toAlgebra
  let := aP
  let αlim (j : J) :
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
    { (colimit.ι F j.val).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
        (colimit.w F (homOfLE (hi.trans j.property))) }
  let gD (j : J) : D.obj j →+* (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q :=
    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
    letI := aPs j
    (Algebra.TensorProduct.map (μs j) (AlgHom.id P Q)).toRingHom.comp (d j).toRingHom
  let gE (j : J) : E.obj j →+* ↥(colimit F) ⊗[F.obj i₀] C₀ :=
    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
    (Algebra.TensorProduct.map (αlim j) (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp
      (c j).toRingHom
  have hD : ∀ {j k : J} (r : j ⟶ k), (gD k).comp (D.map r).hom = gD j := by
    intro j k r
    let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
    let := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
    let := aPs j
    let := aPs k
    obtain ⟨β, hβ, hd⟩ := hDt r
    have hμβ : (μs k).comp β = μs j := by
      ext z
      have hk := DFunLike.congr_fun (hμs k) (β z)
      have hj := DFunLike.congr_fun (hμs j) z
      have hb := DFunLike.congr_fun hβ z
      simp only [AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom] at hk hj hb
      change μs k (β z) = μs j z
      rw [hk, hb, hj]
      clear hk hj hb
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
          simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.coe_mk]
          congr 1
          exact congrArg (fun f : F.obj j.val ⟶ colimit F ↦ f a)
            (colimit.w F (homOfLE (leOfHom r)))
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    apply RingHom.ext
    intro z
    have hz := DFunLike.congr_fun hd z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hz
    change Algebra.TensorProduct.map (μs k) (AlgHom.id P Q)
      (d k ((D.map r).hom z)) = Algebra.TensorProduct.map (μs j) (AlgHom.id P Q) (d j z)
    rw [hz, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hμβ]
    rfl
  have hE : ∀ {j k : J} (r : j ⟶ k), (gE k).comp (E.map r).hom = gE j := by
    intro j k r
    let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
    let := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
    apply RingHom.ext
    intro z
    have hz := DFunLike.congr_fun (hEt r) z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hz
    change Algebra.TensorProduct.map (αlim k) (AlgHom.id (F.obj i₀) C₀)
      (c k ((E.map r).hom z)) =
      Algebra.TensorProduct.map (αlim j) (AlgHom.id (F.obj i₀) C₀) (c j z)
    rw [hz]
    generalize c j z = t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.coe_mk]
        congr 1
        exact congrArg (fun f : F.obj j.val ⟶ colimit F ↦ f a)
          (colimit.w F (homOfLE (leOfHom r)))
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  let dLim : ULift.{max v w x y} ((↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q) ≃+*
      ((↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q) := ULift.ringEquiv
  let cLim : ULift.{max v w x y} (↥(colimit F) ⊗[F.obj i₀] C₀) ≃+*
      (↥(colimit F) ⊗[F.obj i₀] C₀) := ULift.ringEquiv
  let cD : Cocone D :=
    { pt := CommRingCat.of (ULift.{max v w x y}
        ((↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q))
      ι :=
        { app := fun j ↦ CommRingCat.ofHom (dLim.symm.toRingHom.comp (gD j))
          naturality := by
            intro j k r
            apply CommRingCat.hom_ext
            apply RingHom.ext
            intro z
            exact congrArg dLim.symm (DFunLike.congr_fun (hD r) z) } }
  let cE : Cocone E :=
    { pt := CommRingCat.of (ULift.{max v w x y} (↥(colimit F) ⊗[F.obj i₀] C₀))
      ι :=
        { app := fun j ↦ CommRingCat.ofHom (cLim.symm.toRingHom.comp (gE j))
          naturality := by
            intro j k r
            apply CommRingCat.hom_ext
            apply RingHom.ext
            intro z
            exact congrArg cLim.symm (DFunLike.congr_fun (hE r) z) } }
  refine ⟨cD, cE, dLim, cLim, ?_, ?_⟩
  · intro j
    apply RingHom.ext
    intro z
    exact dLim.apply_symm_apply (gD j z)
  · intro j
    apply RingHom.ext
    intro z
    exact cLim.apply_symm_apply (gE j z)

end RingHom
