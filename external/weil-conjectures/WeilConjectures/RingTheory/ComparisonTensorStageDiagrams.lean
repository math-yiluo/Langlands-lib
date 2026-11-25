/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Algebra.Ring.ULift


/-! # A step of finite-stage tensor comparison
Source: Stacks Project, Algebra, Tags 02JO (3) and 00DD.
-/
@[expose] public section
open scoped TensorProduct
open CategoryTheory
universe v w x y
namespace RingHom
/-- A component of the finite-stage tensor comparison construction.
Source: Stacks Project, Algebra, Tags 02JO (3) and 00DD.
(blueprint: lem-weil-pbc-comparison-tensor-stage-diagrams-j3)

Proof: Write t_ij for the F(i₀)-algebra transition F(i)→F(j), and let
b_ij=t_ij⊗id_B₀. Give B_j its P-action via the actual ring map
b_ij composed with the algebra map P→B_i. Functoriality gives
b_jk composed with b_ij=b_ik, so every canonical transition is P-linear.
Take D_j=ULift(B_j⊗_P Q), E_j=ULift(C_j), and define their maps by
RingHom.ulift of β_jk⊗id_Q and t_jk⊗id_C₀. Tensor map identity and composition
laws prove both functor laws. Take d_j and c_j to be ULift.ringEquiv and
βs_j to be b_ij with its induced P-linearity. All asserted conjugation
identities follow directly from these definitions. This construction also
works for singleton or nonskeletal preorders and for zero rings.
-/
theorem exists_comparison_tensor_stage_diagrams
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v})
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (i : I) (hi : i₀ ≤ i)
    (aPi : let := (F.map (homOfLE hi)).hom.toAlgebra
      Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀)) :
      let J := {j : I // i ≤ j}
      ∃ (aPs : ∀ j : J,
          let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
          Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀)),
        ∃ (D E : J ⥤ CommRingCat.{max v w x y}),
          ∃ (d : ∀ j : J,
              let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
              let := aPs j
              ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q),
            ∃ (c : ∀ j : J,
                let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀)),
                  ∃ (βs : ∀ j : J,
                    let := (F.map (homOfLE hi)).hom.toAlgebra
                    let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    let := aPi
                    let := aPs j
                    (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P]
                      (↥(F.obj j.val) ⊗[F.obj i₀] B₀)),
                  (∀ j : J,
                    let := (F.map (homOfLE hi)).hom.toAlgebra
                    let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    let αij : F.obj i →ₐ[F.obj i₀] F.obj j.val :=
                      { (F.map (homOfLE j.property)).hom with
                        commutes' := fun s ↦
                          congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f s)
                            (F.map_comp (homOfLE hi) (homOfLE j.property)).symm }
                    (βs j).toRingHom =
                      (Algebra.TensorProduct.map αij (AlgHom.id (F.obj i₀) B₀)).toRingHom) ∧
                  (∀ {j k : J} (r : j ⟶ k),
                    let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    let := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
                    let := aPs j
                    let := aPs k
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
                    let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    let := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
                    let αjk : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
                        { (F.map (homOfLE (leOfHom r))).hom with
                          commutes' := fun s ↦
                            congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
                              (F.map_comp (homOfLE (hi.trans j.property))
                                (homOfLE (leOfHom r))).symm }
                    (c k).toRingHom.comp (E.map r).hom =
                      (Algebra.TensorProduct.map αjk (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp
                        (c j).toRingHom) := by
  classical
  let J := {j : I // i ≤ j}
  let : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
  let := aPi
  let (j : J) : Algebra (F.obj i₀) (F.obj j.val) :=
    (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
  let t₀ (j : J) : F.obj i →ₐ[F.obj i₀] F.obj j.val :=
    { (F.map (homOfLE j.property)).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f s)
        (F.map_comp (homOfLE hi) (homOfLE j.property)).symm }
  let t {j k : J} (r : j ⟶ k) : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
    { (F.map (homOfLE (leOfHom r))).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
        (F.map_comp (homOfLE (hi.trans j.property)) (homOfLE (leOfHom r))).symm }
  let B (j : J) := ↥(F.obj j.val) ⊗[F.obj i₀] B₀
  let C (j : J) := ↥(F.obj j.val) ⊗[F.obj i₀] C₀
  let b₀ (j : J) := Algebra.TensorProduct.map (t₀ j) (AlgHom.id (F.obj i₀) B₀)
  let b {j k : J} (r : j ⟶ k) :=
    Algebra.TensorProduct.map (t r) (AlgHom.id (F.obj i₀) B₀)
  let e {j k : J} (r : j ⟶ k) :=
    Algebra.TensorProduct.map (t r) (AlgHom.id (F.obj i₀) C₀)
  have ht₀ {j k : J} (r : j ⟶ k) : (t r).comp (t₀ j) = t₀ k := by
    apply AlgHom.ext
    intro z
    exact congrArg (fun f : F.obj i ⟶ F.obj k.val ↦ f z)
      (F.map_comp (homOfLE j.property) (homOfLE (leOfHom r))).symm
  have hb₀ {j k : J} (r : j ⟶ k) : (b r).comp (b₀ j) = b₀ k := by
    dsimp only [b, b₀]
    rw [← Algebra.TensorProduct.map_comp, ht₀ r]
    rfl
  let aPs (j : J) : Algebra P (B j) :=
    ((b₀ j).toRingHom.comp (algebraMap P (↥(F.obj i) ⊗[F.obj i₀] B₀))).toAlgebra
  let (j : J) : Algebra P (B j) := aPs j
  let βs (j : J) : (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P] B j :=
    { (b₀ j).toRingHom with commutes' := fun _ ↦ rfl }
  let β {j k : J} (r : j ⟶ k) : B j →ₐ[P] B k :=
    { (b r).toRingHom with
      commutes' := fun p ↦ DFunLike.congr_fun (hb₀ r)
        (algebraMap P (↥(F.obj i) ⊗[F.obj i₀] B₀) p) }
  have ht_id (j : J) : t (𝟙 j) = AlgHom.id (F.obj i₀) (F.obj j.val) := by
    apply AlgHom.ext
    intro z
    change (F.map (homOfLE (show j.val ≤ j.val from le_rfl))) z = z
    rw [show homOfLE (show j.val ≤ j.val from le_rfl) = 𝟙 j.val from Subsingleton.elim _ _]
    rw [F.map_id]
    rfl
  have ht_comp {j k l : J} (r : j ⟶ k) (s : k ⟶ l) :
      t (r ≫ s) = (t s).comp (t r) := by
    apply AlgHom.ext
    intro z
    exact congrArg (fun f : F.obj j.val ⟶ F.obj l.val ↦ f z)
      (F.map_comp (homOfLE (leOfHom r)) (homOfLE (leOfHom s)))
  have hβ_id (j : J) : β (𝟙 j) = AlgHom.id P (B j) := by
    apply AlgHom.ext
    intro z
    change Algebra.TensorProduct.map (t (𝟙 j)) (AlgHom.id (F.obj i₀) B₀) z = z
    rw [ht_id, Algebra.TensorProduct.map_id]
    rfl
  have hβ_comp {j k l : J} (r : j ⟶ k) (s : k ⟶ l) :
      β (r ≫ s) = (β s).comp (β r) := by
    apply AlgHom.ext
    intro z
    change Algebra.TensorProduct.map (t (r ≫ s)) (AlgHom.id (F.obj i₀) B₀) z =
      Algebra.TensorProduct.map (t s) (AlgHom.id (F.obj i₀) B₀)
        (Algebra.TensorProduct.map (t r) (AlgHom.id (F.obj i₀) B₀) z)
    rw [ht_comp r s]
    exact DFunLike.congr_fun
      (Algebra.TensorProduct.map_comp (t s) (t r)
        (AlgHom.id (F.obj i₀) B₀) (AlgHom.id (F.obj i₀) B₀)) z
  let D : J ⥤ CommRingCat.{max v w x y} :=
    { obj := fun j ↦ CommRingCat.of (ULift.{max v w x y} (B j ⊗[P] Q))
      map := fun r ↦ CommRingCat.ofHom
        (Algebra.TensorProduct.map (β r) (AlgHom.id P Q)).toRingHom.ulift
      map_id := by
        intro j
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro z
        change ULift.up (Algebra.TensorProduct.map (β (𝟙 j)) (AlgHom.id P Q) z.down) = z
        rw [hβ_id, Algebra.TensorProduct.map_id]
        rfl
      map_comp := by
        intro j k l r s
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro z
        change ULift.up (Algebra.TensorProduct.map (β (r ≫ s)) (AlgHom.id P Q) z.down) =
          ULift.up (Algebra.TensorProduct.map (β s) (AlgHom.id P Q)
            (Algebra.TensorProduct.map (β r) (AlgHom.id P Q) z.down))
        rw [hβ_comp r s]
        exact congrArg ULift.up (DFunLike.congr_fun
          (Algebra.TensorProduct.map_comp (β s) (β r) (AlgHom.id P Q) (AlgHom.id P Q))
          z.down) }
  let E : J ⥤ CommRingCat.{max v w x y} :=
    { obj := fun j ↦ CommRingCat.of (ULift.{max v w x y} (C j))
      map := fun r ↦ CommRingCat.ofHom (e r).toRingHom.ulift
      map_id := by
        intro j
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro z
        change ULift.up (Algebra.TensorProduct.map (t (𝟙 j))
          (AlgHom.id (F.obj i₀) C₀) z.down) = z
        rw [ht_id, Algebra.TensorProduct.map_id]
        rfl
      map_comp := by
        intro j k l r s
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro z
        change ULift.up (Algebra.TensorProduct.map (t (r ≫ s))
          (AlgHom.id (F.obj i₀) C₀) z.down) =
          ULift.up (Algebra.TensorProduct.map (t s) (AlgHom.id (F.obj i₀) C₀)
            (Algebra.TensorProduct.map (t r) (AlgHom.id (F.obj i₀) C₀) z.down))
        rw [ht_comp r s]
        exact congrArg ULift.up (DFunLike.congr_fun
          (Algebra.TensorProduct.map_comp (t s) (t r) (AlgHom.id (F.obj i₀) C₀)
            (AlgHom.id (F.obj i₀) C₀)) z.down) }
  refine ⟨aPs, D, E, fun _ ↦ ULift.ringEquiv, fun _ ↦ ULift.ringEquiv, βs, ?_, ?_, ?_⟩
  · intro j
    rfl
  · intro j k r
    exact ⟨β r, rfl, rfl⟩
  · intro j k r
    rfl

end RingHom
