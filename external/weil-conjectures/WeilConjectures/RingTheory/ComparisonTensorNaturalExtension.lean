/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder


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
(blueprint: lem-weil-pbc-comparison-tensor-natural-extension-j3)

Proof: Let q_i:Q→C_i be ψ composed with the right tensor inclusion, and
q_j the canonical C_i→C_j transition composed with q_i. Give C_j the
P-action through φ_j composed with P→B_j. The equality hψ and the tensor
balancing relation identify q_i(algebraMap(p)) with φ_i(algebraMap(p)).
The P-linearity of βs_j and the tensor identity e_ij φ_i=φ_j βs_j then
show q_j is a P-algebra map. Define χ_j as the actual tensor product map
of the P-algebra maps φ_j:B_j→C_j and q_j:Q→C_j. Thus χ_j(b⊗q)=φ_j(b)q_j(q).
Canonical tensor transitions commute with φ, and q_j is compatible with
transitions by functoriality. Induction on tensors proves χ is compatible
with the prescribed D and E transitions. Conjugating by d_j and c_j
therefore defines a natural transformation. Its left inclusion identity
follows by setting q=1; its Q-coordinate identity follows by setting b=1.
The construction uses no injectivity, flatness, or nonzero-ring assumption.
-/
theorem exists_comparison_tensor_natural_extension
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
      ∀ (aPs : ∀ j : J,
          letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
          Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀)),
        ∀ (D E : J ⥤ CommRingCat.{max v w x y}),
          ∀ (d : ∀ j : J,
              letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
              letI := aPs j
              ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q),
            ∀ (c : ∀ j : J,
                letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀)),
                  ∀ (βs : ∀ j : J,
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
                      (Algebra.TensorProduct.map αij (AlgHom.id (F.obj i₀) B₀)).toRingHom) →
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
                          (d j).toRingHom) →
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
                        (c j).toRingHom) →
                  ∃ (α : D ⟶ E),
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
  classical
  dsimp only
  intro aPs D E d c βs hβs hDt hEt
  let J := {j : I // i ≤ j}
  let : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
  let := aPi
  let (j : J) : Algebra (F.obj i₀) (F.obj j.val) :=
    (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
  let B (j : J) := ↥(F.obj j.val) ⊗[F.obj i₀] B₀
  let C (j : J) := ↥(F.obj j.val) ⊗[F.obj i₀] C₀
  let (j : J) : Algebra P (B j) := aPs j
  let t₀ (j : J) : F.obj i →ₐ[F.obj i₀] F.obj j.val :=
    { (F.map (homOfLE j.property)).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f s)
        (F.map_comp (homOfLE hi) (homOfLE j.property)).symm }
  let t {j k : J} (r : j ⟶ k) : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
    { (F.map (homOfLE (leOfHom r))).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
        (F.map_comp (homOfLE (hi.trans j.property)) (homOfLE (leOfHom r))).symm }
  let φ (j : J) : B j →+* C j :=
    (Algebra.TensorProduct.map (Algebra.ofId (F.obj j.val) (F.obj j.val)) φ₀).toRingHom
  let φi : (↥(F.obj i) ⊗[F.obj i₀] B₀) →+* (↥(F.obj i) ⊗[F.obj i₀] C₀) :=
    (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom
  let e₀ (j : J) := Algebra.TensorProduct.map (t₀ j) (AlgHom.id (F.obj i₀) C₀)
  let e {j k : J} (r : j ⟶ k) :=
    Algebra.TensorProduct.map (t r) (AlgHom.id (F.obj i₀) C₀)
  have hφ₀ (j : J) (z : ↥(F.obj i) ⊗[F.obj i₀] B₀) :
      e₀ j (φi z) = φ j (βs j z) := by
    have hb := DFunLike.congr_fun (hβs j) z
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hb
    rw [hb]
    clear hb
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
    | tmul s b => rfl
  let q₀ : Q →+* (↥(F.obj i) ⊗[F.obj i₀] C₀) :=
    ψ.comp Algebra.TensorProduct.includeRight.toRingHom
  let q (j : J) : Q →+* C j := (e₀ j).toRingHom.comp q₀
  let (j : J) : Algebra P (C j) := ((φ j).comp (algebraMap P (B j))).toAlgebra
  have hq (j : J) (p : P) : q j (algebraMap P Q p) = algebraMap P (C j) p := by
    change e₀ j (ψ (1 ⊗ₜ[P] algebraMap P Q p)) = φ j (algebraMap P (B j) p)
    rw [← (βs j).commutes p, ← hφ₀]
    congr 1
    have h := DFunLike.congr_fun hψ
      (algebraMap P (↥(F.obj i) ⊗[F.obj i₀] B₀) p)
    change ψ ((algebraMap P (↥(F.obj i) ⊗[F.obj i₀] B₀) p) ⊗ₜ[P] 1) = _ at h
    change ψ (algebraMap P ((↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q) p) = _ at h
    rw [Algebra.TensorProduct.algebraMap_apply'] at h
    exact h
  let φP (j : J) : B j →ₐ[P] C j :=
    { φ j with commutes' := fun _ ↦ rfl }
  let qP (j : J) : Q →ₐ[P] C j := { q j with commutes' := hq j }
  let χ (j : J) : B j ⊗[P] Q →+* C j :=
    (Algebra.TensorProduct.productMap (φP j) (qP j)).toRingHom
  have hχ (j : J) (b : B j) (q' : Q) : χ j (b ⊗ₜ[P] q') = φ j b * q j q' := rfl
  have ht₀ {j k : J} (r : j ⟶ k) : (t r).comp (t₀ j) = t₀ k := by
    apply AlgHom.ext
    intro z
    exact congrArg (fun f : F.obj i ⟶ F.obj k.val ↦ f z)
      (F.map_comp (homOfLE j.property) (homOfLE (leOfHom r))).symm
  have hqtrans {j k : J} (r : j ⟶ k) (q' : Q) : e r (q j q') = q k q' := by
    change e r (e₀ j (q₀ q')) = e₀ k (q₀ q')
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ht₀ r]
    rfl
  have hφtrans {j k : J} (r : j ⟶ k) (β : B j →ₐ[P] B k)
      (hβ : β.toRingHom =
        (Algebra.TensorProduct.map (t r) (AlgHom.id (F.obj i₀) B₀)).toRingHom)
      (b : B j) : e r (φ j b) = φ k (β b) := by
    have hb := DFunLike.congr_fun hβ b
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hb
    rw [hb]
    clear hb
    induction b using TensorProduct.inductionOn with
    | add b b' hb hb' => simpa only [map_add] using congrArg₂ (· + ·) hb hb'
    | tmul s b => rfl
  have hχtrans {j k : J} (r : j ⟶ k) (β : B j →ₐ[P] B k)
      (hβ : β.toRingHom =
        (Algebra.TensorProduct.map (t r) (AlgHom.id (F.obj i₀) B₀)).toRingHom)
      (z : B j ⊗[P] Q) :
      e r (χ j z) = χ k (Algebra.TensorProduct.map β (AlgHom.id P Q) z) := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
    | tmul b q' =>
      rw [Algebra.TensorProduct.map_tmul, hχ, hχ, map_mul, hqtrans r q', hφtrans r β hβ]
      rfl
  let α : D ⟶ E :=
    { app := fun j ↦ CommRingCat.ofHom
        ((c j).symm.toRingHom.comp ((χ j).comp (d j).toRingHom))
      naturality := by
        intro j k r
        obtain ⟨β, hβ, hd⟩ := hDt r
        have he := hEt r
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro z
        apply (c k).injective
        have hd' := DFunLike.congr_fun hd z
        have he' := DFunLike.congr_fun he
          ((c j).symm (χ j (d j z)))
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          RingEquiv.apply_symm_apply] at hd' he'
        change c k ((c k).symm (χ k (d k (D.map r z)))) =
          c k (E.map r ((c j).symm (χ j (d j z))))
        rw [RingEquiv.apply_symm_apply, he', hd']
        exact (hχtrans r β hβ (d j z)).symm }
  refine ⟨α, ?_, ?_⟩
  · intro j
    apply RingHom.ext
    intro b
    change c j ((c j).symm (χ j (d j ((d j).symm (b ⊗ₜ[P] 1))))) = φ j b
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hχ, map_one, mul_one]
  · intro j q'
    change c j ((c j).symm (χ j (d j ((d j).symm (1 ⊗ₜ[P] q'))))) =
      e₀ j (ψ (1 ⊗ₜ[P] q'))
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hχ, map_one, one_mul]
    rfl

end RingHom
