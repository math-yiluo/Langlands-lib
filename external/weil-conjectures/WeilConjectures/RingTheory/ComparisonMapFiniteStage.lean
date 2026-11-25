/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.RingTheory.TensorAlgebraStructureFiniteStage
import WeilConjectures.RingTheory.TensorRightFactorFiniteStage

/-! # Finite-stage descent of a compatible tensor comparison

Source: Stacks Project, Algebra, Tags 02JO (3), 00QO and 00DD.
(blueprint: lem-weil-pbc-comparison-map-finite-stage)
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- Descend the two finite presentations to one compatible tensor comparison map.

Source: Stacks Project, Algebra, Tag 02JO (3), construction of Ψ; Tag 00QO,
finite-presentation factorization, and Tag 00DD, tensor colimits.
(blueprint: lem-weil-pbc-comparison-map-finite-stage)

Proof: restrict F to the directed upper tail of i₀. The elementwise base-change
lemma identifies the colimits of the B and C tensor diagrams with the corresponding
limit tensor rings: maps are defined on representatives, with well-definedness
from eventual equality; operations are verified at common upper bounds. Factor
the structure map P → B through a B stage using finite presentation over Z.
Transport that structure to the upper tail. Give the C stages their P-structure
by the base change of φ₀. The map Q → C obtained by composing the right tensor
inclusion with g respects P, by he. Since Q is finitely presented over P, factor
this P-algebra map through a C stage on this tail. Take that stage i, and let ψ
be the tensor product universal map of Bᵢ → Cᵢ and the descended Q → Cᵢ.
Its left restriction is the base change of φ₀. The canonical Bᵢ → B is P-linear
because the P-structure was descended. The two sides of the limit identity agree
on Bᵢ by he and on Q by factorization, hence agree by tensor extensionality.
No finite-presentation hypothesis on φ₀ is used. Zero rings and empty finite
presentations require no changes: there are still only finitely many relations.
-/
theorem exists_comparison_map_finite_stage
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    [Algebra.FinitePresentation ℤ P] [Algebra.FinitePresentation P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (g : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q →+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (he : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      g.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(colimit F) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom) :
    ∃ (i : I) (hi : i₀ ≤ i),
    letI := (colimit.ι F i₀).hom.toAlgebra
    letI := (F.map (homOfLE hi)).hom.toAlgebra
    let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
      { (colimit.ι F i).hom with
        commutes' := fun s ↦
          congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      ∃ (aPi : Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀)),
        letI := aPi
        letI := aP
        ∃ (μB : (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P]
            (↥(colimit F) ⊗[F.obj i₀] B₀)),
          μB.toRingHom =
            (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀)).toRingHom ∧
          ∃ (ψ : ((↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q) →+*
              (↥(F.obj i) ⊗[F.obj i₀] C₀)),
            ψ.comp (Algebra.TensorProduct.includeLeftRingHom (R := P)
                (A := ↥(F.obj i) ⊗[F.obj i₀] B₀) (B := Q)) =
              (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom ∧
            (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp ψ =
              g.comp (Algebra.TensorProduct.map μB (AlgHom.id P Q)).toRingHom
    := by
  let := (colimit.ι F i₀).hom.toAlgebra
  let := aP
  let f := g.comp (Algebra.TensorProduct.includeRight (R := P)
    (A := ↥(colimit F) ⊗[F.obj i₀] B₀) (B := Q)).toRingHom
  have hf : f.comp (algebraMap P Q) =
      (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom.comp
        (algebraMap P (↥(colimit F) ⊗[F.obj i₀] B₀)) := by
    apply RingHom.ext
    intro r
    change g (1 ⊗ₜ[P] algebraMap P Q r) =
      (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀)
        (algebraMap P (↥(colimit F) ⊗[F.obj i₀] B₀) r)
    trans g (algebraMap P (↥(colimit F) ⊗[F.obj i₀] B₀) r ⊗ₜ[P] 1)
    · congr 1
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul r).symm
    · exact RingHom.congr_fun he _
  obtain ⟨j, hj, aPj, μBj, hμBj⟩ :=
    exists_tensor_algebra_structure_finite_stage F i₀ B₀ P aP
  obtain ⟨i, hi, aPi, μB, hμB, q, hq, hqf⟩ :=
    exists_tensor_right_factor_finite_stage F i₀ B₀ C₀ φ₀ P Q aP
      j hj aPj μBj hμBj f hf
  let := (F.map (homOfLE hi)).hom.toAlgebra
  let := aPi
  let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
    { (colimit.ι F i).hom with
      commutes' := fun s ↦
        congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
  let φi := Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀
  let μC := Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)
  let := (φi.toRingHom.comp (algebraMap P (↥(F.obj i) ⊗[F.obj i₀] B₀))).toAlgebra
  let φiP : (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P]
      (↥(F.obj i) ⊗[F.obj i₀] C₀) :=
    { φi.toRingHom with commutes' := fun _ ↦ rfl }
  let qP : Q →ₐ[P] (↥(F.obj i) ⊗[F.obj i₀] C₀) :=
    { q with commutes' := fun r ↦ RingHom.congr_fun hq r }
  let ψ := (Algebra.TensorProduct.productMap φiP qP).toRingHom
  refine ⟨i, hi, aPi, μB, hμB, ψ, ?_, ?_⟩
  · apply RingHom.ext
    intro b
    exact Algebra.TensorProduct.productMap_left_apply φiP qP b
  · apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro b
      change μC (ψ (b ⊗ₜ[P] 1)) = g (μB b ⊗ₜ[P] 1)
      simp only [ψ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.productMap_left_apply]
      have hleft := RingHom.congr_fun he (μB b)
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply] at hleft
      rw [hleft]
      rw [show μB b = Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀) b from
        RingHom.congr_fun hμB b]
      clear hleft
      induction b using TensorProduct.inductionOn with
      | tmul a b => simp [μC, φiP, φi, Algebra.TensorProduct.map_tmul]
      | add b c hb hc => simpa only [map_add] using congrArg₂ (· + ·) hb hc
    · apply RingHom.ext
      intro r
      change μC (ψ (1 ⊗ₜ[P] r)) =
        g (Algebra.TensorProduct.map μB (AlgHom.id P Q) (1 ⊗ₜ[P] r))
      simp only [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      change μC (Algebra.TensorProduct.productMap φiP qP (1 ⊗ₜ[P] r)) =
        g (1 ⊗ₜ[P] r)
      rw [Algebra.TensorProduct.productMap_right_apply]
      exact RingHom.congr_fun hqf r

end RingHom
