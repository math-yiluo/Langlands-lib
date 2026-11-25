/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberSystem
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Localization of the closed-fibre ring transitions

Source: Stacks Project, Algebra, Tag 00R7, proof by Noetherian approximation.
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- Localization survives passage to the stage closed fibres.

Source: Stacks Project, Algebra, Tag 00R7, the quotient systems before the second use
of Tag 00R6.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-localization)

Proof: For a transition i to j, let g : T_i tensor over S_i with S_j to T_j
and U be the localization supplied by X.fibreTransition. The commuting quotient
square defines a ring homomorphism q : B_i tensor over A_i with A_j to B_j,
with q(b tensor a) = image(b) * phi_j(a), by the tensor universal property.
The three quotient maps give P : T_i tensor over S_i with S_j to
B_i tensor over A_i with A_j. It is surjective: lift both factors of a pure
tensor to quotient representatives, then use additive induction on tensors.
The square consisting of g, P, q and the quotient map T_j to B_j commutes,
as checked on pure tensors and then by additive induction.

The image in the source of the extended maximal ideal of S_j lies in ker(P),
since its image in A_j is zero. Its image under g is the extended maximal
ideal in T_j, by the formula g(1 tensor a) = algebraMap(S_j,T_j)(a) and
transitivity of extension of ideals. Hence ker(T_j to B_j) is contained in
the extension of ker(P) along g. Apply IsLocalization.of_surjective to this
square, its two surjective quotient maps and that kernel inclusion. It gives
IsLocalization (U.map P) B_j with precisely the constructed q as algebra map.
The argument uses no flatness and also applies to identity transitions.
-/
theorem NoetherianLocalModelTower.fiber_localization
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    let A := X.fiberA
    let B := X.fiberB
    let φ : ∀ i, A.obj i →+* B.obj i := X.fiberφ
    (∀ (i j : X.ι) (f : i ⟶ j),
      letI := (φ i).toAlgebra
      letI := (A.map f).hom.toAlgebra
      ∃ (q : B.obj i ⊗[A.obj i] A.obj j →+* B.obj j)
        (U : Submonoid (B.obj i ⊗[A.obj i] A.obj j)),
        (∀ (b : B.obj i) (a : A.obj j),
          q (b ⊗ₜ[A.obj i] a) = (B.map f).hom b * φ j a) ∧
        (letI := q.toAlgebra; IsLocalization U (B.obj j))) := by
  let := X.preorder
  let := X.commR
  let := X.commS
  let := X.commT
  let := X.localR
  let := X.algRS
  let := X.algST
  let := X.algRT
  let := X.towerRST
  dsimp only
  intro i j f
  let := (X.fiberφ i).toAlgebra
  let := (X.fiberSMap i j (leOfHom f)).toAlgebra
  let := (X.fiberφ j).toAlgebra
  let : Algebra (X.FiberS i) (X.FiberT j) :=
    ((X.fiberφ j).comp (X.fiberSMap i j (leOfHom f))).toAlgebra
  let : IsScalarTower (X.FiberS i) (X.FiberS j) (X.FiberT j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let f₁ : X.FiberT i →ₐ[X.FiberS i] X.FiberT j := {
    __ := X.fiberTMap i j (leOfHom f)
    commutes' := fun a ↦ RingHom.congr_fun (X.fiber_square i j f) a }
  let f₂ : X.FiberS j →ₐ[X.FiberS i] X.FiberT j := {
    __ := X.fiberφ j
    commutes' := fun _ ↦ rfl }
  let q := (Algebra.TensorProduct.lift f₁ f₂ (fun _ _ ↦ .all _ _)).toRingHom
  let : Algebra (X.S₀ i) (X.S₀ j) := (X.smap i j (leOfHom f)).toAlgebra
  let P := Algebra.TensorProduct.mapRingHom
    (Ideal.Quotient.mk (X.fiberIdealS i))
    (Ideal.Quotient.mk (X.fiberIdealT i))
    (Ideal.Quotient.mk (X.fiberIdealS j)) (by ext; rfl) (by ext; rfl)
  have hP : Function.Surjective P := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add P x y⟩
    | tmul b a =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨b ⊗ₜ a, Algebra.TensorProduct.mapRingHom_tmul ..⟩
  obtain ⟨g, U, hg, hloc⟩ := X.fibreTransition i j (leOfHom f)
  have hsq : (Ideal.Quotient.mk (X.fiberIdealT j)).comp g = q.comp P := by
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply]
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul b a => simp [P, q, hg, f₁, f₂, NoetherianLocalModelTower.fiberTMap,
        NoetherianLocalModelTower.fiberφ]
  have hg_right : g.comp
      (Algebra.TensorProduct.includeRight (R := X.S₀ i) (A := X.T₀ i)).toRingHom =
        algebraMap (X.S₀ j) (X.T₀ j) := by
    ext a
    simpa using hg 1 a
  have hker : (X.fiberIdealS j).map
      (Algebra.TensorProduct.includeRight (R := X.S₀ i) (A := X.T₀ i)).toRingHom ≤
        RingHom.ker P := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp [RingHom.mem_ker, P, Algebra.TensorProduct.includeRight,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  have hIdeal : X.fiberIdealT j = (X.fiberIdealS j).map
      (algebraMap (X.S₀ j) (X.T₀ j)) := by
    rw [NoetherianLocalModelTower.fiberIdealT, NoetherianLocalModelTower.fiberIdealS,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let : Algebra (X.T₀ i ⊗[X.S₀ i] X.S₀ j) (X.T₀ j) := g.toAlgebra
  let : IsLocalization U (X.T₀ j) := hloc
  refine ⟨q, U.map P, ?_, ?_⟩
  · intro b a
    exact Algebra.TensorProduct.lift_tmul f₁ f₂ _ b a
  · let := q.toAlgebra
    apply IsLocalization.of_surjective U (X.T₀ j) P hP
      (Ideal.Quotient.mk (X.fiberIdealT j)) Ideal.Quotient.mk_surjective hsq
    rw [Ideal.mk_ker, hIdeal, ← hg_right, ← Ideal.map_map]
    exact Ideal.map_mono hker

end Module
