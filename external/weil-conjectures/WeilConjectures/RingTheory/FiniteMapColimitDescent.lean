/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.RingTheory.IntegralElementsColimitDescent

/-!
# Descent of finiteness of an algebra map along a directed ring colimit

Source: Stacks Project, Algebra, Lemma 10.168.3 (Tag 07RG)
(blueprint: lem-weil-pbc-colimit-finite-ring-map).
-/

@[expose] public section

universe u v t

open CategoryTheory CategoryTheory.Limits

namespace RingHom


private theorem adjoin_tensor_generators
    {R T B C : Type*} [CommRing R] [CommRing T] [CommRing B] [CommRing C]
    [Algebra R T] [Algebra R B] [Algebra R C] (φ : B →ₐ[R] C)
    (s : Finset C)
    (hs : letI := φ.toRingHom.toAlgebra; Algebra.adjoin B (s : Set C) = ⊤) :
    let ψ := Algebra.TensorProduct.map (AlgHom.id R T) φ
    letI := ψ.toRingHom.toAlgebra
    Algebra.adjoin (TensorProduct R T B)
      ((fun c ↦ TensorProduct.tmul R (1 : T) c) '' (s : Set C)) = ⊤ := by
  let ψ := Algebra.TensorProduct.map (AlgHom.id R T) φ
  let := ψ.toRingHom.toAlgebra
  let D := Algebra.adjoin (TensorProduct R T B)
    ((fun c ↦ TensorProduct.tmul R (1 : T) c) '' (s : Set C))
  have hright (c : C) : TensorProduct.tmul R (1 : T) c ∈ D := by
    let := φ.toRingHom.toAlgebra
    have hc : c ∈ Algebra.adjoin B (s : Set C) := by rw [hs]; trivial
    induction hc using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap b =>
      exact D.algebraMap_mem (TensorProduct.tmul R (1 : T) b)
    | add x y hx hy ihx ihy =>
      simpa only [TensorProduct.tmul_add] using D.add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul] using D.mul_mem ihx ihy
  apply top_unique
  intro z _
  change z ∈ D
  induction z using TensorProduct.inductionOn with
  | tmul t c =>
    have ht : TensorProduct.tmul R t (1 : C) ∈ D := by
      have heq :
          algebraMap (TensorProduct R T B) (TensorProduct R T C)
            (TensorProduct.tmul R t (1 : B)) =
          TensorProduct.tmul R t (1 : C) := by
        change ψ (TensorProduct.tmul R t (1 : B)) = _
        simp only [ψ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      rw [← heq]
      exact D.algebraMap_mem _
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using
      D.mul_mem ht (hright c)
  | add x y ihx ihy => exact D.add_mem (ihx trivial) (ihy trivial)

/-- A finite type algebra map whose base change to a directed colimit is finite
is already finite after base change to some stage above the initial stage.
Source: Stacks Project, Algebra, Lemma 10.168.3 (Tag 07RG)
(blueprint: lem-weil-pbc-colimit-finite-ring-map).

Proof:
1. Choose finitely many generators of `C₀` over `B₀`. Their tensors with `1` generate
   every base change, and the tensor-product transition maps commute with the algebra maps.
2. Finiteness at the colimit implies integrality of these generators
   (`lem-weil-pbc-finite-algebra-is-integral`), giving monic annihilating polynomials.
3. Lift their finitely many coefficients to a common stage by
   `lem-weil-pbc-directed-colimit-base-change-elementwise`, part (1), and directedness.
4. Their evaluations vanish at the colimit, so part (2) of the same lemma makes them
   vanish at a common later stage. Thus all the base-changed generators are integral there.
5. Apply `lem-weil-pbc-finite-of-integral-generators`: a finite type algebra generated
   by integral elements is finite as a module. -/
theorem exists_finite_tensorProductMap_of_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ : Type v) (C₀ : Type t) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hft : φ₀.FiniteType) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra
    (Algebra.TensorProduct.map
      (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).Finite →
      ∃ (i : I) (h : i₀ ≤ i),
        letI : Algebra (F.obj i₀) (F.obj i) :=
          (CommRingCat.Hom.hom (F.map (homOfLE h))).toAlgebra
        (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).Finite := by
  classical
  let : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
    (CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra
  intro hfinite
  let : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  have hint : ∀ x ∈ s,
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).toRingHom.IsIntegralElem
          (TensorProduct.tmul (F.obj i₀) (1 : (colimit F : CommRingCat.{u})) x) := by
    intro x _
    exact hfinite.to_isIntegral _
  obtain ⟨i, h, hi⟩ := exists_integral_tensor_generators_of_colimit F i₀ B₀ C₀ φ₀ s hint
  refine ⟨i, h, ?_⟩
  let : Algebra (F.obj i₀) (F.obj i) :=
    (CommRingCat.Hom.hom (F.map (homOfLE h))).toAlgebra
  let ψ := Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀
  let := ψ.toRingHom.toAlgebra
  have hgen := adjoin_tensor_generators (T := F.obj i) φ₀ s hs
  have hm : Module.Finite (TensorProduct (F.obj i₀) (F.obj i) B₀)
      (Algebra.adjoin (TensorProduct (F.obj i₀) (F.obj i) B₀)
        ((fun c ↦ TensorProduct.tmul (F.obj i₀) (1 : F.obj i) c) '' (s : Set C₀))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image _) (by
      rintro _ ⟨x, hx, rfl⟩
      exact hi x hx)
  rw [hgen] at hm
  exact Module.Finite.of_surjective (Subalgebra.topEquiv.toLinearMap) (by
    exact Subalgebra.topEquiv.surjective)

end RingHom
