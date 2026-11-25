/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

namespace Module

-- Invert the selected rows, then describe the cokernel by the remaining coordinates.
private theorem split_of_unit_minor
    {S M N : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] {m n : ℕ}
    (bm : Basis (Fin m) S M) (bn : Basis (Fin n) S N) (u : M →ₗ[S] N)
    (r : Fin m ↪ Fin n)
    (h : IsUnit ((LinearMap.toMatrix bm bn u).submatrix r id).det) :
    ∃ v : N →ₗ[S] M, v.comp u = LinearMap.id ∧
      Module.Finite S (N ⧸ LinearMap.range u) ∧
      Module.Free S (N ⧸ LinearMap.range u) := by
  classical
  let B := (LinearMap.toMatrix bm bn u).submatrix r id
  let t : N →ₗ[S] (Fin m → S) := (LinearMap.funLeft S S r).comp bn.equivFun.toLinearMap
  let v : N →ₗ[S] M := bm.equivFun.symm.toLinearMap.comp (B⁻¹.mulVecLin.comp t)
  have htu (x : M) : t (u x) = B.mulVec (bm.equivFun x) := by
    funext i
    exact (congrFun (u.toMatrix_mulVec_repr bm bn x) (r i)).symm
  have hv (x : M) : v (u x) = x := by
    change bm.equivFun.symm (B⁻¹.mulVec (t (u x))) = x
    rw [htu, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B h, Matrix.one_mulVec]
    exact bm.equivFun.symm_apply_apply x
  have htv (y : N) : t (u (v y)) = t y := by
    rw [htu]
    change B.mulVec (bm.equivFun (bm.equivFun.symm (B⁻¹.mulVec (t y)))) = t y
    rw [bm.equivFun.apply_symm_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv B h, Matrix.one_mulVec]
  -- The projection y ↦ y - u(v(y)) vanishes precisely on the image of u.
  let C := {j : Fin n // j ∉ Set.range r}
  let q : N →ₗ[S] (C → S) := (LinearMap.funLeft S S (fun j : C ↦ j.1)).comp
    (bn.equivFun.toLinearMap.comp (LinearMap.id - u.comp v))
  have hq (y : N) (j : C) : q y j = bn.equivFun y j - bn.equivFun (u (v y)) j := by
    simp [q]
  have hqu (x : M) : q (u x) = 0 := by
    ext j
    rw [hq, hv, sub_self]
    rfl
  have hker : LinearMap.range u = LinearMap.ker q := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hqu x
    · intro hy
      refine ⟨v y, bn.equivFun.injective ?_⟩
      funext j
      by_cases hj : j ∈ Set.range r
      · obtain ⟨i, rfl⟩ := hj
        exact congrFun (htv y) i
      · have hz := congrFun hy (⟨j, hj⟩ : C)
        rw [hq] at hz
        exact (sub_eq_zero.mp hz).symm
  have hsurj : Function.Surjective q := by
    intro z
    let a : Fin n → S := fun j ↦ if hj : j ∈ Set.range r then 0 else z ⟨j, hj⟩
    let y := bn.equivFun.symm a
    have hty : t y = 0 := by
      ext i
      change bn.equivFun (bn.equivFun.symm a) (r i) = 0
      rw [bn.equivFun.apply_symm_apply]
      exact dite_eq_left (Set.mem_range_self i)
    have hvy : v y = 0 := by
      change bm.equivFun.symm (B⁻¹.mulVec (t y)) = 0
      rw [hty, Matrix.mulVec_zero, map_zero]
    refine ⟨y, ?_⟩
    ext j
    rw [hq, hvy, map_zero, map_zero]
    change bn.equivFun (bn.equivFun.symm a) j - 0 = z j
    rw [bn.equivFun.apply_symm_apply, sub_zero]
    exact dite_eq_right j.2
  let e := (Submodule.quotEquivOfEq _ _ hker).trans (q.quotKerEquivOfSurjective hsurj)
  have : Module.Finite S (C → S) := inferInstance
  have : Module.Free S (C → S) := inferInstance
  exact ⟨v, LinearMap.ext hv, Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
    Module.Free.of_equiv e.symm⟩

-- The row space has full dimension, so a basis of rows gives a nonzero maximal minor.
private theorem exists_nonzero_minor
    {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {m n : ℕ}
    (bm : Basis (Fin m) K M) (bn : Basis (Fin n) K N) (u : M →ₗ[K] N)
    (hu : Function.Injective u) :
    ∃ r : Fin m ↪ Fin n, ((LinearMap.toMatrix bm bn u).submatrix r id).det ≠ 0 := by
  classical
  let A := LinearMap.toMatrix bm bn u
  have : Module.Finite K M := Module.Finite.of_basis bm
  have : Module.Finite K N := Module.Finite.of_basis bn
  have hspan : Submodule.span K (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← A.rank_eq_finrank_span_row, A.rank_eq_finrank_range_toLin bn bm]
    rw [Matrix.toLin_toMatrix, LinearMap.finrank_range_of_inj hu]
    rw [Module.finrank_eq_card_basis bm, Module.finrank_pi, Fintype.card_fin]
  let b := Basis.ofSpan hspan.ge
  let := FiniteDimensional.fintypeBasisIndex b
  have hcard := (Module.finrank_eq_card_basis b).symm
  simp only [Module.finrank_pi, Fintype.card_fin] at hcard
  let e := Fintype.equivFinOfCardEq hcard
  let c := b.reindex e
  have hc (i : Fin m) : c i ∈ Set.range A.row := by
    apply Basis.ofSpan_subset hspan.ge
    exact ⟨e.symm i, by simp [c, b]⟩
  choose r hr using hc
  have hinj : Function.Injective r := by
    intro i j hij
    apply c.injective
    rw [← hr i, ← hr j, hij]
  refine ⟨⟨r, hinj⟩, ?_⟩
  have hrows : (A.submatrix r id).row = c := by
    funext i
    exact hr i
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp (hrows.symm ▸ c.linearIndependent)) |>.ne_zero

/-- A matrix minor argument gives a split localized map and a free cokernel, while an
isomorphism on the residue field gives an explicit inverse after localization. The proof is
Stacks Project, Algebra, Tag 00O0, parts (1) and (3): choose a nonvanishing maximal minor,
localize at its determinant, and use elementary row and column operations; in the square case
use the adjugate matrix. (blueprint: lem-pc-finite-free-map-residue-localization-strong) -/
theorem finiteFreeMap_residue_localization_strong
    {R : Type*} [CommRing R] (m n : ℕ)
    (u : (Fin m → R) →ₗ[R] (Fin n → R)) (p : Ideal R) [p.IsPrime] :
    (Function.Injective (u.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        (∃ v : TensorProduct R (Localization.Away f) (Fin n → R) →ₗ[Localization.Away f]
            TensorProduct R (Localization.Away f) (Fin m → R),
          v.comp (u.baseChange (Localization.Away f)) = LinearMap.id ∧
          Module.Finite (Localization.Away f)
            (TensorProduct R (Localization.Away f) (Fin n → R) ⧸
              LinearMap.range (u.baseChange (Localization.Away f))) ∧
          Module.Free (Localization.Away f)
            (TensorProduct R (Localization.Away f) (Fin n → R) ⧸
              LinearMap.range (u.baseChange (Localization.Away f))))) ∧
    (Function.Bijective (u.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        ∃ v : TensorProduct R (Localization.Away f) (Fin n → R) →ₗ[Localization.Away f]
            TensorProduct R (Localization.Away f) (Fin m → R),
          v.comp (u.baseChange (Localization.Away f)) = LinearMap.id ∧
          (u.baseChange (Localization.Away f)).comp v = LinearMap.id) := by
  classical
  have hinj (hu : Function.Injective (u.baseChange p.ResidueField)) :
      ∃ f : R, f ∉ p ∧
        ∃ v : TensorProduct R (Localization.Away f) (Fin n → R) →ₗ[Localization.Away f]
            TensorProduct R (Localization.Away f) (Fin m → R),
          v.comp (u.baseChange (Localization.Away f)) = LinearMap.id ∧
          Module.Finite (Localization.Away f)
            (TensorProduct R (Localization.Away f) (Fin n → R) ⧸
              LinearMap.range (u.baseChange (Localization.Away f))) ∧
          Module.Free (Localization.Away f)
            (TensorProduct R (Localization.Away f) (Fin n → R) ⧸
              LinearMap.range (u.baseChange (Localization.Away f))) := by
    let bm := Pi.basisFun R (Fin m)
    let bn := Pi.basisFun R (Fin n)
    obtain ⟨r, hr⟩ := exists_nonzero_minor (Algebra.TensorProduct.basis p.ResidueField bm)
      (Algebra.TensorProduct.basis p.ResidueField bn) (u.baseChange p.ResidueField) hu
    let f := ((LinearMap.toMatrix bm bn u).submatrix r id).det
    have hdet (S : Type _) [CommRing S] [Algebra R S] :
        ((LinearMap.toMatrix (Algebra.TensorProduct.basis S bm) (Algebra.TensorProduct.basis S bn)
          (u.baseChange S)).submatrix r id).det = algebraMap R S f := by
      rw [LinearMap.toMatrix_baseChange]
      exact ((algebraMap R S).map_det ((LinearMap.toMatrix bm bn u).submatrix r id)).symm
    have hf : f ∉ p := by
      intro hf
      apply hr
      rw [hdet]
      exact Ideal.algebraMap_residueField_eq_zero.mpr hf
    refine ⟨f, hf, ?_⟩
    apply split_of_unit_minor (Algebra.TensorProduct.basis (Localization.Away f) bm)
      (Algebra.TensorProduct.basis (Localization.Away f) bn) (u.baseChange (Localization.Away f)) r
    rw [hdet]
    exact IsLocalization.Away.algebraMap_isUnit f
  refine ⟨hinj, ?_⟩
  intro hu
  have hmn := (LinearEquiv.ofBijective (u.baseChange p.ResidueField) hu).finrank_eq
  rw [Module.finrank_eq_card_basis ((Pi.basisFun R (Fin m)).baseChange p.ResidueField),
    Module.finrank_eq_card_basis ((Pi.basisFun R (Fin n)).baseChange p.ResidueField)] at hmn
  simp only [Fintype.card_fin] at hmn
  subst n
  obtain ⟨f, hf, v, hv, _, _⟩ := hinj hu.1
  have : Module.Finite (Localization.Away f)
      (TensorProduct R (Localization.Away f) (Fin m → R)) :=
    Module.Finite.of_basis
      (Algebra.TensorProduct.basis (Localization.Away f) (Pi.basisFun R (Fin m)))
  exact ⟨f, hf, v, hv, (LinearMap.comp_eq_id_comm _ _).mp hv⟩

end Module
