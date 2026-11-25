/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.LinearAlgebra.Matrix.LeftInverseMinors
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Splitting the localized conormal differential of a strictly standard presentation

Source: Stacks Project, Smoothing Ring Maps, Lemmas 07CA and 07ET.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra.Presentation

/-- The two strictly standard conditions split the localized conormal differential.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07CA, first paragraph,
using the matrix identity of Lemma Tag 07ET.
(blueprint: lem-weil-pbc-strictly-standard-localized-conormal-split).

Proof: let E be the map from A^c to I/I² sending each basis vector to the class of the
corresponding initial relation, and D the conormal differential. In the polynomial
cotangent-space basis, D E has the evaluated Jacobian matrix M. The displayed minor
combination and the adjugate identity give a matrix B with B M = a times the identity;
transposing the row convention of the displayed determinants does not change them.
After scalar extension to A_a, a is a unit, so a⁻¹ B is a left inverse of D E.
The relation condition says that a times every remaining relation class lies in the
span of the initial classes, since I² vanishes in I/I². Thus E becomes surjective after
localization: all relation classes generate I/I² and the remaining ones are now in
its image. Surjectivity alone now suffices: if g D E = id, then E g D E = E.
Evaluating this equality on a preimage under E gives E g D = id. Thus E g is
the required left inverse of D, with g represented by a⁻¹ B.
For c = 0 the relation condition makes the localized conormal module zero, so its
unique map back is a left inverse. The same argument covers the zero localization. -/
theorem strictlyStandard_localized_conormal_split
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m c : ℕ} (P : Presentation R A (Fin n) (Fin m))
    (hc : c ≤ min n m) (a : A)
    (a' : {s : Finset (Fin n) // s.card = c} → A)
    (hminor : a = ∑ s : {s : Finset (Fin n) // s.card = c}, a' s *
      Matrix.det (fun j i : Fin c =>
        MvPolynomial.aeval P.val (MvPolynomial.pderiv (s.val.orderEmbOfFin s.property i)
          (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j)))))
    (hrelations : ∀ j : Fin m, c ≤ j.val →
      P.σ a * P.relation j ∈
        Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} +
          (Ideal.span (Set.range P.relation)) ^ 2) :
    ∃ l : (Localization.Away a ⊗[A] P.toExtension.CotangentSpace) →ₗ[Localization.Away a]
        (Localization.Away a ⊗[A] P.toExtension.Cotangent),
      l.comp (P.toExtension.cotangentComplex.baseChange (Localization.Away a)) =
        LinearMap.id := by
  classical
  let S := Localization.Away a
  let C := P.toExtension.Cotangent
  let f : Fin m → C := fun j ↦
    Extension.Cotangent.mk (P := P.toExtension) ⟨P.relation j, P.relation_mem_ker j⟩
  let t : Fin c → S ⊗[A] C := fun j ↦
    1 ⊗ₜ[A] f (Fin.castLE (le_trans hc (min_le_right n m)) j)
  let b := Pi.basisFun S (Fin c)
  let w := P.toGenerators.cotangentSpaceBasis.baseChange S
  let E := b.constr S t
  let d := P.toExtension.cotangentComplex.baseChange S
  -- The relation condition generates the localized conormal module.
  have hE : Function.Surjective E := by
    set_option backward.isDefEq.respectTransparency false in
      let N := LinearMap.range E
      let F : C →ₗ[A] S ⊗[A] C := TensorProduct.mk A S C 1
      let K : Ideal P.toExtension.Ring :=
        Ideal.span {g | ∃ k : Fin m, k.val < c ∧ g = P.relation k}
      have hK : K ≤ P.toExtension.ker := by
        apply Ideal.span_le.mpr
        rintro g ⟨k, _, rfl⟩
        exact P.relation_mem_ker k
      have hKmem (g : P.toExtension.Ring) (hg : g ∈ K) :
          F (Extension.Cotangent.mk (P := P.toExtension) ⟨g, hK hg⟩) ∈ N := by
        induction hg using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨k, hk, rfl⟩ := hz
          let j : Fin c := ⟨k.val, hk⟩
          have hj : Fin.castLE (le_trans hc (min_le_right n m)) j = k := Fin.ext rfl
          refine ⟨b j, ?_⟩
          simp only [E, Module.Basis.constr_basis, t, hj]
          rfl
        | zero =>
          change F (Extension.Cotangent.mk (P := P.toExtension) 0) ∈ N
          simp only [map_zero]
          exact N.zero_mem
        | add z z' hz hz' ih ih' =>
          have hm := N.add_mem ih ih'
          rw [← map_add, ← map_add] at hm
          exact hm
        | smul r z hz ih =>
          have hm := N.smul_mem (algebraMap A S (algebraMap P.toExtension.Ring A r)) ih
          rw [algebraMap_smul, ← map_smul, algebraMap_smul, ← map_smul] at hm
          exact hm
      have hf (j : Fin m) : F (f j) ∈ N := by
        by_cases hj : j.val < c
        · let k : Fin c := ⟨j.val, hj⟩
          have hk : Fin.castLE (le_trans hc (min_le_right n m)) k = j := Fin.ext rfl
          refine ⟨b k, ?_⟩
          simp only [E, Module.Basis.constr_basis, t, hk]
          rfl
        · have hrel := hrelations j (Nat.le_of_not_gt hj)
          rw [P.span_range_relation_eq_ker] at hrel
          obtain ⟨g, hg, q, hq, heq⟩ := Submodule.mem_sup.mp hrel
          have hclass : Extension.Cotangent.mk (P := P.toExtension)
              (P.σ a • (⟨P.relation j, P.relation_mem_ker j⟩ : P.toExtension.ker)) =
              Extension.Cotangent.mk (P := P.toExtension) ⟨g, hK hg⟩ := by
            apply (Extension.Cotangent.mk_eq_mk_iff_sub_mem _ _).mpr
            change P.σ a * P.relation j - g ∈ P.toExtension.ker ^ 2
            rw [← heq]
            simpa using hq
          have hmul : algebraMap A S a • F (f j) ∈ N := by
            have hm := hKmem g hg
            rw [← hclass, map_smul, ← algebraMap_smul A] at hm
            erw [P.toExtension.algebraMap_σ] at hm
            rw [map_smul, ← algebraMap_smul S] at hm
            exact hm
          obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (S := S) a
          have hm := N.smul_mem (↑v⁻¹ : S) hmul
          simpa only [← hv, smul_smul, Units.inv_mul, one_smul] using hm
      have hspan : Submodule.span A (Set.range f) = ⊤ :=
        Extension.Cotangent.span_eq_top_of_span_eq_ker (P := P.toExtension) P.relation
          P.span_range_relation_eq_ker
      have hx (x : C) : F x ∈ N := by
        have hm : x ∈ Submodule.span A (Set.range f) := by rw [hspan]; trivial
        induction hm using Submodule.span_induction with
        | mem z hz => obtain ⟨j, rfl⟩ := hz; exact hf j
        | zero => simpa only [map_zero] using N.zero_mem
        | add z z' _ _ ih ih' => simpa only [map_add] using N.add_mem ih ih'
        | smul r z _ ih =>
          rw [map_smul, ← algebraMap_smul S]
          exact N.smul_mem _ ih
      apply LinearMap.range_eq_top.mp
      apply top_unique
      intro x _
      induction x using TensorProduct.inductionOn with
      | tmul s x =>
        have hm := N.smul_mem s (hx x)
        simpa only [F, TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul,
          mul_one] using hm
      | add x y hx hy => exact N.add_mem (hx trivial) (hy trivial)
  -- The minor condition supplies a scalar left inverse of the Jacobian matrix.
  let M : Matrix (Fin n) (Fin c) A := fun i j ↦
    MvPolynomial.aeval P.val (MvPolynomial.pderiv i
      (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j)))
  let J : Ideal A := Ideal.span (Set.range
    (fun s : {s : Finset (Fin n) // s.card = c} ↦
      (M.submatrix (s.val.orderEmbOfFin s.property) _root_.id).det))
  have ha : a ∈ J := by
    rw [hminor]
    apply Submodule.sum_mem
    intro s _
    apply Ideal.mul_mem_left
    have hdet : Matrix.det (fun j i : Fin c ↦
        MvPolynomial.aeval P.val (MvPolynomial.pderiv (s.val.orderEmbOfFin s.property i)
          (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j)))) =
        (M.submatrix (s.val.orderEmbOfFin s.property) _root_.id).det := by
      exact Matrix.det_transpose _
    rw [hdet]
    exact Ideal.subset_span ⟨s, rfl⟩
  obtain ⟨B, hB⟩ := (Matrix.scalar_left_inverse_maximal_minors n c
    (le_trans hc (min_le_left n m)) M).1 a ha
  have hM : LinearMap.toMatrix b w (d.comp E) = M.map (algebraMap A S) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.comp_apply, Module.Basis.constr_basis]
    change w.repr (d (1 ⊗ₜ[A] f (Fin.castLE
      (le_trans hc (min_le_right n m)) j))) i = _
    rw [LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul,
      Extension.cotangentComplex_mk]
    erw [Generators.cotangentSpaceBasis_repr_tmul]
    simp [M, Algebra.smul_def]
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := S) a
  let L : Matrix (Fin c) (Fin n) S :=
    (↑u⁻¹ : S) • B.map (algebraMap A S)
  have hL : L * M.map (algebraMap A S) = 1 := by
    have hmap := congrArg (fun N : Matrix (Fin c) (Fin c) A ↦
      N.map (algebraMap A S)) hB
    rw [Matrix.map_mul] at hmap
    have hscalar : (a • (1 : Matrix (Fin c) (Fin c) A)).map (algebraMap A S) =
        algebraMap A S a • 1 := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [hscalar] at hmap
    dsimp [L]
    rw [Matrix.smul_mul, hmap, smul_smul, ← hu, Units.inv_mul, one_smul]
  let g := Matrix.toLin w b L
  have hg : g.comp (d.comp E) = LinearMap.id := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b w b, hM, LinearMap.toMatrix_toLin,
      LinearMap.toMatrix_id]
    exact hL
  -- Check the left inverse on preimages under the surjective generator map.
  refine ⟨E.comp g, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hE x
  have hy := LinearMap.congr_fun hg y
  change E (g (d (E y))) = E y
  exact congrArg E hy

end Algebra.Presentation
