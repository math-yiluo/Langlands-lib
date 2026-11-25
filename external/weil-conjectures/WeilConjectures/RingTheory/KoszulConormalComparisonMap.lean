/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
import WeilConjectures.RingTheory.KoszulConormalBasis
import Mathlib.LinearAlgebra.Determinant

/-!
# Construction of the normalized dual Koszul comparison

Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, local Koszul computation.
(blueprint: new-s3-koszul-conormal-comparison-map).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

private theorem conormal_coord
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I)
    (b : Module.Basis (Fin r) (A ⧸ I) I.Cotangent)
    (hb : ∀ i, b i = koszulConormalVector A I r f hf (Finsupp.single i 1))
    (v : Fin r →₀ A) (j : Fin r) :
    b.coord j (koszulConormalVector A I r f hf v) = Ideal.Quotient.mk I (v j) := by
  classical
  induction v using Finsupp.induction with
  | zero => simp
  | @single_add i a v hi ha ih =>
    rw [map_add, map_add, ih]
    have hs : koszulConormalVector A I r f hf (Finsupp.single i a) =
        a • b i := by
      rw [hb]
      simp [koszulConormalVector]
    rw [hs]
    by_cases hij : i = j <;> simp [Module.Basis.coord_apply, hij, Algebra.smul_def]

set_option backward.isDefEq.respectTransparency false in
private theorem top_functional_det
    (A : Type u) [CommRing A] (r : ℕ)
    (x : (⋀[A]^r (Fin r →₀ A)) →ₗ[A] A)
    (v : Fin r → (Fin r →₀ A)) :
    x (exteriorPower.ιMulti A r v) =
      x (exteriorPower.ιMulti A r (fun i ↦ Finsupp.single i 1)) *
        (Matrix.of fun i j ↦ v i j).det := by
  let e := Finsupp.basisSingleOne (R := A) (ι := Fin r)
  have h := (x.compAlternatingMap (exteriorPower.ιMulti A r)).eq_smul_basis_det e
  have hv := DFunLike.congr_fun h v
  have hm : e.toMatrix v = (Matrix.of fun i j ↦ v i j).transpose := rfl
  simp only [smul_apply, LinearMap.compAlternatingMap_apply,
    Module.Basis.det_apply, hm, Matrix.det_transpose, smul_eq_mul] at hv
  simpa [e] using hv

set_option backward.isDefEq.respectTransparency false in
private theorem boundary_top_mem
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (f : Fin (n + 1) → A)
    (hf : Ideal.span (Set.range f) = I)
    (x : (⋀[A]^n (Fin (n + 1) →₀ A)) →ₗ[A] A) :
    x (koszulBoundary A (n + 1) f n
      (exteriorPower.ιMulti A (n + 1) (fun i ↦ Finsupp.single i 1))) ∈ I := by
  classical
  let e : Fin (n + 1) → (Fin (n + 1) →₀ A) := fun i ↦ Finsupp.single i 1
  let l := Finsupp.linearCombination A f
  obtain ⟨D, hD1, hrec, huniq, hgen, hzero, hdeg, hform, hleib, hdu⟩ :=
    koszul_differential A (Fin (n + 1) →₀ A) l
  have hc : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin (n + 1) →₀ A))) l = D := by
    apply huniq
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro v y
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul
          (Q := (0 : QuadraticForm A (Fin (n + 1) →₀ A))) l v y
  have hd : koszulBoundary A (n + 1) f n (exteriorPower.ιMulti A (n + 1) e) =
      ∑ i : Fin (n + 1), (((-1 : A) ^ (i.val + 2)) * f i) •
        exteriorPower.ιMulti A n (e ∘ i.succAbove) := by
    apply Subtype.ext
    change CliffordAlgebra.contractLeft _ _ = _
    rw [hc]
    change D (ExteriorAlgebra.ιMulti A (n + 1) e) = _
    rw [hform]
    simp [l, e, Algebra.smul_def]
  rw [hd, map_sum]
  apply Ideal.sum_mem
  intro i hi
  rw [map_smul, smul_eq_mul]
  apply I.mul_mem_right
  apply I.mul_mem_left
  exact hf ▸ Ideal.subset_span (Set.mem_range_self i)

/-- A determinant-normalized comparison map exists.
Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, local computation;
Tag 062I, lemma-H1-regular-quasi-regular, first paragraph, for the conormal basis.
(blueprint: new-s3-koszul-conormal-comparison-map).

Proof: Set E = A^r and B = A/I. By `exists_koszul_conormal_basis`, the classes
c_i of the generators form a B-basis of I/I^2. Let c_i^* be its dual basis,
e_top the ordered wedge of the standard basis of E, and s = (-1)^(r*(r-1)/2).
Send a top-degree functional x to s times its value on e_top reduced modulo I,
times the ordered wedge of the c_i^*. This is A-linear, with the target A-action
restricted from B. Transport it along singleObjXSelf to the degree-r term of
the single complex, and put zero in all other degrees.

The only nontrivial chain-map equation is that the degree-(r-1) differential
is killed. The dual differential is signed precomposition with Koszul d_r;
d_r(e_top) is a signed sum of complementary basis wedges with coefficients f_i.
Thus its evaluation by any functional belongs to I and vanishes in B. The
outgoing differential of the target is zero. These equations give the map phi.

For v_1,...,v_r in E, their top wedge is det(v) times e_top. Their conormal
classes have the same coordinate matrix reduced to B. The determinant pairing
of the ordered dual conormal wedge with their wedge is therefore det(v) mod I.
Multiplying by s and x(e_top) mod I gives exactly IsKoszulConormalComparison.
For r = 0 the empty determinant is 1, I = 0, and this is the identity on A.
For I = A all target modules are zero and the formula still defines the map. -/
theorem exists_koszul_conormal_comparison_map
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ φ : koszulDualComplex A r f ⟶
        (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
          (koszulNormalDeterminant A I r),
      IsKoszulConormalComparison A I r f hf φ := by
  classical
  obtain ⟨b, hb⟩ := exists_koszul_conormal_basis A I r f hreg hf
  let e := exteriorPower.ιMulti A r (fun i : Fin r ↦ Finsupp.single i (1 : A))
  let w := exteriorPower.ιMulti (A ⧸ I) r b.coord
  let s : A ⧸ I := (-1) ^ (r * (r - 1) / 2)
  let t : (koszulDualComplex A r f).X r ⟶ koszulNormalDeterminant A I r :=
    ModuleCat.semilinearMapAddEquiv (Ideal.Quotient.mk I) _
      (ModuleCat.of (A ⧸ I) (⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent)))
      { toFun := fun x ↦ (s * Ideal.Quotient.mk I (x.hom e)) • w
        map_add' := by
          intro x y
          simp [koszulDualComplex, map_add, mul_add, add_smul]
        map_smul' := by
          intro a x
          simp only [koszulComplex] at x ⊢
          change (s * Ideal.Quotient.mk I (a * x.hom e)) • w =
            Ideal.Quotient.mk I a • ((s * Ideal.Quotient.mk I (x.hom e)) • w)
          simp only [map_mul, smul_smul]
          congr 1
          ring }
  have ht : ∀ i, (ComplexShape.up ℕ).Rel i r →
      (koszulDualComplex A r f).d i r ≫ t = 0 := by
    intro i hi
    have hr : i + 1 = r := hi
    subst r
    simp only [koszulDualComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (s * Ideal.Quotient.mk I
      ((koszulDualBoundary A (i + 1) i f x).hom e)) • w = 0
    have hx : Ideal.Quotient.mk I
        (x.hom (koszulBoundary A (i + 1) f i e)) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (boundary_top_mem A I i f hf x.hom)
    simp only [koszulComplex] at x hx ⊢
    simpa [koszulDualBoundary, Linear.leftComp, koszulComplex, e, map_mul] using
      congrArg (fun a : A ⧸ I ↦ (s * (Ideal.Quotient.mk I ((-1 : A) ^ (i + 1)) * a)) • w) hx
  let φ := HomologicalComplex.mkHomToSingle t ht
  refine ⟨φ, ?_⟩
  intro x v
  have hvalue : koszulComparisonValue A I r f φ x =
      (s * Ideal.Quotient.mk I (x.hom e)) • w := by
    dsimp [koszulComparisonValue, φ]
    rw [HomologicalComplex.mkHomToSingle_f]
    change ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) r
      (koszulNormalDeterminant A I r)).inv ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) r
      (koszulNormalDeterminant A I r)).hom) (t x) = _
    simp only [Iso.inv_hom_id, ModuleCat.id_apply]
    rfl
  rw [hvalue]
  have hp : exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
      (exteriorPower.ιMulti (A ⧸ I) r
        (fun i ↦ koszulConormalVector A I r f hf (v i))) =
        Ideal.Quotient.mk I (Matrix.of fun i j ↦ v i j).det := by
    simp only [w, exteriorPower.pairingDual_ιMulti_ιMulti,
      conormal_coord A I r f hf b hb]
    exact (RingHom.map_det (Ideal.Quotient.mk I) _).symm
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hp]
  simp only [koszulComplex] at x ⊢
  rw [top_functional_det A r x.hom v, map_mul]
  exact mul_assoc _ _ _

end ExteriorAlgebra
