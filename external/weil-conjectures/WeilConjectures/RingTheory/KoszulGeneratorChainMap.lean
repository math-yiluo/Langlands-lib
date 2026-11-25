/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Generator substitution for Koszul complexes

Source: Stacks Project, Tags 0BQY and 0BQZ.
(blueprint: new-q2-koszul-generator-chain-map).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- The Koszul boundary on a wedge is the alternating contraction sum.
Source: Stacks Project, Tags 0BQY and 0BQZ; the contraction formula in
`koszul_differential`. Shared by generator substitution and top evaluation.
(blueprint: new-q2-koszul-generator-chain-map).

Proof: Uniqueness in koszul_differential identifies its derivation with
contractLeft at the zero quadratic form, since both kill one and obey the same
recursion on a generator times an exterior-algebra element. Apply the resulting
wedge formula and compare the underlying exterior-algebra elements by
Subtype.ext; scalar multiplication gives the displayed contraction sum. -/
theorem boundary_wedge
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (n : ℕ) (v : Fin (n + 1) → (Fin r →₀ A)) :
    koszulBoundary A r f n (exteriorPower.ιMulti A (n + 1) v) =
      ∑ i : Fin (n + 1),
        (((-1 : A) ^ (i.val + 2)) * Finsupp.linearCombination A f (v i)) •
          exteriorPower.ιMulti A n (v ∘ i.succAbove) := by
  classical
  let l := Finsupp.linearCombination A f
  obtain ⟨D, hD1, hrec, huniq, hgen, hzero, hdeg, hform, hleib, hdu⟩ :=
    koszul_differential A (Fin r →₀ A) l
  have hc : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin r →₀ A))) l = D := by
    apply huniq
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro v y
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul
          (Q := (0 : QuadraticForm A (Fin r →₀ A))) l v y
  apply Subtype.ext
  change CliffordAlgebra.contractLeft _ _ = _
  rw [hc]
  change D (ExteriorAlgebra.ιMulti A (n + 1) v) = _
  rw [hform]
  simp [l, Algebra.smul_def]

set_option backward.isDefEq.respectTransparency false in
/-- Exterior powers of a generator substitution intertwine normalized augmentations.
Source: Stacks Project, Tag 0BQZ, finite-free Koszul resolution computation.
(blueprint: new-q2-koszul-generator-chain-map).

Proof: The degree-n component is exteriorPower.map n t. On a wedge the contraction
formula is an alternating sum of wedges omitting one vector. The hypothesis on
the linear combinations makes the coefficients agree, so these components commute
with every differential. Extend this chain map by zero to integer degrees.
Degree zero is the identity under zeroEquiv, so the two normalized augmentations
commute there. Away from zero their target terms are zero. The extension's degree
-r component is the specified exterior power transported by extendXIso.
This construction includes r=0 and the zero quotient, and uses no inverse of t. -/
theorem exists_koszul_generator_chain_map
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f g : Fin r → A)
    (t : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A))
    (ht : (Finsupp.linearCombination A g).comp t = Finsupp.linearCombination A f)
    (εf : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
    (εg : (koszulComplex A r g).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
    (haugf : ∀ x : ⋀[A]^0 (Fin r →₀ A),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom
        (εf.f 0 (((koszulComplex A r f).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x))
    (haugg : ∀ x : ⋀[A]^0 (Fin r →₀ A),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom
        (εg.f 0 (((koszulComplex A r g).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x))
    : ∃ U : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
        (koszulComplex A r g).extend ComplexShape.embeddingDownNat,
      U ≫ εg = εf ∧
      ((koszulComplex A r f).extendXIso ComplexShape.embeddingDownNat
        (i := r) rfl).inv ≫ U.f (-(r : ℤ)) =
      ModuleCat.ofHom (exteriorPower.map r t) ≫
        ((koszulComplex A r g).extendXIso ComplexShape.embeddingDownNat
          (i := r) rfl).inv := by
  classical
  have hd (k : Fin r → A) (n : ℕ) : (koszulComplex A r k).d (n + 1) n =
      ModuleCat.ofHom (koszulBoundary A r k n) := by
    dsimp only [koszulComplex]
    exact ChainComplex.of_d _ _ n
  have hcomm (n : ℕ) :
      (koszulBoundary A r g n).comp (exteriorPower.map (n + 1) t) =
      (exteriorPower.map n t).comp (koszulBoundary A r f n) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, boundary_wedge, map_sum, map_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Function.comp_apply]
    rw [show Finsupp.linearCombination A g (t (v i)) =
      Finsupp.linearCombination A f (v i) from LinearMap.congr_fun ht (v i)]
    rfl
  let T : koszulComplex A r f ⟶ koszulComplex A r g :=
    ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (exteriorPower.map n t)) (by
      intro n
      rw [hd g n, hd f n]
      exact ModuleCat.hom_ext (hcomm n))
  let U := HomologicalComplex.extendMap T ComplexShape.embeddingDownNat
  refine ⟨U, ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro j
    by_cases hj : j = 0
    · subst j
      apply (cancel_mono (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom).mp
      apply (cancel_epi ((koszulComplex A r f).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).inv).mp
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of A (A ⧸ I))).hom
          (εg.f 0 (U.f 0 (((koszulComplex A r f).extendXIso
            ComplexShape.embeddingDownNat (i := 0) rfl).inv x))) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of A (A ⧸ I))).hom
          (εf.f 0 (((koszulComplex A r f).extendXIso
            ComplexShape.embeddingDownNat (i := 0) rfl).inv x))
      have hUf : ((koszulComplex A r f).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv ≫ U.f 0 =
          ModuleCat.ofHom (exteriorPower.map 0 t) ≫
            ((koszulComplex A r g).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv := by
        dsimp only [U]
        rw [HomologicalComplex.extendMap_f T ComplexShape.embeddingDownNat
          (i := 0) (i' := 0) rfl]
        simp only [Iso.inv_hom_id_assoc]
        rfl
      have hh := congrArg (fun k ↦ k x) hUf
      change U.f 0 (((koszulComplex A r f).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).inv x) =
        ((koszulComplex A r g).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv
            (exteriorPower.map 0 t x) at hh
      rw [hh, haugg, haugf]
      congr 1
      exact LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality t) x
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I)) j hj).eq_of_tgt _ _
  · dsimp only [U]
    rw [HomologicalComplex.extendMap_f T ComplexShape.embeddingDownNat
      (i := r) (i' := -(r : ℤ)) rfl]
    simp only [Iso.inv_hom_id_assoc]
    rfl

end ExteriorAlgebra
