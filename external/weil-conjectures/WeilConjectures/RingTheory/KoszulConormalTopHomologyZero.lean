/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison

/-! Rank-zero top homology comparison.

(blueprint: lem-sc-koszul-conormal-top-homology-zero).

Proof in words: Evaluate the signed dual Koszul complex on the empty wedge; the incoming
differential is zero and the determinant normalization is the identity, hence the induced map is
an isomorphism.
Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext.
(blueprint: lem-sc-koszul-conormal-top-homology-zero).

The proof is the empty determinant calculation: the zero exterior power is the
coefficient module and both the incoming differential and determinant sign are
trivial.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

private theorem zero_wedge_expand (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] (x : ⋀[R]^0 M) :
    x = exteriorPower.zeroEquiv R M x •
      exteriorPower.ιMulti R 0 (fun i ↦ Fin.elim0 i) := by
  apply (exteriorPower.zeroEquiv R M).injective
  simp

private theorem pairing_zero (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] (x : ⋀[R]^0 (Module.Dual R M))
    (v : Fin 0 → M) :
    exteriorPower.pairingDual R M 0 x (exteriorPower.ιMulti R 0 v) =
      exteriorPower.zeroEquiv R (Module.Dual R M) x := by
  rw [zero_wedge_expand R (Module.Dual R M) x]
  simp

private theorem positive_wedge_subsingleton (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Subsingleton M] (n : ℕ) (hn : 0 < n) :
    Subsingleton (⋀[R]^n M) := by
  have h : (LinearMap.id : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M)) = 0 := by
    apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (exteriorPower.ιMulti_span R n M)).2
    intro y
    obtain ⟨v, hv⟩ := y.property
    change y.val = 0
    rw [← hv]
    exact (exteriorPower.ιMulti R n).map_coord_zero ⟨0, hn⟩
      (Subsingleton.elim _ _)
  apply subsingleton_of_forall_eq 0
  intro x
  exact congrArg (fun t : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M) ↦ t x) h

/-- Rank-zero top homology determinant calculation. The empty signed dual Koszul wedge has zero
incoming differential, and determinant normalization is the identity, hence the induced map is an
isomorphism. (blueprint: lem-sc-koszul-conormal-top-homology-zero). -/
theorem koszul_conormal_comparison_isIso_top_homology_zero
    (A : Type u) [CommRing A] (I : Ideal A) (f : Fin 0 → A)
    (hf : Ideal.span (Set.range f) = I)
    (b : Module.Basis (Fin 0) (A ⧸ I) I.Cotangent)
    (hb : ∀ i, b i = koszulConormalVector A I 0 f hf (Finsupp.single i 1))
    (φ : koszulDualComplex A 0 f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) 0).obj
        (koszulNormalDeterminant A I 0))
    (hφ : IsKoszulConormalComparison A I 0 f hf φ) :
    IsIso (HomologicalComplex.homologyMap φ 0) := by
  have _hb := hb
  have hI : I = ⊥ := by
    rw [← hf]
    simp
  have hnorm (x : (koszulComplex A 0 f).X 0 ⟶ ModuleCat.of A A) :
      exteriorPower.zeroEquiv (A ⧸ I) (Module.Dual (A ⧸ I) I.Cotangent)
        (koszulComparisonValue A I 0 f φ x) =
        Ideal.Quotient.mk I (x.hom
          (exteriorPower.ιMulti A 0 (fun i ↦ Fin.elim0 i))) := by
    simpa [pairing_zero] using hφ x (fun i ↦ Fin.elim0 i)
  have hquot : Function.Injective (Ideal.Quotient.mk I) := by
    exact (RingHom.injective_iff_ker_eq_bot _).mpr (by rw [Ideal.mk_ker, hI])
  have hzero : IsIso (φ.f 0) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro x y hxy
      have hval : x.hom (exteriorPower.ιMulti A 0 (fun i ↦ Fin.elim0 i)) =
          y.hom (exteriorPower.ιMulti A 0 (fun i ↦ Fin.elim0 i)) := by
        apply hquot
        rw [← hnorm x, ← hnorm y]
        exact congrArg
          (fun z ↦ exteriorPower.zeroEquiv (A ⧸ I)
            (Module.Dual (A ⧸ I) I.Cotangent)
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
              (koszulNormalDeterminant A I 0)).hom z)) hxy
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rw [zero_wedge_expand A (Fin 0 →₀ A) z]
      simp only [map_smul, hval]
    · intro y
      let z := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
        (koszulNormalDeterminant A I 0)).hom y
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
        (exteriorPower.zeroEquiv (A ⧸ I) (Module.Dual (A ⧸ I) I.Cotangent) z)
      let x : (koszulComplex A 0 f).X 0 ⟶ ModuleCat.of A A :=
        ModuleCat.ofHom (a • (exteriorPower.zeroEquiv A (Fin 0 →₀ A)).toLinearMap)
      refine ⟨x, ?_⟩
      apply (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
        (koszulNormalDeterminant A I 0)).toLinearEquiv.injective
      apply (exteriorPower.zeroEquiv (A ⧸ I)
        (Module.Dual (A ⧸ I) I.Cotangent)).injective
      change exteriorPower.zeroEquiv (A ⧸ I) (Module.Dual (A ⧸ I) I.Cotangent)
        (koszulComparisonValue A I 0 f φ x) = _
      rw [hnorm]
      change Ideal.Quotient.mk I
        (a * exteriorPower.zeroEquiv A (Fin 0 →₀ A)
          (exteriorPower.ιMulti A 0 (fun i ↦ Fin.elim0 i))) =
        exteriorPower.zeroEquiv (A ⧸ I) (Module.Dual (A ⧸ I) I.Cotangent) z
      rw [exteriorPower.zeroEquiv_ιMulti, mul_one]
      exact ha
  have hcomponents (n : ℕ) : IsIso (φ.f n) := by
    cases n with
    | zero => exact hzero
    | succ n =>
      have : Subsingleton (⋀[A]^(n + 1) (Fin 0 →₀ A)) :=
        positive_wedge_subsingleton A (Fin 0 →₀ A) (n + 1) (Nat.succ_pos n)
      have : Subsingleton
          (ModuleCat.of A (⋀[A]^(n + 1) (Fin 0 →₀ A)) ⟶ ModuleCat.of A A) :=
        ⟨fun x y ↦ by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          have hz : z = 0 := Subsingleton.elim _ _
          simp [hz]⟩
      have hs : CategoryTheory.Limits.IsZero ((koszulDualComplex A 0 f).X (n + 1)) := by
        change CategoryTheory.Limits.IsZero
          (ModuleCat.of A (ModuleCat.of A (⋀[A]^(n + 1) (Fin 0 →₀ A)) ⟶
            ModuleCat.of A A))
        exact ModuleCat.isZero_of_subsingleton _
      have ht := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ)
        0 (koszulNormalDeterminant A I 0) (n + 1) (by omega)
      exact CategoryTheory.Limits.IsZero.isIso hs ht (φ.f (n + 1))
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  infer_instance

end ExteriorAlgebra
