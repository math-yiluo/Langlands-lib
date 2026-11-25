/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.RingTheory.KoszulAugmentationLiftExists
import WeilConjectures.RingTheory.KoszulGeneratorChainMap
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Transport of normalized Koszul test cycles between quotient resolutions

Source: Stacks Project, Tags 062H and 00LS.
(blueprint: new-t2-koszul-restriction-test-cycles). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

section

open ExteriorAlgebra

private noncomputable def exteriorBasis
    (A : Type u) [CommRing A] (r n : ℕ) :
    Module.Basis (Set.powersetCard (Fin r) n) A (⋀[A]^n (Fin r →₀ A)) :=
  (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower n

private noncomputable def baseChangeExteriorEquiv
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] (r n : ℕ) :
    S ⊗[A] (⋀[A]^n (Fin r →₀ A)) ≃ₗ[S] ⋀[S]^n (Fin r →₀ S) :=
  ((exteriorBasis A r n).baseChange S).equiv (exteriorBasis S r n) (Equiv.refl _)

private theorem baseChangeExteriorEquiv_wedge
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] (r n : ℕ)
    (g : Fin n → Fin r) :
    baseChangeExteriorEquiv A S r n
      (1 ⊗ₜ[A] exteriorPower.ιMulti A n (fun i ↦ Finsupp.single (g i) 1)) =
        exteriorPower.ιMulti S n (fun i ↦ Finsupp.single (g i) 1) := by
  apply (exteriorBasis S r n).repr.injective
  ext t
  simp only [baseChangeExteriorEquiv, Module.Basis.equiv, Equiv.refl_symm,
    Module.Basis.reindex_refl, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.baseChange_repr_tmul]
  simp only [exteriorBasis, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti, Module.Basis.coord_apply,
    Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, Finsupp.single_apply,
    Algebra.smul_def, mul_one]
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

private theorem koszulBoundary_wedge
    (A : Type u) [CommRing A] (r n : ℕ) (f : Fin r → A) (g : Fin (n + 1) → Fin r) :
    koszulBoundary A r f n
      (exteriorPower.ιMulti A (n + 1) (fun i ↦ Finsupp.single (g i) 1)) =
        ∑ i : Fin (n + 1), ((-1 : A) ^ (i.val + 2) * f (g i)) •
          exteriorPower.ιMulti A n (fun j ↦ Finsupp.single (g (i.succAbove j)) 1) := by
  obtain ⟨D, _, _, huniq, _, _, _, hform, _, _⟩ :=
    koszul_differential A (Fin r →₀ A) (Finsupp.linearCombination A f)
  have hD : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin r →₀ A))) (Finsupp.linearCombination A f) = D := by
    apply huniq
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro v x
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm A (Fin r →₀ A)))
          (Finsupp.linearCombination A f) v x
  apply Subtype.val_injective
  simpa [koszulBoundary, hD, Finsupp.linearCombination_single,
    Algebra.smul_def, Function.comp_def] using
    hform n (fun i ↦ Finsupp.single (g i) 1)

private theorem normalized_koszulBaseChangeIso
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (r : ℕ) (f : Fin r → A) :
    ∃ e : ((ModuleCat.extendScalars (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (koszulComplex A r f) ≅
        koszulComplex S r (algebraMap A S ∘ f),
      ∀ (n : ℕ) (g : Fin n → Fin r),
        e.hom.f n (ModuleCat.tensorEquivExtendScalars A S
          ((koszulComplex A r f).X n)
            (1 ⊗ₜ[A] exteriorPower.ιMulti A n (fun i ↦ Finsupp.single (g i) 1))) =
          exteriorPower.ιMulti S n (fun i ↦ Finsupp.single (g i) 1) := by
  classical
  let K := koszulComplex A r f
  let t (n : ℕ) := ModuleCat.tensorEquivExtendScalars A S (K.X n)
  let e : ((ModuleCat.extendScalars (algebraMap A S)).mapHomologicalComplex
      (.down ℕ)).obj K ≅ koszulComplex S r (algebraMap A S ∘ f) :=
    HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((t n).symm.trans (baseChangeExteriorEquiv A S r n)).toModuleIso)
    (by
      intro i j hij
      have he : i = j + 1 := by simpa using hij.symm
      subst i
      apply (cancel_epi (t (j + 1)).toModuleIso.hom).mp
      ext1
      apply ((exteriorBasis A r (j + 1)).baseChange S).ext
      intro v
      simp only [Module.Basis.baseChange_apply]
      simp only [koszulComplex, ChainComplex.of_d]
      change koszulBoundary S r (algebraMap A S ∘ f) j
          (baseChangeExteriorEquiv A S r (j + 1)
            ((t (j + 1)).symm (t (j + 1) (1 ⊗ₜ[A] (exteriorBasis A r (j + 1)) v)))) = _
      rw [LinearEquiv.symm_apply_apply]
      change koszulBoundary S r (algebraMap A S ∘ f) j
          (baseChangeExteriorEquiv A S r (j + 1)
            (1 ⊗ₜ[A] (exteriorBasis A r (j + 1)) v)) =
        baseChangeExteriorEquiv A S r j ((t j).symm
          ((ModuleCat.extendScalars (algebraMap A S)).map (K.d (j + 1) j)
            (t (j + 1) (1 ⊗ₜ[A] (exteriorBasis A r (j + 1)) v))))
      simp only [t, ModuleCat.tensorEquivExtendScalars_tmul, ModuleCat.ExtendScalars.map_tmul]
      rw [← ModuleCat.tensorEquivExtendScalars_tmul A S (K.X j)]
      simp only [LinearEquiv.symm_apply_apply, K, koszulComplex, ChainComplex.of_d]
      change koszulBoundary S r (algebraMap A S ∘ f) j
          (baseChangeExteriorEquiv A S r (j + 1)
            (1 ⊗ₜ[A] (exteriorBasis A r (j + 1)) v)) =
        baseChangeExteriorEquiv A S r j
          (1 ⊗ₜ[A] koszulBoundary A r f j ((exteriorBasis A r (j + 1)) v))
      simp only [exteriorBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
      simp only [Function.comp_def, Finsupp.coe_basisSingleOne]
      rw [baseChangeExteriorEquiv_wedge, koszulBoundary_wedge, koszulBoundary_wedge]
      simp only [TensorProduct.tmul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [TensorProduct.tmul_smul]
      conv_rhs => arg 2; rw [← algebraMap_smul S]
      rw [map_smul, baseChangeExteriorEquiv_wedge]
      simp)
  refine ⟨e, ?_⟩
  intro n g
  change baseChangeExteriorEquiv A S r n
    ((t n).symm (t n (1 ⊗ₜ[A] exteriorPower.ιMulti A n
      (fun i ↦ Finsupp.single (g i) 1)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact baseChangeExteriorEquiv_wedge A S r n g


private theorem tensorKoszul_d_zero (A : Type u) [CommRing A]
    (I : Ideal A) (r : ℕ) (g : Fin r → I) (i j : ℕ) :
    (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
      (ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A)))).d i j = 0 := by
  classical
  by_cases hij : i = j + 1
  · subst i
    change (tensorRight (ModuleCat.of A (A ⧸ I))).map
      ((ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A))).d (j + 1) j) = 0
    simp only [ExteriorAlgebra.koszulComplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply LinearMap.ext
    intro y
    change ExteriorAlgebra.koszulBoundary A r (fun k ↦ (g k : A)) j
      (exteriorPower.ιMulti A (j + 1) v) ⊗ₜ[A] y = 0
    rw [ExteriorAlgebra.boundary_wedge, TensorProduct.sum_tmul]
    apply Finset.sum_eq_zero
    intro k hk
    rw [TensorProduct.smul_tmul]
    have he : Finsupp.linearCombination A (fun k ↦ (g k : A)) =
        I.subtype.comp (Finsupp.linearCombination A g) := by
      ext k
      simp
    have hmem : Finsupp.linearCombination A (fun k ↦ (g k : A)) (v k) ∈ I := by
      rw [he]
      exact (Finsupp.linearCombination A g (v k)).property
    have hz : (((-1 : A) ^ (k.val + 2) *
        Finsupp.linearCombination A (fun k ↦ (g k : A)) (v k)) • y : A ⧸ I) = 0 := by
      change Ideal.Quotient.mk I _ * y = 0
      rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, mul_zero, zero_mul]
    rw [hz, TensorProduct.tmul_zero]
  · have hz := (ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A))).shape i j
      (by simpa [eq_comm] using hij)
    change (tensorRight (ModuleCat.of A (A ⧸ I))).map
      ((ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A))).d i j) = 0
    rw [hz, Functor.map_zero]

end

/-- An augmented comparison of quotient resolutions carries compatible Koszul test
cycles to each other. This is a chain-level statement: it mentions neither Tor
coordinates nor the normalized exterior-to-Tor comparison.
Source: Stacks Project, Tag 062H (Koszul scalar extension), Tag 00LS (Koszul
augmentation lifts), and Tag 0623 (the quotient-tensored Koszul differential).
(blueprint: new-t2-koszul-restriction-test-cycles).

Proof: Lift the Koszul augmentation of g into P. Extend this lift to B and compose
with the adjoint of a. The standard scalar-extension isomorphism from the Koszul
complex on g to that on g' sends each standard exterior basis vector to the same
basis vector: the contraction formula commutes with φ because φ(g_j)=g'_j.
Transport the extended lift by the inverse of this isomorphism to obtain aB.
In degree zero both augmentations send the empty wedge to 1; the ring map ψ
preserves 1, so ha proves its displayed augmentation equation. All
quotient-tensored Koszul differentials vanish, since their coefficients lie
in I or J. Thus the standard top wedges tensored with 1 have cycle preimages
zA,zB. Tensor compatibility hk identifies the images of these two wedges
under the resolution lifts: ψ preserves 1 and scalar extension preserves
standard wedges. Naturality of the cycles inclusion gives exactly the last
equation. No acyclicity of either Koszul complex or flatness of φ is used.
For n=0 use the empty wedge and the degree-zero augmentation. For zero quotient
rings the tensor complexes vanish, and the cycle representatives are zero. -/
theorem exists_koszul_restriction_test_cycles
    (A B : Type u) [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (φ : A →+* B) (n : ℕ) (g : Fin n → I) (g' : Fin n → J)
    (hg : ∀ j, φ (g j) = g' j)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (Q : ProjectiveResolution (ModuleCat.of B (B ⧸ J)))
    (ψ : (A ⧸ I) →+* (B ⧸ J))
    (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
      (.down ℕ)).obj Q.complex)
    (k : ((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
        (.down ℕ)).obj P.complex ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
        (((tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex
          (.down ℕ)).obj Q.complex))
    (ha : ∀ x : P.complex.X 0, Q.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x))
    (hk : ∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
      k.f j (x ⊗ₜ[A] y) = (show Q.complex.X j from a.f j x) ⊗ₜ[B] (ψ y)) :
    let KA := ExteriorAlgebra.koszulComplex A n (fun j ↦ (g j : A))
    let KB := ExteriorAlgebra.koszulComplex B n (fun j ↦ (g' j : B))
    let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    let TB := (tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex (.down ℕ)
    ∃ (aA : KA ⟶ P.complex) (aB : KB ⟶ Q.complex),
      aA.f 0 ≫ P.π.f 0 = ModuleCat.ofHom (I.mkQ.comp
        (exteriorPower.zeroEquiv A (Fin n →₀ A)).toLinearMap) ∧
      aB.f 0 ≫ Q.π.f 0 = ModuleCat.ofHom (J.mkQ.comp
        (exteriorPower.zeroEquiv B (Fin n →₀ B)).toLinearMap) ∧
      ∃ (zA : (TA.obj KA).cycles n) (zB : (TB.obj KB).cycles n),
        (TA.obj KA).iCycles n zA =
          (exteriorPower.ιMulti A n (fun j ↦ Finsupp.single j 1)) ⊗ₜ[A] (1 : A ⧸ I) ∧
        (TB.obj KB).iCycles n zB =
          (exteriorPower.ιMulti B n (fun j ↦ Finsupp.single j 1)) ⊗ₜ[B] (1 : B ⧸ J) ∧
        (TB.obj Q.complex).iCycles n (HomologicalComplex.cyclesMap (TB.map aB) n zB) =
          k.f n ((TA.obj P.complex).iCycles n
            (HomologicalComplex.cyclesMap (TA.map aA) n zA))  := by
  classical
  let := φ.toAlgebra
  let KA := ExteriorAlgebra.koszulComplex A n (fun j ↦ (g j : A))
  let KB := ExteriorAlgebra.koszulComplex B n (fun j ↦ (g' j : B))
  let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
  let TB := (tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex (.down ℕ)
  obtain ⟨aA, haA⟩ := koszul_augmentation_lift_exists A I n g P
  have hdata := normalized_koszulBaseChangeIso
    A B n (fun j ↦ (g j : A))
  have hgen : algebraMap A B ∘ (fun j ↦ (g j : A)) = (fun j ↦ (g' j : B)) := by
    funext j
    exact hg j
  rw [hgen] at hdata
  obtain ⟨e, he⟩ := hdata
  let : (ModuleCat.extendScalars φ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  let adj := (ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.down ℕ)
  let lB := (adj.homEquiv KA Q.complex).symm (aA ≫ a)
  let aB : KB ⟶ Q.complex := e.inv ≫ lB
  have hl (j : ℕ) (x : KA.X j) :
      lB.f j (ModuleCat.tensorEquivExtendScalars A B (KA.X j) (1 ⊗ₜ[A] x)) =
        a.f j (aA.f j x) := by
    have hh := (adj.homEquiv KA Q.complex).apply_symm_apply (aA ≫ a)
    rw [Adjunction.homEquiv_unit] at hh
    have hh' := congrArg (fun f ↦ f.f j x) hh
    exact hh'
  have hab (j : ℕ) (v : Fin j → Fin n) :
      aB.f j (exteriorPower.ιMulti B j (fun k ↦ Finsupp.single (v k) 1)) =
        a.f j (aA.f j (exteriorPower.ιMulti A j
          (fun k ↦ Finsupp.single (v k) 1))) := by
    have hh := congrArg (fun x ↦ e.inv.f j x) (he j v)
    have hinv := congrArg (fun f ↦ f.f j
      (ModuleCat.tensorEquivExtendScalars A B (KA.X j)
        (1 ⊗ₜ[A] exteriorPower.ιMulti A j (fun k ↦ Finsupp.single (v k) 1))))
      e.hom_inv_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hinv
    change lB.f j (e.inv.f j _) = _
    rw [← hh, hinv]
    exact hl j _
  have haB : aB.f 0 ≫ Q.π.f 0 = ModuleCat.ofHom (J.mkQ.comp
      (exteriorPower.zeroEquiv B (Fin n →₀ B)).toLinearMap) := by
    apply (cancel_epi (exteriorPower.zeroEquiv B (Fin n →₀ B)).symm.toModuleIso.hom).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    have hzeroB : (exteriorPower.zeroEquiv B (Fin n →₀ B)).symm 1 =
        exteriorPower.ιMulti B 0 (fun j ↦ Finsupp.single (Fin.elim0 j) 1) := by
      apply (exteriorPower.zeroEquiv B (Fin n →₀ B)).injective
      simp
    change Q.π.f 0 (aB.f 0 ((exteriorPower.zeroEquiv B (Fin n →₀ B)).symm 1)) = _
    rw [hzeroB, hab 0 Fin.elim0, ha]
    have hh := congrArg (fun f ↦ f
      (exteriorPower.ιMulti A 0 (fun j ↦ Finsupp.single (Fin.elim0 j) 1))) haA
    change P.π.f 0 (aA.f 0 _) = _ at hh
    rw [hh]
    change ψ (I.mkQ (exteriorPower.zeroEquiv A (Fin n →₀ A)
      (exteriorPower.ιMulti A 0 (fun j ↦ Finsupp.single (Fin.elim0 j) 1)))) =
        J.mkQ (exteriorPower.zeroEquiv B (Fin n →₀ B)
          ((exteriorPower.zeroEquiv B (Fin n →₀ B)).symm 1))
    rw [exteriorPower.zeroEquiv_ιMulti, LinearEquiv.apply_symm_apply]
    exact map_one ψ
  let yA : (TA.obj KA).X n :=
    exteriorPower.ιMulti A n (fun j ↦ Finsupp.single j 1) ⊗ₜ[A] (1 : A ⧸ I)
  let yB : (TB.obj KB).X n :=
    exteriorPower.ιMulti B n (fun j ↦ Finsupp.single j 1) ⊗ₜ[B] (1 : B ⧸ J)
  let cA := (TA.obj KA).iCyclesIso n ((ComplexShape.down ℕ).next n) rfl
    (tensorKoszul_d_zero A I n g _ _)
  let cB := (TB.obj KB).iCyclesIso n ((ComplexShape.down ℕ).next n) rfl
    (tensorKoszul_d_zero B J n g' _ _)
  let zA := cA.inv yA
  let zB := cB.inv yB
  have hzA : (TA.obj KA).iCycles n zA = yA := by
    exact congrArg (fun f ↦ f yA) cA.inv_hom_id
  have hzB : (TB.obj KB).iCycles n zB = yB := by
    exact congrArg (fun f ↦ f yB) cB.inv_hom_id
  refine ⟨aA, aB, haA, haB, zA, zB, hzA, hzB, ?_⟩
  have hA := congrArg (fun f ↦ f zA) (HomologicalComplex.cyclesMap_i (TA.map aA) n)
  have hB := congrArg (fun f ↦ f zB) (HomologicalComplex.cyclesMap_i (TB.map aB) n)
  simp only [ConcreteCategory.comp_apply] at hA hB
  rw [hA, hB, hzA, hzB]
  change (aB.f n (exteriorPower.ιMulti B n (fun j ↦ Finsupp.single j 1))) ⊗ₜ[B]
      (1 : B ⧸ J) =
    k.f n ((aA.f n (exteriorPower.ιMulti A n (fun j ↦ Finsupp.single j 1))) ⊗ₜ[A]
      (1 : A ⧸ I))
  rw [hk, map_one, hab n (fun j ↦ j)]


end AlgebraicGeometry
