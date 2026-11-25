/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # The Koszul complex under extension of scalars

Source: Stacks Project, Tag 062H, the complex identification in the proof.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ExteriorAlgebra

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

/-- Extension of scalars identifies the Koszul complex with the Koszul complex
of the images of its generators. No flatness or regularity is required.
Source: Stacks Project, Tag 062H, first equality in the proof
(blueprint: lem-sc-koszul-base-change-iso).

Proof: In degree n, use the exterior basis indexed by n-element subsets of Fin r.
The base-extended exterior basis over A and the exterior basis over S have the
same index set. Send each tensor 1 ⊗ e_I to the corresponding basis vector e_I
and extend S-linearly. The inverse sends e_I to 1 ⊗ e_I; the basis expansion
proves both inverse identities. The contraction formula gives the differential
on e_I as the alternating sum of the wedges with one vector omitted, multiplied
by the corresponding generator. Extension of scalars applies algebraMap A S
to each coefficient, which is exactly the differential over S. Hence the
component isomorphisms commute with differentials and assemble to a chain
complex isomorphism. For n > r both bases are empty; for r = 0 the only
nonzero term is degree zero. The basis construction also works for the zero
ring, so neither properness nor nontriviality is needed. -/
theorem nonempty_koszulBaseChangeIso
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (r : ℕ) (f : Fin r → A) :
    Nonempty (((ModuleCat.extendScalars (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (koszulComplex A r f) ≅
        koszulComplex S r (algebraMap A S ∘ f)) := by
  classical
  let K := koszulComplex A r f
  let t (n : ℕ) := ModuleCat.tensorEquivExtendScalars A S (K.X n)
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((t n).symm.trans (baseChangeExteriorEquiv A S r n)).toModuleIso) ?_⟩
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
  simp


end ExteriorAlgebra
