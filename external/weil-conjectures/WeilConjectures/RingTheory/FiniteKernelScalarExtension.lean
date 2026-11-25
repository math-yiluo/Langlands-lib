/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Linear extension with finite error over the smaller field

Source: Stacks Project, Tag 07FG, finite support of the differential kernel and
extension of the remaining differential images to a basis.
(blueprint: lem-weil-pbc-finite-kernel-scalar-extension)
-/

@[expose] public section
set_option autoImplicit false
open scoped TensorProduct
universe u v w x y

namespace LinearMap

/-- A linear map from the original vector space can be extended through a map on its
scalar extension, up to an error of finite rank over the original field.

Source: Stacks Project, Tag 07FG, the paragraphs choosing the finite set J0 and
extending the independent differential images to a basis.
(blueprint: lem-weil-pbc-finite-kernel-scalar-extension)

Proof: Choose a k-basis b of V. Its scalar extension is a K-basis of K tensor V.
Choose finitely many generators of the kernel of phi, and let J0 be the union of
their finite supports in that basis. The kernel is contained in the span of the
basis elements with indices in J0. The images under phi of the basis elements
outside J0 are linearly independent: any relation is in the kernel and also in
the span of the complementary basis elements, so its coefficients vanish.
Prescribe on these images the values ell(b_j), and extend this linear map to W
by extending the independent family to a basis and assigning zero on the extra
vectors. Call the resulting K-linear map g. The k-linear difference on V
vanishes on b_j outside J0. For each vector, its finite basis expansion therefore
expresses this difference as a k-linear combination of the finitely many values
ell(b_j) - g(phi(1 tensor b_j)), j in J0. Take f to be this finite image.
This works also when V or M is zero or J0 is empty. -/
theorem exists_extension_finite_error
    (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K]
    (V : Type w) [AddCommGroup V] [Module k V]
    (W : Type x) [AddCommGroup W] [Module k W] [Module K W] [IsScalarTower k K W]
    (M : Type y) [AddCommGroup M] [Module k M] [Module K M] [IsScalarTower k K M]
    (phi : K ⊗[k] V →ₗ[K] W) (hphi : Module.Finite K phi.ker)
    (ell : V →ₗ[k] M) :
    ∃ (g : W →ₗ[K] M) (f : Finset M),
      ∀ v : V, ell v - g (phi (1 ⊗ₜ[k] v)) ∈ Submodule.span k (f : Set M) := by
  classical
  let b := Module.Free.chooseBasis k V
  let B := b.baseChange K
  have : Module.Finite K phi.ker := hphi
  obtain ⟨t, ht⟩ := Submodule.FG.of_finite (N := phi.ker)
  let s := t.biUnion fun z ↦ (B.repr z).support
  have hker : phi.ker ≤ Submodule.span K (B '' (s : Set (Module.Free.ChooseBasisIndex k V))) := by
    rw [← ht, Submodule.span_le]
    intro z hz
    apply (B.mem_span_image).mpr
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨z, hz, hi⟩
  let J := {i : Module.Free.ChooseBasisIndex k V // i ∉ s}
  have hdis : Disjoint (Submodule.span K (Set.range fun i : J ↦ B i.val)) phi.ker := by
    have hd := B.linearIndependent.disjoint_span_image
      (s := {i | i ∉ s}) (t := (s : Set _)) (by exact Set.disjoint_left.mpr fun _ h hn ↦ h hn)
    apply Disjoint.mono_right hker
    convert hd using 1
    congr 1
    ext z
    simp [J]
  have hli : LinearIndependent K (fun i : J ↦ phi (B i.val)) :=
    (B.linearIndependent.comp Subtype.val Subtype.val_injective).map hdis
  let c := Module.Basis.span hli
  let q := c.constr K (fun i : J ↦ ell (b i.val))
  obtain ⟨g, hg⟩ := q.exists_extend
  have hgB (i : J) : g (phi (B i.val)) = ell (b i.val) := by
    have he := LinearMap.congr_fun hg (c i)
    change g (c i : W) = (c.constr K (fun j : J ↦ ell (b j.val))) (c i) at he
    rw [Module.Basis.constr_basis] at he
    simpa only [c, Module.Basis.span_apply] using he
  let j : V →ₗ[k] K ⊗[k] V := TensorProduct.mk k K V 1
  let delta : V →ₗ[k] M := ell -
    (g.restrictScalars k).comp ((phi.restrictScalars k).comp j)
  let f := s.image (fun i ↦ delta (b i))
  refine ⟨g, f, ?_⟩
  have hb (i : Module.Free.ChooseBasisIndex k V) :
      delta (b i) ∈ Submodule.span k (f : Set M) := by
    by_cases hi : i ∈ s
    · exact Submodule.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · have he := hgB ⟨i, hi⟩
      have hz : delta (b i) = 0 := by
        simpa only [delta, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.restrictScalars_apply, j, TensorProduct.mk_apply,
          Module.Basis.baseChange_apply, B, sub_eq_zero] using he.symm
      rw [hz]
      exact Submodule.zero_mem _
  have hle : (⊤ : Submodule k V) ≤ (Submodule.span k (f : Set M)).comap delta := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hb i
  intro v
  exact hle (show v ∈ (⊤ : Submodule k V) from trivial)


end LinearMap
