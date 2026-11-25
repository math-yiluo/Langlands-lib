/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Tensor products and internal homs of Frobenius modules

The tensor product `M ⊗ N` of two Frobenius modules carries the Frobenius `F_M ⊗ F_N`, and the
space of linear maps `Hom(M, N)` the Frobenius `X ↦ F_N ∘ X ∘ F_M⁻¹`. The two are related by the
Frobenius-equivariant isomorphism `Hom(M^∨, N) ≅ M ⊗ N`.

Over an algebraically closed field, the eigenvalues of `F_M ⊗ F_N` are exactly the products
`a b` of an eigenvalue `a` of `F_M` and an eigenvalue `b` of `F_N`. Consequently weights add
under tensor products.

## Main declarations

- `Module.End.hasEigenvalue_map_mul`: `a b` is an eigenvalue of `f ⊗ g`.
- `Module.End.exists_hasEigenvalue_mul_of_hasEigenvalue_map`: every eigenvalue of `f ⊗ g`, `f`
  invertible, is such a product.
- `FrobeniusModule.tensor`, `FrobeniusModule.linearHom`: the tensor product and the internal hom.
- `FrobeniusModule.homDualEquiv`: `Hom(M^∨, N) ≅ M ⊗ N`.
- `FrobeniusModule.Equiv.ofBilinear`: a perfect Frobenius-invariant pairing `P × A → C`
  identifies `P` with `Hom(A, C)`; `FrobeniusModule.Equiv.tensorOfHomDual`: `P ≅ Hom(A, N)` and
  `A ≅ M^∨` give `P ≅ M ⊗ N`.
- `FrobeniusModule.HasWeightsAtMost.tensor`, `FrobeniusModule.IsPureOfWeight.tensor`: weights
  of tensor products.
-/

@[expose] public section

universe u v t

open TensorProduct

namespace Module.End

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- If a nonzero `T : V ⊗ W` satisfies `(1 ⊗ g) T = b T`, then `b` is an eigenvalue of `g`:
otherwise `g - b` is injective, hence so is `1 ⊗ (g - b)`, as `V` is flat over the field `K`. -/
theorem hasEigenvalue_of_lTensor_apply_eq_smul {g : End K W} {b : K} {T : V ⊗[K] W}
    (hT : T ≠ 0) (h : g.lTensor V T = b • T) : g.HasEigenvalue b := by
  rw [hasEigenvalue_iff, eigenspace_def, Ne, LinearMap.ker_eq_bot]
  intro hinj
  refine hT (Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ hinj ?_)
  rw [LinearMap.lTensor_sub, LinearMap.lTensor_smul, one_eq_id, LinearMap.lTensor_id]
  simp [h]

/-- If a nonzero `T : V ⊗ W` satisfies `(f ⊗ 1) T = a T`, then `a` is an eigenvalue of `f`. -/
theorem hasEigenvalue_of_rTensor_apply_eq_smul {f : End K V} {a : K} {T : V ⊗[K] W}
    (hT : T ≠ 0) (h : f.rTensor W T = a • T) : f.HasEigenvalue a := by
  rw [hasEigenvalue_iff, eigenspace_def, Ne, LinearMap.ker_eq_bot]
  intro hinj
  refine hT (Module.Flat.rTensor_preserves_injective_linearMap (M := W) _ hinj ?_)
  rw [LinearMap.rTensor_sub, LinearMap.rTensor_smul, one_eq_id, LinearMap.rTensor_id]
  simp [h]

/-- If `a` is an eigenvalue of `f` and `b` one of `g`, then `a b` is an eigenvalue of `f ⊗ g`:
the tensor product of eigenvectors is an eigenvector. -/
theorem hasEigenvalue_map_mul {f : End K V} {g : End K W} {a b : K} (ha : f.HasEigenvalue a)
    (hb : g.HasEigenvalue b) : HasEigenvalue (TensorProduct.map f g) (a * b) := by
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  obtain ⟨w, hw⟩ := hb.exists_hasEigenvector
  rw [hasEigenvector_iff, mem_eigenspace_iff] at hv hw
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ v ≠ 0 := by
    by_contra! H
    exact hv.2 ((Module.forall_dual_apply_eq_zero_iff K v).1 H)
  refine hasEigenvalue_of_hasEigenvector (x := v ⊗ₜ w) (hasEigenvector_iff.2 ⟨?_, fun h ↦ ?_⟩)
  · rw [mem_eigenspace_iff, map_tmul, hv.1, hw.1, smul_tmul_smul]
  · have := congrArg (fun T ↦ TensorProduct.lid K W (TensorProduct.map φ LinearMap.id T)) h
    simp [hφ, hw.2] at this

/-- Over an algebraically closed field, every eigenvalue `μ` of `f ⊗ g` on `V ⊗ W`, for `f`
invertible and `V`, `W` finite-dimensional, is a product `a b` of an eigenvalue `a` of `f` and an
eigenvalue `b` of `g`. -/
theorem exists_hasEigenvalue_mul_of_hasEigenvalue_map [IsAlgClosed K] [FiniteDimensional K V]
    [FiniteDimensional K W] (f : V ≃ₗ[K] V) (g : End K W) {μ : K}
    (h : HasEigenvalue (TensorProduct.map f.toLinearMap g) μ) :
    ∃ a b, HasEigenvalue (f : End K V) a ∧ g.HasEigenvalue b ∧ μ = a * b := by
  -- `f ⊗ 1` commutes with `f ⊗ g`, hence preserves its `μ`-eigenspace, on which it has an
  -- eigenvector `T`; then `T` is also an eigenvector of `1 ⊗ g`.
  have hmaps (T : V ⊗[K] W) (hT : T ∈ eigenspace (TensorProduct.map f.toLinearMap g) μ) :
      (f : End K V).rTensor W T ∈ eigenspace (TensorProduct.map f.toLinearMap g) μ := by
    rw [mem_eigenspace_iff] at hT ⊢
    rw [← LinearMap.comp_apply, LinearMap.map_comp_rTensor,
      ← LinearMap.rTensor_comp_map (f' := (f : End K V)) (f := (f : End K V)) (g := g),
      LinearMap.comp_apply, hT, map_smul]
  have := Submodule.nontrivial_iff_ne_bot.2 (hasEigenvalue_iff.1 h)
  obtain ⟨a, ha⟩ := exists_eigenvalue (((f : End K V).rTensor W).restrict hmaps)
  obtain ⟨⟨T, hTE⟩, hT⟩ := ha.exists_hasEigenvector
  rw [hasEigenvector_iff, mem_eigenspace_iff] at hT
  rw [mem_eigenspace_iff] at hTE
  have hRT : (f : End K V).rTensor W T = a • T := congrArg Subtype.val hT.1
  have hT0 : T ≠ 0 := fun h0 ↦ hT.2 (Subtype.ext h0)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hRT
    exact hT0 (Module.Flat.rTensor_preserves_injective_linearMap (M := W) _ f.injective
      (hRT.trans (map_zero _).symm))
  have hlT : g.lTensor V T = (μ / a) • T := by
    have hgT : a • g.lTensor V T = μ • T := by
      rw [← hTE, ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hRT, map_smul]
    rw [div_eq_inv_mul, mul_smul, ← hgT, inv_smul_smul₀ ha0]
  refine ⟨a, μ / a, hasEigenvalue_of_rTensor_apply_eq_smul hT0 hRT,
    hasEigenvalue_of_lTensor_apply_eq_smul hT0 hlT, ?_⟩
  field_simp

end Module.End

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- The tensor product `M ⊗ N` of two Frobenius modules, with the Frobenius `F_M ⊗ F_N`. -/
noncomputable def tensor (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K) :
    FrobeniusModule.{max u t, v} K where
  carrier := M.carrier ⊗[K] N.carrier
  frobenius := TensorProduct.congr M.frobenius N.frobenius

lemma tensor_frobenius_tmul (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K)
    (x : M.carrier) (y : N.carrier) :
    (M.tensor N).frobenius (x ⊗ₜ y) = M.frobenius x ⊗ₜ N.frobenius y :=
  rfl

lemma frobeniusEnd_tensor (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K) :
    (M.tensor N).frobeniusEnd = TensorProduct.map M.frobeniusEnd N.frobeniusEnd :=
  TensorProduct.ext' fun _ _ ↦ rfl

/-- The internal hom `Hom(M, N)` of two Frobenius modules, with the Frobenius
`X ↦ F_N ∘ X ∘ F_M⁻¹`. -/
noncomputable def linearHom (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K) :
    FrobeniusModule.{max u t, v} K where
  carrier := M.carrier →ₗ[K] N.carrier
  frobenius := M.frobenius.arrowCongr N.frobenius

/-- The Frobenius of `Hom_K(M, N)` sends `X` to `F_N ∘ X ∘ F_M⁻¹`. -/
lemma linearHom_frobenius_apply (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K)
    (X : M.carrier →ₗ[K] N.carrier) :
    ((M.linearHom N).frobenius X : M.carrier →ₗ[K] N.carrier) =
      N.frobenius.toLinearMap ∘ₗ X ∘ₗ M.frobenius.symm.toLinearMap :=
  rfl

/-- An isomorphism of Frobenius modules intertwines the inverse Frobenius automorphisms. -/
lemma Equiv.map_frobenius_symm {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N)
    (x : M.carrier) :
    e.toLinearEquiv (M.frobenius.symm x) = N.frobenius.symm (e.toLinearEquiv x) := by
  rw [LinearEquiv.eq_symm_apply, ← e.map_frobenius, LinearEquiv.apply_symm_apply]

/-- The inverse of an isomorphism of Frobenius modules intertwines the inverse Frobenius
automorphisms. -/
lemma Equiv.symm_map_frobenius_symm {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N)
    (x : N.carrier) :
    e.toLinearEquiv.symm (N.frobenius.symm x) = M.frobenius.symm (e.toLinearEquiv.symm x) := by
  rw [LinearEquiv.symm_apply_eq, e.map_frobenius_symm, LinearEquiv.apply_symm_apply]

/-- Isomorphisms of Frobenius modules induce an isomorphism of internal homs. -/
def Equiv.homCongr {M M' : FrobeniusModule.{u, v} K} {N N' : FrobeniusModule.{t, v} K}
    (e₁ : M.Equiv M') (e₂ : N.Equiv N') : (M.linearHom N).Equiv (M'.linearHom N') where
  toLinearEquiv := e₁.toLinearEquiv.arrowCongr e₂.toLinearEquiv
  map_frobenius X := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [linearHom, LinearEquiv.arrowCongr_apply]
    rw [e₂.map_frobenius, e₁.symm_map_frobenius_symm]

/-- A perfect pairing `p : P × A → C` invariant under the Frobenius,
`p (F_P x) (F_A y) = F_C (p x y)`, identifies `P` with `Hom(A, C)`. -/
noncomputable def Equiv.ofBilinear {P A C : FrobeniusModule.{u, v} K}
    (p : P.carrier →ₗ[K] A.carrier →ₗ[K] C.carrier) (hp : Function.Bijective p)
    (h : ∀ x y, p (P.frobenius x) (A.frobenius y) = C.frobenius (p x y)) :
    P.Equiv (A.linearHom C) where
  toLinearEquiv := LinearEquiv.ofBijective p hp
  map_frobenius x := LinearMap.ext fun y ↦ by
    obtain ⟨z, rfl⟩ := A.frobenius.surjective y
    rw [linearHom_frobenius_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact h x z

/-- The linear isomorphism `Hom(M^∨, N) ≃ M ⊗ N` underlying `FrobeniusModule.homDualEquiv`,
sending the map `φ ↦ φ(x) y` to `x ⊗ y`. -/
noncomputable def homDualLinearEquiv (M : FrobeniusModule.{u, v} K)
    (N : FrobeniusModule.{t, v} K) :
    (Module.Dual K M.carrier →ₗ[K] N.carrier) ≃ₗ[K] M.carrier ⊗[K] N.carrier :=
  (dualTensorHomEquiv K (Module.Dual K M.carrier) N.carrier).symm ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv K M.carrier).symm (LinearEquiv.refl K N.carrier)

lemma homDualLinearEquiv_symm_tmul (M : FrobeniusModule.{u, v} K)
    (N : FrobeniusModule.{t, v} K) (x : M.carrier) (y : N.carrier)
    (φ : Module.Dual K M.carrier) : (homDualLinearEquiv M N).symm (x ⊗ₜ y) φ = φ x • y := by
  simp [homDualLinearEquiv]

/-- The Frobenius-equivariant isomorphism `Hom(M^∨, N) ≅ M ⊗ N`: `x ⊗ y` corresponds to the map
`φ ↦ φ(x) y`. -/
noncomputable def homDualEquiv (M N : FrobeniusModule.{max u v, v} K) :
    (M.dual.linearHom N).Equiv (M.tensor N) where
  toLinearEquiv := homDualLinearEquiv M N
  map_frobenius X := by
    have key (T : M.carrier ⊗[K] N.carrier) :
        (homDualLinearEquiv M N).symm ((M.tensor N).frobenius T) =
          (M.dual.linearHom N).frobenius ((homDualLinearEquiv M N).symm T) := by
      induction T using TensorProduct.inductionOn with
      | tmul x y =>
        refine LinearMap.ext fun φ ↦ ?_
        rw [tensor_frobenius_tmul, homDualLinearEquiv_symm_tmul, linearHom_frobenius_apply]
        simp [dual, homDualLinearEquiv_symm_tmul]
      | add T T' hT hT' => simp only [map_add, hT, hT']
    obtain ⟨T, rfl⟩ := (homDualLinearEquiv M N).symm.surjective X
    rw [← key]
    exact ((homDualLinearEquiv M N).apply_symm_apply _).trans
      (congrArg _ ((homDualLinearEquiv M N).apply_symm_apply T).symm)

/-- `homDualEquiv` sends the map `φ ↦ φ(x) y` to `x ⊗ y`. -/
lemma homDualEquiv_symm_tmul (M N : FrobeniusModule.{max u v, v} K) (x : M.carrier)
    (y : N.carrier) (φ : Module.Dual K M.carrier) :
    (show M.dual.carrier →ₗ[K] N.carrier from
      (homDualEquiv M N).toLinearEquiv.symm (x ⊗ₜ y)) φ =
      φ x • y :=
  homDualLinearEquiv_symm_tmul M N x y φ


/-- An isomorphism `P ≅ Hom(A, N)` together with `A ≅ M^∨` gives `P ≅ M ⊗ N`, through
`Hom(M^∨, N) ≅ M ⊗ N` (`FrobeniusModule.homDualEquiv`). -/
noncomputable def Equiv.tensorOfHomDual {P A M N : FrobeniusModule.{max u v, v} K}
    (e : P.Equiv (A.linearHom N)) (f : A.Equiv M.dual) : P.Equiv (M.tensor N) where
  toLinearEquiv := e.toLinearEquiv ≪≫ₗ
    (Equiv.homCongr f ⟨LinearEquiv.refl K N.carrier, fun x ↦ by
      rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply]⟩).toLinearEquiv ≪≫ₗ
    (homDualEquiv M N).toLinearEquiv
  map_frobenius x := by
    simp only [LinearEquiv.trans_apply, Equiv.map_frobenius]

/-- `a b` is an eigenvalue of the Frobenius of `M ⊗ N` if `a` is one of `M` and `b` one of `N`.
-/
theorem hasEigenvalue_tensor_mul {M : FrobeniusModule.{u, v} K} {N : FrobeniusModule.{t, v} K}
    {a b : K} (ha : M.frobeniusEnd.HasEigenvalue a) (hb : N.frobeniusEnd.HasEigenvalue b) :
    (M.tensor N).frobeniusEnd.HasEigenvalue (a * b) := by
  rw [frobeniusEnd_tensor]
  exact Module.End.hasEigenvalue_map_mul ha hb

/-- Over an algebraically closed field, the eigenvalues of the Frobenius of `M ⊗ N` are the
products of eigenvalues of `M` and of `N`. -/
theorem exists_of_hasEigenvalue_tensor [IsAlgClosed K] {M : FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{t, v} K} {μ : K} (h : (M.tensor N).frobeniusEnd.HasEigenvalue μ) :
    ∃ a b, M.frobeniusEnd.HasEigenvalue a ∧ N.frobeniusEnd.HasEigenvalue b ∧ μ = a * b := by
  rw [frobeniusEnd_tensor] at h
  exact Module.End.exists_hasEigenvalue_mul_of_hasEigenvalue_map M.frobenius N.frobeniusEnd h

/-- Weights at most `w` and `w'` give weights at most `w + w'` on the tensor product. -/
theorem HasWeightsAtMost.tensor [IsAlgClosed K] {ι : K →+* ℂ} {q : ℕ} (hq : 0 < q)
    {M : FrobeniusModule.{u, v} K} {N : FrobeniusModule.{t, v} K} {w w' : ℝ}
    (hM : M.HasWeightsAtMost ι q w) (hN : N.HasWeightsAtMost ι q w') :
    (M.tensor N).HasWeightsAtMost ι q (w + w') := by
  intro μ hμ
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_of_hasEigenvalue_tensor hμ
  rw [map_mul, norm_mul, add_div, Real.rpow_add (by exact_mod_cast hq)]
  exact mul_le_mul (hM a ha) (hN b hb) (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-- The tensor product of modules pure of weights `w` and `w'` is pure of weight `w + w'`. -/
theorem IsPureOfWeight.tensor [IsAlgClosed K] {ι : K →+* ℂ} {q : ℕ} (hq : 0 < q)
    {M : FrobeniusModule.{u, v} K} {N : FrobeniusModule.{t, v} K} {w w' : ℝ}
    (hM : M.IsPureOfWeight ι q w) (hN : N.IsPureOfWeight ι q w') :
    (M.tensor N).IsPureOfWeight ι q (w + w') := by
  intro μ hμ
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_of_hasEigenvalue_tensor hμ
  rw [map_mul, norm_mul, add_div, Real.rpow_add (by exact_mod_cast hq), hM a ha, hN b hb]

end FrobeniusModule
