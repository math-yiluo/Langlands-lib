/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Symmetric algebras and base change

Source: Stacks Project, Algebra, Lemma 0C6F and the universal properties of symmetric
algebras and extension of scalars (blueprint: lem-weil-pbc-symmetric-algebra-base-change).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace SymmetricAlgebra

/-- The canonical base-change map for the symmetric algebra is an isomorphism.
Source: Stacks Project, Algebra, Lemma 0C6F, generalized by the universal properties
(blueprint: lem-weil-pbc-symmetric-algebra-base-change).

Proof: (1) The symmetric-algebra universal property
(lem-weil-pbc-symmetric-algebra-universal-property) constructs the unique `β` from the
linear map `m ↦ ι S (S ⊗[R] M) (1 ⊗ₜ m)`.
(2) The algebra base-change universal property
(lem-weil-pbc-algebra-tensor-base-change-universal-property) extends `β` to the displayed
`S`-algebra map, sending `s ⊗ₜ a` to `s • β a`.
(3) The module base-change universal property
(lem-weil-pbc-module-base-change-universal-property) extends `m ↦ 1 ⊗ₜ ι R M m` to
an `S`-linear map sending `s ⊗ₜ m` to `s ⊗ₜ ι R M m`. Extend this again by the
symmetric-algebra universal property to obtain the inverse algebra map.
(4) The forward map after the inverse is the identity on all degree-one generators;
symmetric-algebra uniqueness makes it the identity everywhere.
(5) For the other composite, algebra base-change uniqueness reduces to comparing maps
on `SymmetricAlgebra R M`; symmetric-algebra uniqueness reduces this to the generators,
where both maps send `ι R M m` to `1 ⊗ₜ ι R M m`. Thus both composites are identities. -/
theorem baseChange_bijective
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
    (β : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra S (S ⊗[R] M))
    (hβ : ∀ m : M, β (ι R M m) = ι S (S ⊗[R] M) (1 ⊗ₜ[R] m)) :
    Function.Bijective
      (AlgHom.liftEquiv R S (SymmetricAlgebra R M)
        (SymmetricAlgebra S (S ⊗[R] M)) β) := by
  let Φ := AlgHom.liftEquiv R S (SymmetricAlgebra R M)
    (SymmetricAlgebra S (S ⊗[R] M)) β
  let j : M →ₗ[R] S ⊗[R] SymmetricAlgebra R M :=
    Algebra.TensorProduct.includeRight.toLinearMap.comp (ι R M)
  let Ψ : SymmetricAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] SymmetricAlgebra R M :=
    lift (j.liftBaseChange S)
  have hΨ : ∀ s m, Ψ (ι S (S ⊗[R] M) (s ⊗ₜ[R] m)) =
      s ⊗ₜ[R] ι R M m := by
    intro s m
    simp [Ψ, j, TensorProduct.smul_tmul']
  have hright : Φ.comp Ψ = AlgHom.id S _ := by
    apply algHom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
      change Φ (Ψ (ι S (S ⊗[R] M) (s ⊗ₜ[R] m))) =
        ι S (S ⊗[R] M) (s ⊗ₜ[R] m)
      rw [hΨ, AlgHom.liftEquiv_tmul, hβ]
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  have hleft : Ψ.comp Φ = AlgHom.id S _ := by
    apply Algebra.TensorProduct.ext_ring
    apply algHom_ext
    apply LinearMap.ext
    intro m
    simp [Φ, hβ, hΨ]
  exact ⟨(show Function.LeftInverse Ψ Φ from fun x ↦ DFunLike.congr_fun hleft x).injective,
    (show Function.RightInverse Ψ Φ from fun x ↦ DFunLike.congr_fun hright x).surjective⟩

/-- The principal localization of a symmetric algebra is the symmetric algebra of the
localized module over the localized ring.
Source: Stacks Project, Algebra, Lemma 0C6F
(blueprint: lem-weil-pbc-symmetric-algebra-base-change).

Proof: (6) Specialize the base-change isomorphism to `S = Localization.Away f`.
Use the algebra and module tensor-localization identifications
(lem-weil-pbc-localization-tensor), namely `IsLocalization.Away.tensorRightEquiv` and
`LocalizedModule.equivTensorProduct`, to identify its source with the localization of
`SymmetricAlgebra R M` at the image of the powers of `f`, and its degree-one module
with `LocalizedModule (Submonoid.powers f) M`. Under these identifications the comparison
is exactly the stated localization isomorphism. The image submonoid is exactly the powers
of `algebraMap R (SymmetricAlgebra R M) f`. -/
theorem exists_away_baseChange
    {R : Type u} {M : Type w} [CommRing R] [AddCommGroup M] [Module R M] (f : R) :
    Nonempty (Localization
        (Algebra.algebraMapSubmonoid (SymmetricAlgebra R M) (Submonoid.powers f))
        ≃ₐ[Localization.Away f]
        SymmetricAlgebra (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) := by
  let S := Localization.Away f
  let N := LocalizedModule (Submonoid.powers f) M
  let k : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
  let β : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra S (S ⊗[R] M) :=
    lift ((ι S (S ⊗[R] M)).restrictScalars R |>.comp k)
  have hβ : ∀ m : M, β (ι R M m) = ι S (S ⊗[R] M) (1 ⊗ₜ[R] m) := by
    intro m
    simp [β, k]
  let e₁ := AlgEquiv.ofBijective
    (AlgHom.liftEquiv R S (SymmetricAlgebra R M)
      (SymmetricAlgebra S (S ⊗[R] M)) β) (baseChange_bijective β hβ)
  let e := (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm
  let g : SymmetricAlgebra S (S ⊗[R] M) →ₐ[S] SymmetricAlgebra S N :=
    lift ((ι S N).comp e.toLinearMap)
  let h : SymmetricAlgebra S N →ₐ[S] SymmetricAlgebra S (S ⊗[R] M) :=
    lift ((ι S (S ⊗[R] M)).comp e.symm.toLinearMap)
  have hgh : g.comp h = AlgHom.id S _ := by
    apply algHom_ext
    apply LinearMap.ext
    intro x
    change g (h (ι S N x)) = ι S N x
    simp only [g, h, lift_ι_apply, LinearMap.comp_apply]
    exact congrArg (ι S N) (e.apply_symm_apply x)
  have hhg : h.comp g = AlgHom.id S _ := by
    apply algHom_ext
    apply LinearMap.ext
    intro x
    change h (g (ι S (S ⊗[R] M) x)) = ι S (S ⊗[R] M) x
    simp only [g, h, lift_ι_apply, LinearMap.comp_apply]
    exact congrArg (ι S (S ⊗[R] M)) (e.symm_apply_apply x)
  let e₂ := AlgEquiv.ofAlgHom g h hgh hhg
  exact ⟨(Localization.tensorRightAlgEquiv (Submonoid.powers f)
    (SymmetricAlgebra R M)).symm.trans (e₁.trans e₂)⟩


end SymmetricAlgebra
