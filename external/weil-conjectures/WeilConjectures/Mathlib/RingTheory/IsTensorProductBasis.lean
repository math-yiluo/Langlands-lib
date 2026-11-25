/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Base change along a free algebra, in coordinates

For an `R`-algebra `S` with a finite basis `b`, an `R`-linear map `f : M → N` to an `S`-module
is a base change iff `g ↦ ∑ i, b i • f (g i)` is bijective.
-/

@[expose] public section

open TensorProduct

/-- For a free `R`-algebra `S` with finite basis `b`, an `R`-linear map `f : M → N` to an
`S`-module is a base change iff `g ↦ ∑ i, b i • f (g i)` is bijective. -/
theorem IsBaseChange.iff_bijective_sum_basis_smul {R S M N ι : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] (f : M →ₗ[R] N) [Fintype ι] (b : Module.Basis ι R S) :
    IsBaseChange S f ↔ Function.Bijective fun g : ι → M ↦ ∑ i, b i • f (g i) := by
  classical
  let e : (ι → M) ≃ₗ[R] S ⊗[R] M :=
    (Finsupp.linearEquivFunOnFinite R M ι).symm ≪≫ₗ
      (TensorProduct.equivFinsuppOfBasisLeft b).symm
  have h : (fun g : ι → M ↦ ∑ i, b i • f (g i)) =
      TensorProduct.lift
        (((Algebra.linearMap S <| Module.End S (M →ₗ[R] N)).flip f).restrictScalars R) ∘
          e := by
    funext g
    simp [e, Finsupp.sum_fintype]
  rw [h, Function.Bijective.of_comp_iff _ e.bijective]
  rfl

/-- Let `S` be a free `R`-algebra with basis `β`, and let `e : H → H'` be an `R`-linear map to
an `S`-module such that `h ↦ ∑ i, β i • e (h i)` is bijective. Let `A` be an
`R`-algebra and `B` an `S`-algebra and `A`-algebra compatibly, with `v` an `A`-basis of `B`.
Then for the map `Θ : A ⊗[R] H → B ⊗[S] H'`, `a ⊗ x ↦ a ⊗ e x`, the map
`g ↦ ∑ k, v k • Θ (g k)` is bijective. -/
theorem TensorProduct.bijective_sum_smul_of_bijective_sum_basis_smul
    {R S A B H H' ι κ : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] [Algebra A B] [Algebra R B]
    [IsScalarTower R S B] [IsScalarTower R A B]
    [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module S H'] [Module R H']
    [IsScalarTower R S H'] (e : H →ₗ[R] H') [Fintype ι] [Fintype κ]
    (β : Module.Basis ι R S)
    (hβ : Function.Bijective fun h : ι → H ↦ ∑ i, β i • e (h i))
    (v : κ → B) (hv : Function.Bijective fun c : κ → A ↦ ∑ k, c k • v k)
    (Θ : A ⊗[R] H →+ B ⊗[S] H')
    (hΘ : ∀ a x, Θ (a ⊗ₜ x) = algebraMap A B a ⊗ₜ e x) :
    Function.Bijective fun g : κ → A ⊗[R] H ↦ ∑ k, v k • Θ (g k) := by
  let Θ' : A ⊗[R] H →ₗ[A] B ⊗[S] H' :=
    { Θ with
      map_smul' := fun a z ↦ by
        simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
        induction z using TensorProduct.inductionOn with
        | tmul a' x =>
          rw [TensorProduct.smul_tmul', hΘ, hΘ, smul_eq_mul,
            map_mul, TensorProduct.smul_tmul', _root_.Algebra.smul_def a]
        | add z w hz hw => rw [smul_add, map_add, map_add, hz, hw, smul_add] }
  have h1 : IsBaseChange S e := (IsBaseChange.iff_bijective_sum_basis_smul e β).2 hβ
  have h2 := h1.comp (TensorProduct.isBaseChange S H' B)
  have h3 : IsBaseChange B Θ' := by
    refine (TensorProduct.isBaseChange R H A).comp_iff.1 ?_
    convert h2 using 1
    ext x
    simp [Θ', hΘ]
  have hvb : Function.Bijective (Fintype.linearCombination A v) := by
    convert hv using 1
    funext c
    exact Fintype.linearCombination_apply A v c
  let vb : Module.Basis κ A B :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ hvb).symm
  have hvb' : ⇑vb = v := by
    funext k
    classical
    simp [vb, Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply, Pi.single_apply]
  have := (IsBaseChange.iff_bijective_sum_basis_smul Θ' vb).1 h3
  rw [hvb'] at this
  exact this
