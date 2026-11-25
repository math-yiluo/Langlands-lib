/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.RingTheory.Jacobson.Semiprimary
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Reduction of the coefficient sheaf to sheaves killed by the Jacobson radical

For a commutative square `h ≫ f' = e ≫ g` and `M ∈ D(X'_ét, Λ)`, `Λ` a finite ring with Jacobson
radical `J`, the base change map `M ⊗ᴸ Lf'^* Rg_* 𝓕 ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* 𝓕)` is an isomorphism
for every sheaf `𝓕` placed in degree `0` as soon as it is for the sheaves killed by `J`
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_singleFunctor_of_smul_eq_zero`): `J` is
nilpotent, a sheaf `𝓕` killed by `J^{m+1}` is an extension of a sheaf killed by `J^m` by the
subsheaf `𝓕[J]` killed by `J`, and both sides are triangulated functors of `𝓕`. This is the
reduction to prime torsion of the proof of blueprint `lemma-kunneth-field-coefficients--1`, for a
general finite `Λ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The map `𝓕 ⟶ ⨁_{x ∈ I} 𝓕` given by the multiplications by the elements of a finite ideal. -/
noncomputable def smulLift {C : Type*} [Category C] [Preadditive C] [Linear Λ C]
    [HasFiniteBiproducts C] (I : Ideal Λ) [Finite I] (F : C) :
    F ⟶ ⨁ fun _ : I ↦ F :=
  biproduct.lift fun x ↦ (x : Λ) • 𝟙 F

/-- The kernel of `AlgebraicGeometry.Etale.smulLift`, the subobject killed by `I`, is killed by
`I`. -/
lemma smul_id_kernel_smulLift {C : Type*} [Category C] [Abelian C] [Linear Λ C]
    (I : Ideal Λ) [Finite I] (F : C) {x : Λ} (hx : x ∈ I) :
    x • 𝟙 (kernel (smulLift I F)) = 0 := by
  have h2 := kernel.condition (smulLift I F) =≫ biproduct.π _ ⟨x, hx⟩
  rw [Category.assoc, smulLift, biproduct.lift_π, zero_comp, Linear.comp_smul,
    Category.comp_id] at h2
  rw [← cancel_mono (kernel.ι (smulLift I F)), zero_comp, Linear.smul_comp, Category.id_comp]
  exact h2

/-- If `F` is killed by `I^{m+1}`, the cokernel of the inclusion of the subobject killed by `I` is
killed by `I^m`. -/
lemma smul_id_cokernel_kernel_smulLift {C : Type*} [Category C] [Abelian C] [Linear Λ C]
    (I : Ideal Λ) [Finite I] (F : C) (m : ℕ) (hF : ∀ x ∈ I ^ (m + 1), x • 𝟙 F = 0) {x : Λ}
    (hx : x ∈ I ^ m) :
    x • 𝟙 (cokernel (kernel.ι (smulLift I F))) = 0 := by
  have hl : (x • 𝟙 F) ≫ smulLift I F = 0 := by
    ext y
    simp only [smulLift, biproduct.lift_π, zero_comp, Linear.smul_comp,
      Category.id_comp, smul_smul]
    exact hF _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hx y.2)
  rw [← cancel_epi (cokernel.π (kernel.ι (smulLift I F))), comp_zero, Linear.comp_smul,
    Category.comp_id, ← Category.id_comp (cokernel.π _), ← Linear.smul_comp,
    ← kernel.lift_ι _ _ hl, Category.assoc, cokernel.condition, comp_zero]

variable [Finite Λ]

/-- **Reduction to coefficients killed by the Jacobson radical.** If the base change map
`M ⊗ᴸ Lf'^* Rg_* 𝓕 ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* 𝓕)` is an isomorphism for every sheaf `𝓕` killed by the
Jacobson radical of the finite ring `Λ`, it is an isomorphism for every sheaf `𝓕`. -/
theorem isIso_tensorBaseChangeMap_singleFunctor_of_smul_eq_zero {X' S' T Y : Scheme.{u}}
    (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hJ : ∀ 𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      (∀ x ∈ Ring.jacobson Λ, x • 𝟙 𝓕 = 0) →
        IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w M
          ((DerivedCategory.singleFunctor _ 0).obj 𝓕)))
    (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w M
      ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) := by
  let τ := tensorBaseChangeMapRight (ModuleCat.{u + 1} Λ) h e f' g w M
  obtain ⟨n, hn⟩ := (IsSemiprimaryRing.isNilpotent : IsNilpotent (Ring.jacobson Λ))
  suffices H : ∀ (m : ℕ) (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∀ x ∈ Ring.jacobson Λ ^ m, x • 𝟙 𝓕 = 0) →
        IsIso (τ.app ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) from
    H n 𝓕 fun x hx ↦ by
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
      rw [hx, zero_smul]
  intro m
  induction m with
  | zero =>
    intro 𝓕 h𝓕
    have h0 : IsZero 𝓕 := by
      rw [IsZero.iff_id_eq_zero, ← one_smul Λ (𝟙 𝓕)]
      exact h𝓕 1 (by simp)
    have hs := (DerivedCategory.singleFunctor _ 0).map_isZero h0
    exact ⟨0, ((R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ L((f')^*[ModuleCat.{u + 1} Λ]) ⋙
      (-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).obj M).map_isZero hs).eq_of_src _ _,
      ((L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ (-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj
        (L((h)^*[ModuleCat.{u + 1} Λ]).obj M) ⋙ R((h)_*[ModuleCat.{u + 1} Λ])).map_isZero
          hs).eq_of_src _ _⟩
  | succ m ih =>
    intro 𝓕 h𝓕
    let ι := kernel.ι (smulLift (Ring.jacobson Λ) 𝓕)
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι) }
    refine NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃ τ (hS.singleTriangle_distinguished) ?_ ?_
    · exact hJ _ fun x hx ↦ smul_id_kernel_smulLift _ 𝓕 hx
    · exact ih _ fun x hx ↦ smul_id_cokernel_kernel_smulLift _ 𝓕 m h𝓕 hx

end Etale

end AlgebraicGeometry
