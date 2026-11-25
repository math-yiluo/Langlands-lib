/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.RingTheory.Flat.Basic

/-! # Cycle formula on the homology of a free resolution

Source: Stacks Project, Algebra, Tags 00M5 and 00M6.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

private theorem cycleMap_of_exact
    {R : Type u} [CommRing R]
    {A₀ B₀ C₀ A₁ B₁ C₁ Z T : Type u}
    [AddCommGroup A₀] [Module R A₀] [AddCommGroup B₀] [Module R B₀]
    [AddCommGroup C₀] [Module R C₀] [AddCommGroup A₁] [Module R A₁]
    [AddCommGroup B₁] [Module R B₁] [AddCommGroup C₁] [Module R C₁]
    [AddCommGroup Z] [Module R Z] [AddCommGroup T] [Module R T]
    (s₀ : A₀ →ₗ[R] B₀) (q₀ : B₀ →ₗ[R] C₀)
    (s₁ : A₁ →ₗ[R] B₁) (q₁ : B₁ →ₗ[R] C₁)
    (da : A₁ →ₗ[R] A₀) (db : B₁ →ₗ[R] B₀) (dc : C₁ →ₗ[R] C₀)
    (i : Z →ₗ[R] C₁) (μ : A₀ →ₗ[R] T)
    (hs₀ : Function.Injective s₀)
    (he₀ : ∀ b, q₀ b = 0 ↔ ∃ a, s₀ a = b)
    (he₁ : ∀ b, q₁ b = 0 ↔ ∃ a, s₁ a = b)
    (hq₁ : Function.Surjective q₁)
    (hd₀ : ∀ a, db (s₁ a) = s₀ (da a))
    (hd₁ : ∀ b, q₀ (db b) = dc (q₁ b))
    (hi : ∀ z, dc (i z) = 0) (hμ : ∀ a, μ (da a) = 0) :
    ∃ δ : Z →ₗ[R] T, ∀ z b a, q₁ b = i z → s₀ a = db b → δ z = μ a := by
  classical
  choose b hb using fun z ↦ hq₁ (i z)
  have ha_exists : ∀ z, ∃ a, s₀ a = db (b z) := by
    intro z
    apply (he₀ _).mp
    rw [hd₁, hb, hi]
  choose a ha using ha_exists
  have compare : ∀ z b' a', q₁ b' = i z → s₀ a' = db b' → μ (a z) = μ a' := by
    intro z b' a' hb' ha'
    have hq : q₁ (b z - b') = 0 := by rw [map_sub, hb, hb', sub_self]
    obtain ⟨t, ht⟩ := (he₁ _).mp hq
    have hd : a z - a' = da t := hs₀ (by
      rw [map_sub, ha, ha', ← map_sub, ← ht, hd₀])
    have hm : μ (a z) - μ a' = 0 := by rw [← map_sub, hd, hμ]
    exact sub_eq_zero.mp hm
  let δ : Z →ₗ[R] T :=
    { toFun := fun z ↦ μ (a z)
      map_add' := by
        intro z w
        rw [compare (z + w) (b z + b w) (a z + a w)
          (by rw [map_add, hb, hb, map_add])
          (by rw [map_add, ha, ha, map_add]), map_add]
      map_smul' := by
        intro r z
        rw [compare (r • z) (r • b z) (r • a z)
          (by rw [map_smul, hb, map_smul])
          (by rw [map_smul, ha, map_smul]), map_smul]
        rfl }
  exact ⟨δ, compare⟩

/-- Source: Stacks Project, Algebra, proof of Tag 00M5 and Remark 00M6.
(blueprint: lem-weil-pbc-tor-ideal-homology-formula)

Proof in words: tensor the exact sequence of the ideal, ring and quotient with
all free resolution terms. Flatness gives injective ideal-tensor maps and right
exactness identifies their cokernels with the quotient-tensor terms. For a
quotient cycle lift y, choose an ideal-tensor preimage of d y. Send it to I ⊗ M
by tensor symmetry and the augmentation. Changing the ideal-tensor preimage
has no effect by injectivity, and changing the lift adds the differential of
an ideal tensor, killed by augmentation. This gives a linear map on cycles
which vanishes on boundaries, hence a linear map on homology. For a finite
expression d y = Σ a_j p_j, choose Σ p_j ⊗ a_j as preimage, giving the formula.
The construction also applies to the zero and unit ideals and the zero module.
-/
theorem exists_tor_ideal_homology_formula
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (hP : ∀ n : ℕ, Module.Free R (P.complex.X n))
    :
    ∃ δH : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology 1 →ₗ[R] (I ⊗[R] M),
      (∀ (z : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
        I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).cycles 1)
        (y : P.complex.X 1) (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
        ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) →
        P.complex.d 1 0 y = ∑ j, (a j : R) • p j →
        δH
          (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homologyπ 1 z) =
          ∑ j, a j ⊗ₜ[R] P.π.f 0 (p j)) := by
  classical
  let F := (tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))
  let C := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let s₀ := I.subtype.lTensor (P.complex.X 0)
  let q₀ := I.mkQ.lTensor (P.complex.X 0)
  let s₁ := I.subtype.lTensor (P.complex.X 1)
  let q₁ := I.mkQ.lTensor (P.complex.X 1)
  let da := (P.complex.d 1 0).hom.rTensor I
  let db := (P.complex.d 1 0).hom.rTensor R
  let μ := (TensorProduct.comm R M I).toLinearMap.comp ((P.π.f 0).hom.rTensor I)
  have hs₀ : Function.Injective s₀ := by
    let := hP 0
    exact Module.Flat.lTensor_preserves_injective_linearMap I.subtype Subtype.val_injective
  have he₀ : ∀ b, q₀ b = 0 ↔ ∃ a, s₀ a = b := by
    exact _root_.lTensor_exact (P.complex.X 0)
      (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
  have he₁ : ∀ b, q₁ b = 0 ↔ ∃ a, s₁ a = b := by
    exact _root_.lTensor_exact (P.complex.X 1)
      (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
  have hq₁ : Function.Surjective q₁ := LinearMap.lTensor_surjective _ I.mkQ_surjective
  have hd₀ : ∀ a, db (s₁ a) = s₀ (da a) := by
    intro a
    induction a using TensorProduct.inductionOn with
    | tmul p a => rfl
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  have hd₁ : ∀ b, q₀ (db b) = (C.d 1 0).hom (q₁ b) := by
    intro b
    induction b using TensorProduct.inductionOn with
    | tmul p r => rfl
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  have hi : ∀ z, (C.d 1 0).hom ((C.iCycles 1).hom z) = 0 := by
    intro z
    exact congrArg (fun f : C.cycles 1 ⟶ C.X 0 ↦ f z) (C.iCycles_d 1 0)
  have hμ : ∀ a, μ (da a) = 0 := by
    intro a
    induction a using TensorProduct.inductionOn with
    | tmul p a =>
      have hp : P.π.f 0 (P.complex.d 1 0 p) = 0 :=
        congrArg (fun f : P.complex.X 1 ⟶ M ↦ f p) P.complex_d_comp_π_f_zero
      change a ⊗ₜ[R] P.π.f 0 (P.complex.d 1 0 p) = 0
      rw [hp, TensorProduct.tmul_zero]
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  obtain ⟨δ, hδ⟩ := cycleMap_of_exact s₀ q₀ s₁ q₁ da db (C.d 1 0).hom
    (C.iCycles 1).hom μ hs₀ he₀ he₁ hq₁ hd₀ hd₁ hi hμ
  have formula : ∀ (z : C.cycles 1) (y : P.complex.X 1) (k : ℕ)
      (a : Fin k → I) (p : Fin k → P.complex.X 0),
      C.iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) →
      P.complex.d 1 0 y = ∑ j, (a j : R) • p j →
      δ z = ∑ j, a j ⊗ₜ[R] P.π.f 0 (p j) := by
    intro z y k a p hz hy
    have hq : q₁ (y ⊗ₜ[R] (1 : R)) = (C.iCycles 1).hom z := by
      change y ⊗ₜ[R] (1 : R ⧸ I) = C.iCycles 1 z
      exact hz.symm
    have hs : s₀ (∑ j, p j ⊗ₜ[R] a j) = db (y ⊗ₜ[R] (1 : R)) := by
      simp only [s₀, db, map_sum, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, hy]
      simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul,
        smul_eq_mul, mul_one]
      rfl
    rw [hδ z _ _ hq hs]
    simp [μ]
  have hboundary : C.toCycles 2 1 ≫ ofHom δ = 0 := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul p q =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      have hc : C.iCycles 1 (C.toCycles 2 1 (p ⊗ₜ[R] Ideal.Quotient.mk I r)) =
          (r • P.complex.d 2 1 p) ⊗ₜ[R] (1 : R ⧸ I) := by
        have ht := congrArg (fun f : C.X 2 ⟶ C.X 1 ↦
          f (p ⊗ₜ[R] Ideal.Quotient.mk I r)) (C.toCycles_i 2 1)
        change C.iCycles 1 (C.toCycles 2 1 (p ⊗ₜ[R] Ideal.Quotient.mk I r)) =
          P.complex.d 2 1 p ⊗ₜ[R] Ideal.Quotient.mk I r at ht
        have hr : r • (1 : R ⧸ I) = Ideal.Quotient.mk I r := by
          rw [Algebra.smul_def, mul_one]
          rfl
        rw [ht, TensorProduct.smul_tmul, hr]
      have hd : P.complex.d 1 0 (r • P.complex.d 2 1 p) = 0 := by
        have hp := congrArg (fun f : P.complex.X 2 ⟶ P.complex.X 0 ↦ f p)
          (P.complex.d_comp_d 2 1 0)
        change P.complex.d 1 0 (P.complex.d 2 1 p) = 0 at hp
        rw [map_smul, hp, smul_zero]
      simpa using formula _ _ 0 Fin.elim0 Fin.elim0 hc (by simp only [Fin.sum_univ_zero]; exact hd)
    | add a b ha hb => simp only [map_add, ha, hb]
  let δH : C.homology 1 ⟶ of R (I ⊗[R] M) :=
    (C.homologyIsCokernel 2 1 (by simp)).desc
      (CategoryTheory.Limits.CokernelCofork.ofπ (ofHom δ) hboundary)
  refine ⟨δH.hom, ?_⟩
  intro z y k a p hz hy
  have hdesc : δH.hom ((C.homologyπ 1).hom z) = δ z :=
    congrArg (fun f : C.cycles 1 ⟶ of R (I ⊗[R] M) ↦ f.hom z)
      (CategoryTheory.Limits.Cofork.IsColimit.π_desc
        (C.homologyIsCokernel 2 1 (by simp))
        (t := CategoryTheory.Limits.CokernelCofork.ofπ (ofHom δ) hboundary))
  exact hdesc.trans (formula z y k a p hz hy)

end ModuleCat
