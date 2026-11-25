/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Detecting cohomology vanishing on a finite standard-open cover

Source: Stacks Project, Tag 066D, proof, first paragraph, and Tag 00EO (1).
-/

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

attribute [local instance 2000] CommRing.toRing

open TensorProduct

/-- The tensor/extension comparison, with module universes larger than the rings.
This is the construction of `ModuleCat.tensorEquivExtendScalars` at arbitrary module
universe: send pure tensors to the same pure tensors for the restricted scalar action. -/
private noncomputable def tensorEquiv (R S : Type u₁) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{max u₁ v₁} R) :
    S ⊗[R] N ≃ₗ[S] (ModuleCat.extendScalars (algebraMap R S)).obj N := by
  let T := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let toFun : S ⊗[R] N →ₗ[R] TensorProduct R S' N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S' N s
        map_add' s s' := (TensorProduct.mk R S' N).map_add s s'
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S' N) (Algebra.smul_def r s)).trans
            ((TensorProduct.mk R S' N).map_smul r (s : S')) }
  let invFun : TensorProduct R S' N →ₗ[R] S ⊗[R] N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S N (show S from s)
        map_add' s s' := (TensorProduct.mk R S N).map_add (show S from s) (show S from s')
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S N) (Algebra.smul_def r (show S from s)).symm).trans
            ((TensorProduct.mk R S N).map_smul r (show S from s)) }
  have h₁ : ∀ x, invFun (toFun x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : ∀ x, toFun (invFun x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact
    { toFun := toFun
      invFun := invFun
      map_add' := toFun.map_add
      map_smul' s x := by
        induction x using TensorProduct.inductionOn with
        | tmul s' n => rfl
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add]
          exact (smul_add s _ _).symm
      left_inv := h₁
      right_inv := h₂ }

set_option backward.isDefEq.respectTransparency false in
/-- Localization at a unit-ideal generating family detects vanishing of one cohomology module.
Source: Stacks Project, Tag 066D, proof, first paragraph, using Algebra, Tag 00EO (1).
(blueprint: lem-pc-homology-vanishing-localization-span).

Proof: Localization is exact, so the homology of the termwise extension of scalars is
canonically the localization of the homology of `M`. Thus the hypothesis says that every
localization of `Hⁿ(M)` at an `f i` is zero. For an element `x` of `Hⁿ(M)`, the zero criterion
for localized modules gives exponents `e i` with `(f i) ^ (e i)` annihilating `x`. The powers
still generate the unit ideal: the radical of their ideal contains every `f i`, and hence
contains 1. Express 1 as a linear combination of these powers and act on `x`, obtaining
`x = 0`. Hence `Hⁿ(M)` is a zero object. The empty family forces the zero ring and the
same conclusion. -/
theorem homology_vanishes_of_localization_span
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁} (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤)
    (n : ℤ)
    (hlocal : ∀ i : Fin r,
      IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} (Localization.Away (f i))) n).obj
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M)))) :
    IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} A) n).obj (Q.obj M)) := by
  classical
  let H := M.homology n
  have hzero (i : Fin r) :
      IsZero ((ModuleCat.extendScalars (algebraMap A (Localization.Away (f i)))).obj H) := by
    let F : ModuleCat.{max u₁ v₁} A ⥤
        ModuleCat.{max u₁ v₁} (Localization.Away (f i)) :=
      ModuleCat.extendScalars (algebraMap A (Localization.Away (f i)))
    have : F.Additive := ⟨by
        intro X Y g h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul s x => simp [F, ModuleCat.ExtendScalars.map_tmul, TensorProduct.tmul_add]
        | add z z' hz hz' => simp only [map_add, hz, hz']⟩
    have : F.PreservesHomology := by
      apply ((Functor.exact_tfae F).out 2 3).mp
      intro S hS
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
      have := IsLocalization.flat (Localization.Away (f i)) (Submonoid.powers (f i))
      have hex := Module.Flat.lTensor_exact (Localization.Away (f i)) hS
      let e₁ := tensorEquiv A (Localization.Away (f i)) S.X₁
      let e₂ := tensorEquiv A (Localization.Away (f i)) S.X₂
      let e₃ := tensorEquiv A (Localization.Away (f i)) S.X₃
      have comm {X Y : ModuleCat.{max u₁ v₁} A} (g : X ⟶ Y) (x) :
          tensorEquiv A (Localization.Away (f i)) Y
              (g.hom.lTensor (Localization.Away (f i)) x) =
            F.map g (tensorEquiv A (Localization.Away (f i)) X x) := by
        induction x using TensorProduct.inductionOn with
        | tmul s x => rfl
        | add x y hx hy => simp only [map_add, hx, hy]
      change Function.Exact (F.map S.f).hom (F.map S.g).hom
      intro y
      constructor
      · intro hy
        have hy' : (S.g.hom.lTensor (Localization.Away (f i))) (e₂.symm y) = 0 := by
          apply e₃.injective
          rw [map_zero, comm]
          simpa only [e₂, e₃, LinearEquiv.apply_symm_apply] using hy
        obtain ⟨x, hx⟩ := (hex (e₂.symm y)).mp hy'
        refine ⟨e₁ x, ?_⟩
        change F.map S.f (tensorEquiv A (Localization.Away (f i)) S.X₁ x) = y
        rw [← comm, hx]
        exact e₂.apply_symm_apply y
      · rintro ⟨x, rfl⟩
        change (S.map F).g ((S.map F).f x) = 0
        exact (S.map F).zero_apply x
    let e := (homologyFunctorFactors
      (ModuleCat.{max u₁ v₁} (Localization.Away (f i))) n).app
        ((F.mapHomologicalComplex (.up ℤ)).obj M) ≪≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) n).app M
    exact e.isZero_iff.mp (hlocal i)
  have hH : IsZero H := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro x
    apply Module.eq_zero_of_isLocalized_span (Set.range f) hf
      (fun a ↦ Localization.Away a.1 ⊗[A] H)
      (fun a ↦ TensorProduct.mk A (Localization.Away a.1) H 1) x
    intro a
    obtain ⟨i, hi⟩ := a.2
    rcases a with ⟨a, ha⟩
    dsimp at hi ⊢
    subst a
    have hs := ModuleCat.subsingleton_of_isZero (hzero i)
    let e := tensorEquiv A (Localization.Away (f i)) H
    apply e.injective
    exact hs.elim _ _
  exact ((homologyFunctorFactors (ModuleCat.{max u₁ v₁} A) n).app M).isZero_iff.mpr hH

end DerivedCategory
