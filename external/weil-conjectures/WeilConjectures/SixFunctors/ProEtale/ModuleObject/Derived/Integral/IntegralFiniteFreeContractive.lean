/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.LinearAlgebra.Matrix.Ideal

/-! # Contractive matrices over integral coefficient sheaves

Source: Bhatt--Scholze, Section 6.8, integral Nakayama argument.
(blueprint: lem-weil-pbc-integral-finite-free-contractive)
-/

@[expose] public section

universe u v w

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency.types false in
private theorem jacUnit {R : Type*} [Ring R] {x : R}
    (hx : x ∈ (⊥ : TwoSidedIdeal R).jacobson) : IsUnit (1 - x) := by
  obtain ⟨z, hz⟩ := TwoSidedIdeal.mem_jacobson_iff.mp hx (-1)
  have hz' : z * (1 - x) = 1 := by
    rw [TwoSidedIdeal.mem_bot, sub_eq_zero, mul_neg_one, neg_mul] at hz
    rw [mul_sub, mul_one]
    simpa only [sub_eq_add_neg, add_comm] using hz
  have hzJ : z - 1 ∈ (⊥ : TwoSidedIdeal R).jacobson := by
    have hzx : z * x ∈ (⊥ : TwoSidedIdeal R).jacobson :=
      TwoSidedIdeal.mul_mem_left _ _ _ hx
    have hEq : z - 1 = z * x := by
      have := hz'
      rw [mul_sub, mul_one] at this
      rw [sub_eq_iff_eq_add] at this ⊢
      simpa only [add_comm] using this
    rw [hEq]
    exact hzx
  obtain ⟨w, hw⟩ := TwoSidedIdeal.mem_jacobson_iff.mp hzJ 1
  have hw' : w * z = 1 := by
    simpa only [TwoSidedIdeal.mem_bot, mul_one, mul_sub, sub_add_cancel,
      sub_eq_zero] using hw
  have hright : (1 - x) * z = 1 := by
    calc
      (1 - x) * z = (w * z) * ((1 - x) * z) := by rw [hw', one_mul]
      _ = w * (z * (1 - x)) * z := by simp only [mul_assoc]
      _ = 1 := by rw [hz', mul_one, hw']
  exact ⟨⟨1 - x, z, hright, hz'⟩, rfl⟩

variable {C : Type v} [Category.{w} C] [Preadditive C] [HasFiniteBiproducts C]

private noncomputable def matrixEnd (A : C) (n : Type) [Fintype n] [DecidableEq n] :
    Matrix n n (End A) →+* End (⨁ fun _ : n => A) where
  toFun M := .of (biproduct.matrix fun i j => (M j i).asHom)
  map_zero' := by
    apply End.ext
    ext
    simp [biproduct.matrix]
  map_one' := by
    apply End.ext
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, eq_comm]
  map_add' M N := by
    apply End.ext
    change biproduct.matrix (fun i j => ((M + N) j i).asHom) =
      biproduct.matrix (fun i j => (M j i).asHom) +
        biproduct.matrix (fun i j => (N j i).asHom)
    ext
    simp
  map_mul' M N := by
    apply End.ext
    change biproduct.matrix (fun i j => ((M * N) j i).asHom) =
      biproduct.matrix (fun i j => (N j i).asHom) ≫
        biproduct.matrix (fun i j => (M j i).asHom)
    ext i j
    simp only [biproduct.ι_matrix_assoc, biproduct.matrix_π,
      biproduct.lift_desc, Matrix.mul_apply, End.sum_asHom, End.mul_asHom, Category.assoc,
      biproduct.ι_desc]

private theorem finiteFreeContractive {A : C} (n : Type) [Finite n]
    (p : ℕ) (h : ∀ f : End A, IsIso ((1 - p • f : End A).asHom))
    (T : End (⨁ fun _ : n => A)) : IsIso ((1 - p • T : End (⨁ fun _ : n => A)).asHom) := by
  classical
  let := Fintype.ofFinite n
  have hp : (p : End A) ∈ (⊥ : TwoSidedIdeal (End A)).jacobson := by
    rw [TwoSidedIdeal.mem_jacobson_iff]
    intro y
    have hu : IsUnit (1 - p • (-y)) := (isUnit_iff_isIso _).mpr (h (-y))
    obtain ⟨z, hz⟩ := hu.exists_left_inv
    refine ⟨z, ?_⟩
    simp only [TwoSidedIdeal.mem_bot]
    have heq : (1 - p • (-y)) = 1 + y * (p : End A) := by
      simp only [nsmul_eq_mul, Nat.cast_comm, neg_mul, sub_neg_eq_add]
    rw [heq, mul_add, mul_one] at hz
    exact sub_eq_zero.mpr (by simpa only [mul_assoc, add_comm] using hz)
  let M : Matrix n n (End A) := fun j i => .of (biproduct.components T.asHom i j)
  have hM : p • M ∈ (⊥ : TwoSidedIdeal (Matrix n n (End A))).jacobson := by
    rw [← TwoSidedIdeal.matrix_jacobson_bot]
    rw [TwoSidedIdeal.mem_matrix]
    intro i j
    change p • M i j ∈ _
    simpa only [nsmul_eq_mul] using
      TwoSidedIdeal.mul_mem_right (⊥ : TwoSidedIdeal (End A)).jacobson (p : End A) (M i j) hp
  have hu := (jacUnit hM).map (matrixEnd A n)
  have heq : matrixEnd A n (1 - p • M) = (1 - p • T : End (⨁ fun _ : n => A)) := by
    rw [map_sub, map_one, map_nsmul]
    congr 1
    exact congrArg (p • ·) (End.ext (biproduct.components_matrix T.asHom))
  rw [heq] at hu
  exact (isUnit_iff_isIso _).mp hu

namespace AlgebraicGeometry.ProEtale.CondensedRing

open MonoidalCategory MonObj

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- One minus ℓ times an endomorphism of a finite free integral module is invertible.
Source: Bhatt--Scholze, Section 6.8, integral Nakayama argument.
(blueprint: lem-weil-pbc-integral-finite-free-contractive)

Proof: the rank-one assertion says that ℓ belongs to the Jacobson radical of
End(R). Matrix Jacobson radicals are computed entrywise, so the matrix ℓT belongs
to the radical of the matrix endomorphism ring. One minus a radical element is a unit.
The biproduct matrix construction is a ring homomorphism from matrices over End(R)
to End(R^n), and sends this unit to the asserted endomorphism. Rank zero is included. -/
theorem integralFiniteFree_one_sub_nsmul_isIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (e : R ⟶ condensedRingObj (integralCoeff ℓ E) X) [IsMonHom e] [IsIso e]
    (n : ℕ) (T : Mod.finiteFree R n ⟶ Mod.finiteFree R n) :
    IsIso (𝟙 _ - ℓ • T) := by
  exact finiteFreeContractive (A := Mod.regular R) (Fin n) ℓ
    (fun f => integralRegular_one_sub_nsmul_isIso ℓ E X R e f.asHom) (.of T)

end AlgebraicGeometry.ProEtale.CondensedRing
