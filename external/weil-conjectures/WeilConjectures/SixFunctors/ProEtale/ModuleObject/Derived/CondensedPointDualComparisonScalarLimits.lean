/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarExact
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Exactness of copower scalar extension at a geometric point -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Scalar extension preserves finite-limit. The copower adjunction and split vector-space
sequences give the finite-limit conclusion (blueprint: lem-a1-condensed-point-scalar-limits). -/
theorem condensed_point_scalar_limits :
    PreservesFiniteLimits (condensedPointScalarExtension ℓ k)  := by
  let F := condensedPointScalarExtension ℓ k
  have : F.Additive := condensed_point_scalar_additive ℓ k
  have : F.IsLeftAdjoint := (condensedPointScalarAdjunction ℓ k).isLeftAdjoint
  have : F.PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    obtain ⟨r, hr⟩ := f.hom.exists_leftInverse_of_injective
      ((ModuleCat.mono_iff_ker_eq_bot f).mp hf)
    have hfr : f ≫ ModuleCat.ofHom r = 𝟙 X := by
      ext x
      exact DFunLike.congr_fun hr x
    exact mono_of_mono_fac (show F.map f ≫ F.map (ModuleCat.ofHom r) = 𝟙 (F.obj X) by
      rw [← F.map_comp, hfr, F.map_id])
  have : F.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels F
  exact Functor.preservesFiniteLimits_of_preservesHomology F

end AlgebraicGeometry.ProEtale.CondensedRing
