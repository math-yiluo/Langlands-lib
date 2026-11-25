/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.Algebra.Homology.HomComplexComponents

/-! # Naturality for the recorded Hom-complex projections -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t u
open CategoryTheory Opposite
namespace WeilConjectures.IntegralHom
attribute [local implicit_reducible] homComplex projection
attribute [local irreducible] homComplexFunctor

private theorem projection_eq_π
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (A I : CochainComplex (Modules.{t, u} Y R) ℤ) (n p : ℤ) :
    projection Y R A I n p = (by
      exact homComplexπ.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := R) A I n p (p + n) rfl) := by
  rfl

/-- Postcomposition on the Hom complex commutes with its recorded projections.

Source: Stacks 0A8X and the product-projection naturality in HomComplexComponents
(blueprint: lem-sf-integral-hom-projection-naturality).

Proof: the projection in IntegralHomReductionModels and homComplexπ choose the
same projection family from homComplex_projections_exists. Identify them and
apply homComplexFunctor_obj_map_f_π. No boundedness or injectivity is used. -/
theorem homProjection_map
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (A I I' : CochainComplex (Modules.{t, u} Y R) ℤ) (g : I ⟶ I') (n p : ℤ) :
    (((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := R)).obj (op A)).map g).f n ≫ projection Y R A I' n p =
      projection Y R A I n p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (A.X p)) (g.f (p + n)) := by
  have h := homComplexFunctor_obj_map_f_π.{t + 1, t, max u (t + 1), max u (t + 1)}
    (R := R) (L := A) g n p (p + n) rfl
  exact (congrArg (fun z ↦
      (((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := R)).obj (op A)).map g).f n ≫ z) (projection_eq_π Y R A I' n p)).trans
    (h.trans (congrArg (fun z ↦
      z ≫ SheafOfModules.homObjMap (R := R) (𝟙 (A.X p)) (g.f (p + n)))
        (projection_eq_π Y R A I n p).symm))

end WeilConjectures.IntegralHom
