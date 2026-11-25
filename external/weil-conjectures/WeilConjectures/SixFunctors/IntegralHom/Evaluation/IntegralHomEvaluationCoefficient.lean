/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientCochainTensorCurry

/-! # Agreement of the two section-evaluation notations

Source: Stacks Tags 0A8X and 03EO.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

/-- The two notations use the same chosen Hom-complex product projection.

Source: Stacks Tags 0A8X and 03EO; blueprint integral-Hom reduction, paragraph 2.
Proof: unfold evaluation, its projection, the coefficient Hom component and
section application. Both use the same chosen Hom-complex product projection
at total degree i+j and evaluate the resulting section at the identity slice.
(blueprint: new-sf-integral-hom-evaluation-coefficient) -/
theorem evaluate_eq_coefficient (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (P I : CochainComplex (Modules.{t, u} Y R) ℤ) (j i : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (f : ((homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := R) P I).X j).val.obj U) (x : (P.X i).val.obj U) :
    evaluate.{t, u} Y R P I j i U f x =
      coefficientHomSectionApply.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R (P.X i) (I.X (i + j)) U
        ((coefficientHomComponent.{u, t + 1, t}
          (AlgebraicGeometry.Scheme.ProEt.topology Y) R P I j i (i + j) rfl).val.app U f) x := by
  rfl

end WeilConjectures.IntegralHom
