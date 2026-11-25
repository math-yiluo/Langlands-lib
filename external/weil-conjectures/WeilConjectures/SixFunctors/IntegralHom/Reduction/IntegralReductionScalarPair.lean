/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair

/-! # Integral interfaces for the actual normalized scalar pair -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace WeilConjectures.IntegralHom
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  integralReductionExistence integralReductionDerivedExistence HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted constantSheaf

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
  [EssentiallySmall.{max u (t + 1)} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]

/-- Retain the actual normalized pair with the prescribed integral functor interfaces.
Source: Stacks 07A4 and 07A6; the integral Hom reduction proof, paragraph 2.
The existing actual pair supplies all data. Replace its ordinary and derived functor
fields by their definitionally equal integral reduction interfaces; every property is
retained. No new existence choice is made.
(blueprint: def-sf-integral-reduction-scalar-pair). -/
noncomputable def integralReductionScalarPair (n : ℕ) :
    ScalarDerivedPair.{t + 1, t, max u (t + 1), max (t + 2) (u + 1)}
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingProjectionUnrestricted l E Y n) :=
  { coefficientActualScalarDerivedPair l E Y n with
    extension := integralReductionChangeOfRings l E Y D hl n
    extension_additive := integralReductionChangeOfRingsAdditive l E Y D hl n
    derived := integralDerivedReduction l E Y D hl n }

end WeilConjectures.IntegralHom
