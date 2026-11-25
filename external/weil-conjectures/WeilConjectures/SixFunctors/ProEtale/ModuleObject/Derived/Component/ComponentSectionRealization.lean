/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentInverseFullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentSectionScalarNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentSectionDerivedSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentSectionRealizationPoint

/-! # Normalized section-ring realization square for component pullback

Source: Hemo--Richarz--Scholbach, Remark 3.2 and Proposition 4.3(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]

end AlgebraicGeometry.ProEtale.CondensedRing
