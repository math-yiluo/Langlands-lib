/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import all WeilConjectures.SixFunctors.Finite.Closed.FiniteClosedRealizationDomain
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import WeilConjectures.SixFunctors.Finite.Closed.FiniteClosedShriekMapPart
import all WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
import all WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportRestrictionOfScalars
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek

/-! # Finite coefficient change for closed exceptional inverse image

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general, order 2139,
lemma finite coefficient change for closed support (blueprint:
lemma-change-coefficients-exceptional-inverse-image--1).

The maps use the specified pro-etale exceptional functor and ordinary derived scalar
extension. The closed map is uniquely normalized by the exceptional counit. Total
extensions by zero below are used only outside the domains asserted by the theorems.
The closed-composition map is likewise uniquely normalized by the pasted counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

-- Cache these repeated derived-category prerequisites inside this proof module.
private theorem finiteClosedEtSheafify (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance

private theorem finiteClosedProEtInjectives (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  inferInstance

attribute [local instance] finiteClosedEtSheafify finiteClosedProEtInjectives

namespace WeilConjectures

/-- The fixed-scalar presentation of the actual small pro-etale derived category.
Source: blueprint finite coefficient change for closed support
(blueprint: lemma-change-coefficients-exceptional-inverse-image--1). -/
abbrev finiteClosedDerived (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- The recorded ordinary uncompleted derived change of constant coefficients.
Source: blueprint finite coefficient change for closed support
(blueprint: lemma-change-coefficients-exceptional-inverse-image--1). -/
abbrev finiteClosedScalar (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    (T : Scheme.{u}) : finiteClosedDerived T A ⥤ finiteClosedDerived T B :=
  @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) _ _ _ _ φ

/-- Ordinary derived direct image in these coefficient coordinates.
Source: blueprint finite coefficient change for closed support
(blueprint: lemma-change-coefficients-exceptional-inverse-image--1). -/
abbrev finiteClosedPush (A : Type u) [CommRing A] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    finiteClosedDerived Z A ⥤ finiteClosedDerived X A :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).rightDerivedFunctor

/-- Inverse of the specified ordinary coefficient comparison on its isomorphism domain.
Source: blueprint finite coefficient change for closed support
(blueprint: lemma-change-coefficients-exceptional-inverse-image--1). -/
def finiteClosedDirectInverse
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (N : finiteClosedDerived Z A) :
    (finiteClosedPush B i).obj ((finiteClosedScalar φ Z).obj N) ⟶
      (finiteClosedScalar φ X).obj ((finiteClosedPush A i).obj N) :=
  open Classical in
  if h : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i N) then
    @inv _ _ _ _ (ProEtale.finiteCoefficientChangeDirectImageMap φ i N) h
  else 0

end WeilConjectures
