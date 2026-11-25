/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientPullbackReduction
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

/-! # Finite regular coefficient comparison data

Source: Stacks 03D6 and 0D6D; main-20261015, constant-sheaf clause of
theorem-grothendieck-lefschetz-trace-formula--8 (blueprint:
def-zl-finite-regular-coefficient-comparisons).

The regular complex and c, kappa and lambda below are transparent aliases of the
published constructions, not new choices or copies. Composition is the prescribed
ringed-site compositor, transported by the published unit-preserving coordinate maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The prescribed finite compositor in the intrinsic pullback coordinates.
The middle factor is exactly the specialization of the ringed-site compositor in
lem-weil-pbc-proetale-derived-pullback-composition. The other factors are the uniquely
unit-preserving published change of presentation, descended termwise. In particular
this does not introduce an independently chosen intrinsic compositor.
Source: Stacks 0D6D, canonical termwise pullback composition
(blueprint: def-zl-finite-regular-coefficient-comparisons). -/
@[no_expose]
def finiteCanonicalPullbackComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ) :
    finiteDerivedPullback l E m (f ≫ g) ≅
      finiteDerivedPullback l E m g ⋙ finiteDerivedPullback l E m f :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (m + 1))
      (f ≫ g)).symm ≪≫
    integralFiniteCanonicalPullbackComposition l E f g m ≪≫
    Functor.isoWhiskerRight
      (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (m + 1)) g)
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (m + 1)) f) ≪≫
    Functor.isoWhiskerLeft (finiteDerivedPullback l E m g)
      (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (m + 1)) f)

end WeilConjectures
