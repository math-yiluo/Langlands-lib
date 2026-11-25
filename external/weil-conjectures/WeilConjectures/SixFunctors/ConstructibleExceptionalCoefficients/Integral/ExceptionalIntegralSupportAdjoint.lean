/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.IntegralSupportPreservation
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.IntegralSupportAdjointOfPreservation

/-! # A right adjoint to the restricted integral compact-support functor -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

/-- Preservation and right-adjoint existence for one integral compact-support functor.
Source: Zheng, Construction 5.25 and Propositions 5.24 and 5.26;
coefficient construction step 3
(blueprint: lem-sf-integral-support-restricted-right-adjoint).

Proof: extend by zero along c.i and take the proper direct image along c.g on
normalized finite coefficient systems. Extension by zero preserves the finite Tor
interval. Proper cohomological dimension enlarges its upper bound by twice a fixed
finite bound for c.Z, independently of the coefficient level. The finite exceptional
adjoints have uniform bounds from a fixed finite affine cover of X and Y. Their
units and counits commute with coefficient quotient maps. Thus these operations
restrict to normalized constructible systems with common finite Tor bounds and
form an adjunction there. Strict evaluation and derived inverse limit identify
this category with the complete integral constructible finite-Tor subcategory.
Transport the adjunction across these equivalences. The proper/open realization
of the transported left functor is its canonical integral compact-support
realization. Since the ambient inclusion is full and faithful, lift this realization
and transport the adjunction to the literal restriction displayed below. This
proves both its preservation predicate and existence of a right adjoint. No
choice of an adjoint is required by the statement. Empty c.Z has zero operations
and dimension bound zero. No separatedness of X or Y over the base is used. -/
theorem exists_integral_support_adjoint (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (E : FieldStage.{u} l) :
    ∃ hpres : ∀ K : finiteTorConstructibleIntegralCategory l E.carrier X,
      finiteTorConstructibleIntegral l E.carrier Y
        ((PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).obj K.obj),
    ((finiteTorConstructibleIntegral l E.carrier Y).lift
      ((finiteTorConstructibleIntegral l E.carrier X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c)
      hpres).IsLeftAdjoint  := by
  exact ⟨integral_support_preservation l D _hl f c E,
    integral_support_adjoint_of_preservation l D _hl f c E
      (integral_support_preservation l D _hl f c E)⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
