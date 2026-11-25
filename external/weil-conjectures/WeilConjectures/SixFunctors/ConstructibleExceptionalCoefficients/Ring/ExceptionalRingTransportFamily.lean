/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMates
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.ExceptionalRingTransportCore
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalTransportLeftShift

/-! # A coherent ring family before scalar comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- Finite and integral adjunctions can be chosen with their actual normalized
reduction/limit transport, before constructing any coefficient scalar comparison.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24, 5.26;
ring canonical scalar invertibility, proof step 1
(blueprint: lem-sf-exceptional-ring-transport-family).

Proof: normalize the shifts on the finite and integral operations along their
compact-support realizations, with the induced right-adjoint shifts. Then choose
the ordinary finite compact-support adjunctions with their common
coefficient-independent bounds. The actual strict-system proper/open adjunction
and its finite evaluation unit and counit are supplied by exceptionalSystemTransport.
Where that theorem requires a higher coefficient universe, lift the coefficient
field and transport along the induced ring equivalences, retaining the actual
evaluation comparisons and both adjunction maps under this transport.
Restrict to normalized systems with uniform constructibility, cohomological and
Tor intervals: the open functor preserves the Tor interval and proper image has
a uniform cohomological bound, while the finite exceptional adjoints have uniform
bounds. The actual reduction/total-limit adjunction restricts to an equivalence
with the complete integral finite-Tor categories. Conjugate the restricted system
adjunction through this equivalence, using its actual unit and counit. Take these
conjugates as the integral operations. The reconstruction calculus gives realizeF,
realizeG, reductionF, reductionG and the two evaluation identities. Use simultaneous
proper/open system realization for the left realization: its proper comparison
and normalized open map, followed by the reconstruction unit, give exactly the
integral_system_normalized equation. Thus these equations are equations of whole
system maps before evaluation; no faithfulness of finite evaluation is required.
Finite and integral stages are disjoint constructors, so these choices assemble
into the stated family. Empty schemes use the zero adjunction; positive levels
remain n+1 throughout. No scalar restriction, q, b, or scalar invertibility is a
conclusion or hypothesis of this statement. -/
theorem exists_exceptional_ring_transport_family
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l),
      ∃ left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s),
        Nonempty (ExceptionalIntegralScalar.Transported l Ω D hl c operation left) := by
  obtain ⟨operation, left, shifts⟩ :=
    ExceptionalIntegralScalar.exists_exceptional_transport_left_shifts l Ω D hl f c
  obtain ⟨transport⟩ := exists_exceptional_transport_for_operations
    l Ω D hl f c operation left shifts
  exact ⟨operation, left, ⟨transport⟩⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
