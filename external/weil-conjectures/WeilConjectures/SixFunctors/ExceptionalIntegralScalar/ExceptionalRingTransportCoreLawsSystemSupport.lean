/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreLawsSystemSupportMaps

/-! The support part of the exceptional integral transport system laws.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-support-law).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

/--
The strict-system transport calculation supplies the support identity for the
transported functor.  This is the support component isolated from the full
system-law package.  The construction transports the proper/open support
comparison through the chosen reconstruction equivalences and then retains its
functor equality on the prescribed full subcategories.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-support-law).
-/
theorem exists_exceptional_transport_core_system_support_law
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) :
    Nonempty (∀ E : FieldStage.{u} l,
      d.F E ⋙ (sequenceProperty l E Y).ι =
        (sequenceProperty l E X).ι ⋙
          IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
            IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g) := by
  refine ⟨fun E => ?_⟩
  refine CategoryTheory.Functor.ext
    (F := d.F E ⋙ (sequenceProperty l E Y).ι)
    (G := (sequenceProperty l E X).ι ⋙
      IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
        IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g) ?_ ?_
  · intro K
    exact exceptional_transport_core_system_support_obj
      l Ω D hl f c operation left d E K
  · intro K K' u
    exact exceptional_transport_core_system_support_map
      l Ω D hl f c operation left d E u

end WeilConjectures.ExceptionalIntegralScalar
