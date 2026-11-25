/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
/-! The evaluated counit equation for exceptional integral transport.
Source: Zheng, Lemma 5.22 and Proposition 5.24.
(blueprint: new-lem-sf-exceptional-ring-transport-core-evaluation-counit) -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

/-- The finite evaluation of the transported adjunction counit satisfies the
finite-stage adjunction-counit equation.  This is the counit clause in the
strict system transport calculation of Zheng, Lemma 5.22.
(blueprint: new-lem-sf-exceptional-ring-transport-core-evaluation-counit) -/
theorem exceptional_transport_core_evaluation_counit
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l,
      Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) :
    ∀ (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E Y).FullSubcategory),
      (d.evaluationF E n).hom.app ((d.G E).obj K) ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
          ((d.evaluationG E n).hom.app K) ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
          (((d.reconstruction E false).evaluation n).obj K) =
      ((d.reconstruction E false).evaluation n).map ((d.adjunction E).counit.app K) := by
  intro E n K
  exact (d.evaluationG E n).counit K
end WeilConjectures.ExceptionalIntegralScalar
