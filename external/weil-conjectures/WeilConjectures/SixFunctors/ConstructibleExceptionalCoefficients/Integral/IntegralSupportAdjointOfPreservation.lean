/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.IntegralSupportOperationRealization

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

/-- The restricted integral compact-support lift is a left adjoint once preservation is known.
Source: Zheng, Construction 5.25 and Propositions 5.24 and 5.26; coefficient construction step 3.
Proof: transport the normalized finite-system adjunction through strict evaluation and derived
completion, then use fullness of the ambient inclusion to lift its canonical adjunction.
(blueprint: lem-sf-integral-support-adjoint-of-preservation). -/
theorem integral_support_adjoint_of_preservation (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (E : FieldStage.{u} l)
    (hpres : ∀ K : finiteTorConstructibleIntegralCategory l E.carrier X,
      finiteTorConstructibleIntegral l E.carrier Y
        ((PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).obj K.obj)) :
    ((finiteTorConstructibleIntegral l E.carrier Y).lift
      ((finiteTorConstructibleIntegral l E.carrier X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c)
      hpres).IsLeftAdjoint := by
  obtain ⟨A, left⟩ :=
    exists_integral_support_operation_realization l
      (AlgebraicClosure (ULift.{u} (Padic l))) D _hl f c E
  obtain ⟨left⟩ := left
  let F := (finiteTorConstructibleIntegral l E.carrier Y).lift
    ((finiteTorConstructibleIntegral l E.carrier X).ι ⋙
      PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c)
    hpres
  let e : A.F ≅ F := NatIso.ofComponents (fun K ↦
    ObjectProperty.isoMk _ (left.app K)) (by
      intro K L g
      apply ObjectProperty.hom_ext
      exact left.hom.naturality g)
  let : A.F.IsLeftAdjoint := A.adjunction.isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso e

end WeilConjectures.ConstructibleExceptionalCoefficients
