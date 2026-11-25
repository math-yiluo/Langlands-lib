/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMates
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.ExceptionalRingOperationsExistence
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Shift witnesses for exceptional integral transport realizations -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

/-- Exceptional operations admit compact-support realizations compatible with shifts.
Source: Zheng, Construction 5.25 and Proposition 5.26.

Proof: choose the finite and integral operations and their left realizations. At
one ring stage write the realization as `r : F ⋙ IY ≅ IX ⋙ H`. The inclusions
are fully faithful, exact, and compatible with shifts, and the proper/open image
`H` is exact with its canonical shift. Transport that shift to `F` by `ofComp`;
its compatibility theorem makes `r` commute with shifts. Reflect exactness along
`IY`. Give the existing right adjoint its uniquely induced shift, so both
adjunction maps commute with shifts, and use exactness of a right adjoint.
Reassemble the operation with these structures and the same functors,
adjunction, and realization. Choose these normalized operations stagewise.
This argument includes zero objects and empty schemes, with no nonvanishing
assumption.

STATEMENT-DISPUTED (former statement): the universal assertion for arbitrary,
independently shifted operations
and arbitrary realization isomorphisms is not asserted: compatibility requires
this normalization of the shift structures.
(blueprint: new-lem-sf-exceptional-ring-transport-left-shifts)
-/
theorem exists_exceptional_transport_left_shifts
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
        ∀ s : RingStage.{u} l, (left s).hom.CommShift ℤ := by
  classical
  obtain ⟨operation, left, _⟩ := exists_exceptional_ring_operations l Ω D hl f c
  have stage (s : RingStage.{u} l) :
      ∃ A : Operation.{u} l Ω X Y (s.stage l),
        ∃ r : LeftRealization.{u} l Ω c s A, r.hom.CommShift ℤ := by
    let A := operation s
    let r := left s
    let IX := RingStage.inclusion.{u} l Ω X s
    let IY := RingStage.inclusion.{u} l Ω Y s
    let H := PurCompactSupport.image (s.coefficients l) c
    have fully : IY.FullyFaithful := by
      cases s with
      | finite E n => exact (finiteTorConstructible l E.carrier n n.pos Y).fullyFaithfulι
      | integral E => exact (finiteTorConstructibleIntegral l E.carrier Y).fullyFaithfulι
    let : IX.CommShift ℤ := inclusionShift l Ω X s
    let : IY.CommShift ℤ := inclusionShift l Ω Y s
    let : IY.Full := fully.full
    let : IY.Faithful := fully.faithful
    let : IX.IsTriangulated := by
      cases s <;> exact ⟨fun _ hT ↦ hT⟩
    let : IY.IsTriangulated := by
      cases s <;> exact ⟨fun _ hT ↦ hT⟩
    let : H.IsTriangulated := by
      dsimp only [H, PurCompactSupport.image]
      infer_instance
    let : A.F.CommShift ℤ := Functor.CommShift.ofComp r ℤ
    let : r.hom.CommShift ℤ := Functor.CommShift.ofComp_compatibility r ℤ
    let : A.F.IsTriangulated :=
      (Functor.isTriangulated_iff_comp_right r).mpr inferInstance
    let := A.adjunction.rightAdjointCommShift ℤ
    let := A.adjunction.commShift_of_leftAdjoint ℤ
    refine ⟨{
      F := A.F
      G := A.G
      adjunction := A.adjunction
      leftExact := inferInstance
      rightExact := A.adjunction.isTriangulated_rightAdjoint
      unitShift := inferInstance
      counitShift := inferInstance }, r, ?_⟩
    infer_instance
  choose operation' left' shifts using stage
  exact ⟨operation', left', shifts⟩

end WeilConjectures.ExceptionalIntegralScalar
