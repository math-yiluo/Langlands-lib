/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData
public import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestriction
import WeilConjectures.DeligneLaumon.QcqsCompletedRefinement

/-! # Completed integral normalized refinement comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The completed integral coefficient part of the normalized refinement comparison.

Source: the normalized strict reduction construction in Zheng Section 5, Lemma 5.13
and Constructions 5.14--5.15 (Stacks Tags 0F7B and 0F7I).
(blueprint: lem-sf-ring-open-map-normalized-refinement-integral).

Proof: construct compatible finite-level comparisons on the normalized strict
reduction system, take the normalized total-limit comparison, and identify its
transpose with the displayed open unit and restriction. -/
theorem exists_normalized_refinement_iso_integral
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (E : FieldStage.{max u v} l)
    (hi : ((RingStage.integral E).coefficients l).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        (((RingStage.integral E).coefficients l).ring d.Z)
        (((RingStage.integral E).coefficients l).ring c.Z)
        (((RingStage.integral E).coefficients l).ring X)
        (((RingStage.integral E).coefficients l).pull r.hom)
        (((RingStage.integral E).coefficients l).pull c.i))
    (K : C.{u, v} l Ω X (.integral E)) :
    ∃ ε :
        (PurCompactSupport.openExtension
          ((RingStage.integral E).coefficients l) d.i).mapDerivedCategory.obj
          ((RingStage.inclusion.{u, v} l Ω X (RingStage.integral E)).obj K) ≅
        (PurCompactSupport.push ((RingStage.integral E).coefficients l) r.hom).obj
          ((PurCompactSupport.openExtension
            ((RingStage.integral E).coefficients l) c.i).mapDerivedCategory.obj
            ((RingStage.inclusion.{u, v} l Ω X (RingStage.integral E)).obj K)),
      (PurCompactSupport.openDerivedAdjunction
        ((RingStage.integral E).coefficients l) d.i).homEquiv _ _ ε.hom ≫
          PurCompactSupport.refinementRestriction ((RingStage.integral E).coefficients l) r hi
            ((RingStage.inclusion.{u, v} l Ω X (RingStage.integral E)).obj K) =
        (PurCompactSupport.openDerivedAdjunction
          ((RingStage.integral E).coefficients l) c.i).unit.app
          ((RingStage.inclusion.{u, v} l Ω X (RingStage.integral E)).obj K) := by
  let K' : sfIntegralConstructibleCategory l E.carrier X := ⟨K.obj, K.property.1⟩
  obtain ⟨ρ, hρ⟩ := sfQcqsCompletedRefinement_exists l E.carrier D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) r K'
  obtain ⟨ε, hε, _⟩ := hρ
  exact ⟨ε, hε⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
