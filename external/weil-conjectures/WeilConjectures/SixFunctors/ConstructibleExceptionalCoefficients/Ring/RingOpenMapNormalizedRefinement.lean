/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData
public import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestriction
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingOpenMapNormalizedRefinementFinite
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingOpenMapNormalizedRefinementIntegral

/-! # Normalized objectwise refinement comparisons -/

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

/-- A normalized objectwise comparison is available at every ring stage.

Source: the normalized refinement construction in Zheng Section 5, Lemma 5.13 and
Constructions 5.14--5.15 (Stacks Tags 0F7B and 0F7I).
(blueprint: lem-sf-ring-open-map-normalized-refinement).

Proof: use the finite coefficient construction at finite stages and its normalized
strict reduction system at completed integral stages. The coefficient realization
identifies the resulting comparison with the displayed open and proper functors;
its defining normalization is the inverse restriction followed by the open unit.
This statement records only the objectwise comparison and its normalization, leaving
invertibility of the canonical map to the parent theorem. -/
theorem exists_normalized_refinement_iso
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) (s : RingStage.{max u v} l)
    (hi : (s.coefficients l).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        ((s.coefficients l).ring d.Z) ((s.coefficients l).ring c.Z)
        ((s.coefficients l).ring X)
        ((s.coefficients l).pull r.hom) ((s.coefficients l).pull c.i))
    (K : C.{u, v} l Ω X (s.stage l)) :
    ∃ ε : (PurCompactSupport.openExtension (s.coefficients l) d.i).mapDerivedCategory.obj
          ((RingStage.inclusion.{u, v} l Ω X s).obj K) ≅
        (PurCompactSupport.push (s.coefficients l) r.hom).obj
          ((PurCompactSupport.openExtension (s.coefficients l) c.i).mapDerivedCategory.obj
            ((RingStage.inclusion.{u, v} l Ω X s).obj K)),
      (PurCompactSupport.openDerivedAdjunction (s.coefficients l) d.i).homEquiv _ _ ε.hom ≫
          PurCompactSupport.refinementRestriction (s.coefficients l) r hi
            ((RingStage.inclusion.{u, v} l Ω X s).obj K) =
        (PurCompactSupport.openDerivedAdjunction (s.coefficients l) c.i).unit.app
          ((RingStage.inclusion.{u, v} l Ω X s).obj K) := by
  cases s with
  | finite E n =>
      exact exists_normalized_refinement_iso_finite l Ω D hl r E n hi K
  | integral E =>
      exact exists_normalized_refinement_iso_integral l Ω D hl r E hi K

end WeilConjectures.ConstructibleExceptionalCoefficients
