/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData
public import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestriction
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingRefinementCoordinatesCore
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison

/-! # Finite coefficient normalized refinement comparisons -/

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

/-- The finite coefficient part of the normalized refinement comparison.

Source: the finite coefficient construction in Zheng Section 5, Lemma 5.13 and
Constructions 5.14--5.15 (Stacks Tags 0F7B and 0F7I).
(blueprint: lem-sf-ring-open-map-normalized-refinement-finite).

Proof: construct the comparison from the finite coefficient proper/open refinement
word. Its transpose is the open adjunction unit after the canonical restriction;
the finite-Tor and etale-origin calculation makes this word invertible. -/
theorem exists_normalized_refinement_iso_finite
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (E : FieldStage.{max u v} l) (n : ℕ+)
    (hi : ((RingStage.finite E n).coefficients l).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        (((RingStage.finite E n).coefficients l).ring d.Z)
        (((RingStage.finite E n).coefficients l).ring c.Z)
        (((RingStage.finite E n).coefficients l).ring X)
        (((RingStage.finite E n).coefficients l).pull r.hom)
        (((RingStage.finite E n).coefficients l).pull c.i))
    (K : C.{u, v} l Ω X (.finite E n)) :
    ∃ ε :
        (PurCompactSupport.openExtension
          ((RingStage.finite E n).coefficients l) d.i).mapDerivedCategory.obj
          ((RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n)).obj K) ≅
        (PurCompactSupport.push ((RingStage.finite E n).coefficients l) r.hom).obj
          ((PurCompactSupport.openExtension
            ((RingStage.finite E n).coefficients l) c.i).mapDerivedCategory.obj
            ((RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n)).obj K)),
      (PurCompactSupport.openDerivedAdjunction
        ((RingStage.finite E n).coefficients l) d.i).homEquiv _ _ ε.hom ≫
          PurCompactSupport.refinementRestriction ((RingStage.finite E n).coefficients l) r hi
            ((RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n)).obj K) =
        (PurCompactSupport.openDerivedAdjunction
          ((RingStage.finite E n).coefficients l) c.i).unit.app
          ((RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n)).obj K) := by
  classical
  by_cases hchar : l = D.p
  · exact (hl hchar).elim
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero n.ne_zero
  have hn : n = ⟨m + 1, Nat.succ_pos m⟩ := Subtype.ext hm
  subst n
  let A := Padic.coefficientExtensionRing l E.carrier (m + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E.carrier (m + 1)
    (Nat.succ_pos m)
  have hK : intrinsicFiniteTorsionConstructible l E.carrier (m + 1)
      (Nat.succ_pos m) X K.obj := K.property.1
  obtain ⟨a, ha⟩ := hK.1.bddBelow
  obtain ⟨b, hb⟩ := hK.1.bddAbove
  have hv : ∀ i : ℤ, (i < min a b ∨ b < i) →
      CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj) := by
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hi
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin X A).2.2.1 K.obj).mpr
    ⟨hK.2, min a b, b, min_le_right _ _, hv⟩
  obtain ⟨c₀, d₀, _, hvan⟩ := L.property.2
  let LP : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{max u v + 1} (ULift.{max u v + 1} A))) :=
    ⟨L.obj, ⟨c₀, (DerivedCategory.isGE_iff L.obj c₀).2
      (fun i hi ↦ hvan i (Or.inl hi))⟩⟩
  let O : FrobeniusExchange.CompactOrigin A X :=
    { K := K.obj
      L := LP
      alpha := eL }
  have hg : (PurCompactSupport.finite l E.carrier (m + 1) (Nat.succ_pos m)).pull
      (r.hom ≫ d.g) = proEtaleRingCompositeCoefficients r.hom d.g
        ((PurCompactSupport.finite l E.carrier (m + 1) (Nat.succ_pos m)).ring Y)
        ((PurCompactSupport.finite l E.carrier (m + 1) (Nat.succ_pos m)).ring d.Z)
        ((PurCompactSupport.finite l E.carrier (m + 1) (Nat.succ_pos m)).ring c.Z)
        ((PurCompactSupport.finite l E.carrier (m + 1) (Nat.succ_pos m)).pull d.g)
        ((PurCompactSupport.finite l E.carrier (m + 1) (Nat.succ_pos m)).pull r.hom) :=
    (proEtaleConstantRingCompositeCoefficients_eq r.hom d.g A).symm
  obtain ⟨ε, hε, _⟩ := finite_ring_refinement_coordinates_canonical
    l E.carrier m r O hi hg
  exact ⟨ε, hε⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
