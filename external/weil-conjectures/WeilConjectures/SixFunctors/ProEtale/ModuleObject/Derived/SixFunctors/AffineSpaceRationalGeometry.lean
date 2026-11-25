/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Coordinate identifications for rational affine-space induction

Source: blueprint `sk-cor-affine-space-rational-induction.proof.md`, first paragraph
(blueprint: lem-sfb-rational-affine-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Split off the last affine coordinate, using the affine line's recorded coordinate type.
Source: the polynomial-coordinate identity in the affine-space induction
(blueprint: lem-sfb-rational-affine-geometry). -/
def rationalAffineSuccIso (V : Scheme.{u}) (d : ℕ) :
    𝔸(ULift.{u} (Fin (d + 1)); V) ≅ 𝔸(PUnit.{u + 1}; 𝔸(ULift.{u} (Fin d); V)) :=
  AffineSpace.reindexIso V
      ((Equiv.sumCongr Equiv.ulift (Equiv.equivPUnit (Fin 1)).symm).trans
        (finSumFinEquiv.trans Equiv.ulift.symm)) ≪≫ AffineSpace.sumIso V

/-- Coordinate splitting commutes with the actual structural projections.
Source: the polynomial-coordinate identity in the affine-space induction
(blueprint: lem-sfb-rational-affine-geometry).
Proof: the sum-coordinate isomorphism commutes with both projections, and coordinate
reindexing commutes with the projection to V. Compose these two equations. -/
theorem rationalAffineSuccIso_over (V : Scheme.{u}) (d : ℕ) :
    (rationalAffineSuccIso V d).hom ≫
        (𝔸(PUnit.{u + 1}; 𝔸(ULift.{u} (Fin d); V)) ↘ 𝔸(ULift.{u} (Fin d); V)) ≫
          (𝔸(ULift.{u} (Fin d); V) ↘ V) = (𝔸(ULift.{u} (Fin (d + 1)); V) ↘ V) := by
  rw [rationalAffineSuccIso, Iso.trans_hom, Category.assoc,
    AffineSpace.sumIso_hom_over_over, AffineSpace.reindexIso_hom, AffineSpace.reindex_over]

/-- The zero-coordinate affine projection is an isomorphism.
Source: the identity base case of the affine-space induction
(blueprint: lem-sfb-rational-affine-geometry).
Proof: the zero section is its inverse. One composite is the usual section equation;
the other follows from the affine-space universal property, since there are no coordinates. -/
theorem rationalAffineZero_isIso (V : Scheme.{u}) :
    IsIso (𝔸(ULift.{u} (Fin 0); V) ↘ V) := by
  refine ⟨⟨AffineSpace.zeroSection _ V, ?_, AffineSpace.zeroSection_comp_over _ V⟩⟩
  apply AffineSpace.hom_ext
  · simp
  · intro i
    exact Fin.elim0 i.down

end AlgebraicGeometry.ProEtale.CondensedRing
