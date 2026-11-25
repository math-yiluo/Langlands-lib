/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd

/-! # Independence of coordinates on a trivial line

Source: Step 9 of `lem-pod-condensed-point-sections-transport`.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Conjugating an endomorphism of a trivial line to the tensor unit is independent
of the chosen trivialization.
Source: blueprint `theorem-poincare-duality-frobenius`, elimination of the twist, and Step 9 of the
point-section transport argument.
Proof: endomorphisms of the tensor unit commute, by the naturality of the unit
endomorphism action. The two conjugates differ by conjugation with an automorphism
of that unit, which therefore acts trivially.
(blueprint: lem-pod-point-line-coordinates) -/
theorem point_line_conjugation_independent
    {A : Type*} [Category* A] [MonoidalCategory A]
    {L : A} (f : L ⟶ L) (h h' : L ≅ 𝟙_ A) :
    h.inv ≫ f ≫ h.hom = h'.inv ≫ f ≫ h'.hom := by
  have hc := unitEndAction_naturality
    (h.inv ≫ f ≫ h.hom) (End.of (h.inv ≫ h'.hom))
  simp only [unitEndAction_unit] at hc
  calc
    h.inv ≫ f ≫ h.hom =
        (h'.inv ≫ h.hom) ≫ (h.inv ≫ h'.hom) ≫ (h.inv ≫ f ≫ h.hom) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    _ = (h'.inv ≫ h.hom) ≫ (h.inv ≫ f ≫ h.hom) ≫ (h.inv ≫ h'.hom) := by
      rw [hc]
    _ = h'.inv ≫ f ≫ h'.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
