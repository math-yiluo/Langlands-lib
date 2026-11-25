/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PointedEtaleQuotientFunctor
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import WeilConjectures.RingTheory.PointedEtaleFiltered
import WeilConjectures.RingTheory.PointedEtaleQuotientMorphismLift

/-! # Common refinements in pointed base-change comma categories

Source: Stacks Project, Tags 04GW, 04D1 and 05WS.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

private theorem common_refinement_of_filtered
    {C D : Type*} [Category* C] [Category* D]
    [IsFiltered C] [IsFiltered D] (F : C ⥤ D)
    (hLift : ∀ U V (h : F.obj U ⟶ V),
      ∃ (W : C) (k : U ⟶ W) (e : F.obj W ≅ V), F.map k ≫ e.hom = h)
    (T : D) (X Y : StructuredArrow T F) :
    ∃ Z : StructuredArrow T F, Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) := by
  classical
  obtain ⟨U, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs X.right Y.right
  let a := X.hom ≫ F.map f
  let b := Y.hom ≫ F.map g
  obtain ⟨V, h, heq⟩ := IsFilteredOrEmpty.cocone_maps a b
  obtain ⟨W, k, e, hk⟩ := hLift U V h
  have hk' : F.map k = h ≫ e.inv := (Iso.eq_comp_inv e).mpr hk
  let Z : StructuredArrow T F := StructuredArrow.mk ((a ≫ h) ≫ e.inv)
  refine ⟨Z, ⟨StructuredArrow.homMk (f ≫ k) ?_⟩,
    ⟨StructuredArrow.homMk (g ≫ k) ?_⟩⟩
  · change X.hom ≫ F.map (f ≫ k) = (a ≫ h) ≫ e.inv
    rw [F.map_comp, hk']
    simp only [a, Category.assoc]
  · change Y.hom ≫ F.map (g ≫ k) = (a ≫ h) ≫ e.inv
    rw [F.map_comp, hk', ← Category.assoc, ← Category.assoc]
    change (b ≫ h) ≫ e.inv = (a ≫ h) ≫ e.inv
    rw [heq]

/-- Two pointed comma objects admit a common successor.
Source: Stacks Project, Tags 04GW (filteredness) and 04D1 (relative lifting),
used in the pointed-colimit argument of Tag 05WS.
(blueprint: lem-sbc-pointed-etale-quotient-comma-refinement)

Proof: Filteredness of the source supplies U and arrows from the sources of X
and Y. The induced arrows a,b:T -> F(U) are parallel in the target, which is
also filtered, so find h:F(U) -> V with a followed by h equal to b followed by h.
Lift h by the relative pointed etale lifting lemma: obtain W, k:U -> W and
an isomorphism e:F(W) -> V with F(k) followed by e equal to h. Take the comma
object with source W and arrow T -> F(W) given by a followed by h and e inverse.
The two source arrows followed by k yield comma morphisms from X and Y. Their
commuting equations are exactly the equalizing equation and the lifting equation.
This uses the already proved filteredness theorem and requires no separate
scheme-level diagonal construction. -/
theorem pointedEtaleQuotient_comma_refinement
    (A K B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π)
    (c : (quotientBaseChange π).obj (CommAlgCat.of A K) ≅ CommAlgCat.of B L)
    (T : ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of B L) ↦ Etale B X.left))
    (X Y : StructuredArrow T (pointedEtaleBaseChange π c.hom)) :
    ∃ Z : StructuredArrow T (pointedEtaleBaseChange π c.hom),
      Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) := by
  have := pointedEtale_filtered A K
  have := pointedEtale_filtered B L
  exact common_refinement_of_filtered (pointedEtaleBaseChange π c.hom)
    (fun S T f ↦ pointedEtaleQuotient_morphism_lift A K B L π hπ c S T f) T X Y

end Algebra
