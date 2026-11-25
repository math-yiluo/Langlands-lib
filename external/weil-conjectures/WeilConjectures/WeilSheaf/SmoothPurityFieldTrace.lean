/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Proper

/-!
# The smooth proper trace after extending the base field

The trace chosen over the base field remains a universal arrow after a field extension.
This uses invertibility of the canonical dualizing base-change morphism, so no agreement
between the independently chosen orientations over the two fields is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Adjunction

/-- Transposing a pulled-back trace gives the pulled-back orientation followed by
exceptional base change. -/
lemma homEquiv_baseChangedTrace
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {a : C ⥤ D} {a' : D ⥤ C} (adj : a ⊣ a')
    {b : C' ⥤ D'} {b' : D' ⥤ C'} (adj' : b ⊣ b')
    {G : C ⥤ C'} {H : D ⥤ D'} (bc : a ⋙ H ≅ G ⋙ b)
    {U : D} {U' : D'} (e : H.obj U ⟶ U') {T : C} (γ : T ⟶ a'.obj U) :
    adj'.homEquiv _ _
        (bc.inv.app T ≫ H.map (a.map γ ≫ adj.counit.app U) ≫ e) =
      G.map γ ≫ unitBaseChange adj adj' bc.hom e := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, homEquiv_counit, Functor.map_comp, Category.assoc,
    ← cancel_epi (bc.hom.app T), Iso.hom_inv_id_app_assoc]
  have hn := bc.hom.naturality γ
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, app_comp_map_unitBaseChange_comp_counit]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

universe u

open Scheme

variable (l : ℕ) [Fact l.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ l)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ l)]
  {X : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [IsProper (toPoint X).left]
  {X' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [IsProper (toPoint X').left]
  {π : X'.left ⟶ X.left}
  (e : (boundedConstructibleUpperStarOfMap l (X := point F) (Y := point L)
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (𝟙_ _) ⟶ 𝟙_ _)
  (sq : IsPullback π (toPoint X').left (toPoint X).left
    (Spec.map (CommRingCat.ofHom (algebraMap F L))))
  (d : ℕ)

/-- The smooth trace expressed using proper direct image. -/
def smoothProperTrace :
    (boundedConstructibleLowerStar l (toPoint X)).obj
      (boundedConstructibleTateTwist l X d (2 * d)) ⟶ 𝟙_ _ :=
  (boundedConstructibleLowerStar l (toPoint X)).map (smoothOrientation l (toPoint X) d) ≫
    (properLowerStarUpperShriekAdjunction l X).counit.app (𝟙_ _)

/-- The proper trace is the compact-support trace through the comparison of direct images. -/
lemma smoothProperTrace_eq :
    smoothProperTrace l (X := X) d =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl l (toPoint X)).inv.app
        (boundedConstructibleTateTwist l X d (2 * d)) ≫ smoothTrace l (toPoint X) d := by
  rw [smoothProperTrace, smoothTrace_eq]
  change _ ≫ ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl l (toPoint X)).inv.app _ ≫
    (boundedConstructibleUpperShriekAdjunction l (toPoint X)).counit.app _) = _
  rw [← NatTrans.naturality_assoc]

/-- Pull the finite-base smooth trace across proper base change. -/
def fieldChangedSmoothProperTrace :
    (boundedConstructibleLowerStar l (toPoint X')).obj
      ((boundedConstructibleUpperStarOfMap l (X := X) (Y := X') π).obj
        (boundedConstructibleTateTwist l X d (2 * d))) ⟶ 𝟙_ _ :=
  have := isIso_boundedConstructibleBaseChangeOfMap l sq
  (asIso (boundedConstructibleBaseChangeOfMap l sq.toCommSq)).inv.app
      (boundedConstructibleTateTwist l X d (2 * d)) ≫
    (boundedConstructibleUpperStarOfMap l (X := point F) (Y := point L)
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map (smoothProperTrace l d) ≫ e

/-- The adjunct of the field-changed trace is the field-changed orientation. -/
lemma homEquiv_fieldChangedSmoothProperTrace :
    (properLowerStarUpperShriekAdjunction l X').homEquiv _ _
        (fieldChangedSmoothProperTrace l e sq d) =
      (boundedConstructibleUpperStarOfMap l (X := X) (Y := X') π).map
          (smoothOrientation l (toPoint X) d) ≫ dualizingComplexBaseChange l e sq := by
  have := isIso_boundedConstructibleBaseChangeOfMap l sq
  simpa only [fieldChangedSmoothProperTrace, smoothProperTrace, dualizingComplexBaseChange,
    Adjunction.unitBaseChangeOfEq, eqToHom_refl, Category.id_comp, Category.comp_id,
    asIso_hom] using
    Adjunction.homEquiv_baseChangedTrace (properLowerStarUpperShriekAdjunction l X)
    (properLowerStarUpperShriekAdjunction l X')
    (asIso (boundedConstructibleBaseChangeOfMap l sq.toCommSq)) e
    (smoothOrientation l (toPoint X) d)

/-- Proper smooth purity remains invertible after extending the base field, for the
trace chosen over the original field. -/
theorem isIso_homEquiv_fieldChangedSmoothProperTrace [IsIso e]
    [SmoothOfRelativeDimension d (toPoint X).left] :
    IsIso ((properLowerStarUpperShriekAdjunction l X').homEquiv _ _
      (fieldChangedSmoothProperTrace l e sq d)) := by
  rw [homEquiv_fieldChangedSmoothProperTrace]
  have := isIso_dualizingComplexBaseChange_of_fieldExtension l e sq
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
