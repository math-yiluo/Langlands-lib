/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCounitIsIso

/-! # Invertible mates for fully faithful left adjoints

When both adjunction units are invertible and the right adjoints commute up to an
isomorphism, the mate of any invertible left square is invertible. No normalization
between the left and right squares is needed.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  (a : L ⊣ R) (a' : L' ⊣ R') [IsIso a.unit] [IsIso a'.unit]
  {G : C ⥤ C'} {H : D ⥤ D'} (θ : R ⋙ G ≅ H ⋙ R') (bc : L ⋙ H ≅ G ⋙ L')

include θ in
/-- Full faithfulness and a commuting right square force invertibility of the mate
of any invertible left square. -/
theorem isIso_mate_of_isIso_units_of_rightIso (U : D) :
    IsIso ((mateEquiv a a' bc.inv).app U) := by
  have hR : IsIso (R.map (a.counit.app U)) := by
    have h : IsIso (a.unit.app (R.obj U) ≫ R.map (a.counit.app U)) := by
      rw [a.right_triangle_components]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (a.unit.app (R.obj U)) _
  have hn := θ.hom.naturality (a.counit.app U)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  have hcomp : IsIso (θ.hom.app (L.obj (R.obj U)) ≫ R'.map (H.map (a.counit.app U))) := by
    rw [← hn]
    infer_instance
  have hε := IsIso.of_isIso_comp_left (θ.hom.app (L.obj (R.obj U)))
    (R'.map (H.map (a.counit.app U)))
  exact isIso_mateEquiv_app_of_isIso_map_counit a a' (TwoSquare.mk _ _ _ _ bc.inv) U hε

end CategoryTheory.Adjunction
