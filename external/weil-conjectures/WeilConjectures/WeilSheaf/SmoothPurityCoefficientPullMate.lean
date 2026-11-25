/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionPullUnit

/-! # The nonflat pullback comparison as an adjunction mate -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

/-- The unit square identifies a specified left comparison with the mate of a right
comparison. This characterization needs no exactness or flatness assumptions. -/
lemma pushHomOfComapIso_eq_of_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : A ⥤ C} {H : B ⥤ D}
    (e : H ⋙ R' ≅ R ⋙ G) (α : G ⋙ L' ⟶ L ⋙ H)
    (h : ∀ M, G.map (adj.unit.app M) ≫ e.inv.app (L.obj M) =
      adj'.unit.app (G.obj M) ≫ R'.map (α.app M)) :
    pushHomOfComapIso adj adj' e = α := by
  ext M
  apply (adj'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ e.inv) M).symm.trans (h M)

end CategoryTheory.Adjunction

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual nonflat pullback/reduction comparison is the mate of the exact
restriction/pullback comparison. -/
theorem derivedUpperStarExtendScalarsIso_hom_eq_mate :
    (derivedUpperStarExtendScalarsIso a f).hom =
      Adjunction.pushHomOfComapIso
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
        (derivedComapLeftDerivedUpperStarIso a f).symm := by
  symm
  exact Adjunction.pushHomOfComapIso_eq_of_unit _ _ _ _
    (upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app a f)

end AlgebraicGeometry.ProEtale.CondensedRing
