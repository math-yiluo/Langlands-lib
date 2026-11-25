/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree

/-!
# Comparing free Weil objects with compact-support functors

The coproduct proof for a right derived pushforward only needs its comparisons with
forgetting and the cyclic actions. We state that proof for arbitrary functors, so it
also applies to composites with exact extension by zero.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v'

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  (RW : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
  (R : DerivedCategory C ⥤ DerivedCategory D)
  (e : RW ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ R)

/-- The free comparison obtained by transposing the forgetful comparison. -/
def forgetFreeComparison (X : DerivedCategory C) :
    (Free.functor G).mapDerivedCategory.obj (R.obj X) ⟶
      RW.obj ((Free.functor F).mapDerivedCategory.obj X) :=
  ((freeWeilDerivedAdjunction G).homEquiv _ _).symm
    (R.map ((freeWeilDerivedAdjunction F).unit.app X) ≫
      e.inv.app ((Free.functor F).mapDerivedCategory.obj X))

/-- The free comparison respects the free adjunction units. -/
@[reassoc]
lemma unit_app_comp_map_forgetFreeComparison (X : DerivedCategory C) :
    (freeWeilDerivedAdjunction G).unit.app (R.obj X) ≫
        (forget G).mapDerivedCategory.map (forgetFreeComparison RW R e X) =
      R.map ((freeWeilDerivedAdjunction F).unit.app X) ≫
        e.inv.app ((Free.functor F).mapDerivedCategory.obj X) := by
  exact ((freeWeilDerivedAdjunction G).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

variable (χ : R ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ R)
  (hσ : ∀ A : DerivedCategory (IsoAlgebra F),
    (derivedStrIso G).hom.app (RW.obj A) ≫ e.hom.app A =
      G.mapDerivedCategory.map (e.hom.app A) ≫
        χ.hom.app ((forget F).mapDerivedCategory.obj A) ≫
        R.map ((derivedStrIso F).hom.app A))

include hσ

omit [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D] in
/-- The cyclic compatibility written through the inverse forgetful comparison. -/
@[reassoc]
lemma map_derivedStrIso_comp_forgetComparison_inv (A : DerivedCategory (IsoAlgebra F)) :
    R.map ((derivedStrIso F).hom.app A) ≫ e.inv.app A =
      χ.inv.app ((forget F).mapDerivedCategory.obj A) ≫
        G.mapDerivedCategory.map (e.inv.app A) ≫ (derivedStrIso G).hom.app (RW.obj A) := by
  rw [← cancel_epi (χ.hom.app _),
    ← cancel_epi (G.mapDerivedCategory.map (e.hom.app A)),
    ← reassoc_of% (hσ A), Iso.hom_inv_id_app]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  exact Category.comp_id _

/-- A cyclic comparison which preserves the coproduct underlying the free source
has an invertible free comparison. -/
theorem isIso_forgetFreeComparison (X : DerivedCategory C)
    [PreservesColimit
      (Discrete.functor fun n ↦ (Free.objFunctor F n).mapDerivedCategory.obj X) R] :
    IsIso (forgetFreeComparison RW R e X) := by
  have : (forget G).mapDerivedCategory.ReflectsIsomorphisms :=
    (freeWeil_derived_properties G).2.2.2.1
  suffices IsIso ((forget G).mapDerivedCategory.map (forgetFreeComparison RW R e X)) from
    isIso_of_reflects_iso _ (forget G).mapDerivedCategory
  let Z := R.obj X
  have hd₀ := (isColimitMapCoconeCofanMkEquiv R _ _)
    (isColimitOfPreserves R (isColimitDerivedFreeCofan F X))
  let q (n : ℤ) := R.map ((derivedFreeSummand F n).app X) ≫
    e.inv.app ((Free.functor F).mapDerivedCategory.obj X)
  have hd : IsColimit (Cofan.mk _ q) :=
    isColimitCofanMkOfIso hd₀ (fun n ↦ Iso.refl _)
      (e.app ((Free.functor F).mapDerivedCategory.obj X))
      (fun n ↦ by
        simp only [q, Category.assoc, Iso.app_hom, Iso.inv_hom_id_app, Iso.refl_hom,
          Category.id_comp]
        exact Category.comp_id _)
  obtain ⟨ζG, hζG⟩ := exists_iso_derivedFreeSummand_zero G Z
  obtain ⟨ζF, hζF⟩ := exists_iso_derivedFreeSummand_zero F X
  have ht (n : ℤ) := exists_iso_summand_comp_eq G.mapDerivedCategory
    (fun n ↦ (derivedFreeSummand G n).app Z) q
    ((derivedStrIso G).hom.app ((Free.functor G).mapDerivedCategory.obj Z))
    ((derivedStrIso G).hom.app
      (RW.obj ((Free.functor F).mapDerivedCategory.obj X)))
    (fun n ↦ (derivedFreeSummandSuccIso G n).app Z)
    (fun n ↦ R.mapIso ((derivedFreeSummandSuccIso F n).app X) ≪≫
      (χ.app _).symm)
    (fun n ↦ derivedFreeSummand_succ G n Z)
    (fun n ↦ by
      simp only [q, derivedFreeSummand_succ F n X, Functor.map_comp, Category.assoc,
        Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]
      rw [map_derivedStrIso_comp_forgetComparison_inv RW R e χ hσ]
      erw [χ.inv.naturality_assoc]
      rfl)
    ((forget G).mapDerivedCategory.map (forgetFreeComparison RW R e X))
    ((derivedStrIso G).hom.naturality (forgetFreeComparison RW R e X))
    (ζG ≪≫ R.mapIso ζF.symm)
    (by
      simp only [hζG, q, hζF, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
        ← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
      exact congrArg (ζG.hom ≫ ·) (unit_app_comp_map_forgetFreeComparison RW R e X))
    n
  choose t ht using ht
  exact isIso_of_cofan_inj_comp_eq (isColimitDerivedFreeCofan G Z) hd _ t ht


end CategoryTheory.Endofunctor.IsoAlgebra
