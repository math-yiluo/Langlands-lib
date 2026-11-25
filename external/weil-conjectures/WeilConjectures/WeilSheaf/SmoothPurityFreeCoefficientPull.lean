/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreePullbackCube
public import WeilConjectures.TateTwist.TateModuleUpperStar
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsCokernelPow

/-! # The free-module pullback comparison commutes with coefficient extension -/

@[expose] public section

universe u v

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory

private lemma purity_adjunction_ofNatIsoRight_refl
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) : adj.ofNatIsoRight (Iso.refl R) = adj := by
  ext X
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.refl_hom, NatTrans.id_app, Functor.comp_obj, Functor.id_obj, Category.comp_id]

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (a : R ⟶ S) [IsMonHom a]

/-- The free-module coefficient comparison is conjugate to the identity on underlying
objects of restricted modules. -/
lemma purity_conjugate_freeFunctorCompExtendScalarsIso :
    conjugateIsoEquiv (freeForgetAdjunction S)
        ((freeForgetAdjunction R).comp (extendRestrictAdjunction a))
        (freeFunctorCompExtendScalarsIso a) = Iso.refl _ := by
  rw [freeFunctorCompExtendScalarsIso, purity_adjunction_ofNatIsoRight_refl,
    Adjunction.leftAdjointUniq, conjugateIsoEquiv_iso_symm]
  erw [Equiv.apply_symm_apply]
  rfl

end Mod

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Pullback of a free module followed by extension of scalars agrees with extension
of scalars followed by pullback, through the canonical free-module comparisons. -/
lemma pullIso_hom_app_free_comp (M : Sheaf (ProEt.topology Y) Ab.{u + 1}) :
    (Mod.extendScalars (coefficientMap a X)).map
          ((freeFunctorCompUpperStarIso Λ g).hom.app M) ≫
        (Mod.freeFunctorCompExtendScalarsIso (coefficientMap a X)).hom.app
          ((g)^*[Ab.{u + 1}].obj M) =
      (pullIso a g).hom.app ((Mod.freeFunctor (condensedRingObj Λ Y)).obj M) ≫
        (g)^*⟦Λ'⟧.map ((Mod.freeFunctorCompExtendScalarsIso (coefficientMap a Y)).hom.app M) ≫
        (freeFunctorCompUpperStarIso Λ' g).hom.app M := by
  apply purity_free_pullback_cube
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g)
    (Mod.freeForgetAdjunction _) (Mod.freeForgetAdjunction _)
    (upperStarLowerStarAdjunction Λ g)
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.freeForgetAdjunction _) (Mod.freeForgetAdjunction _)
    (upperStarLowerStarAdjunction Λ' g)
  intro N
  rw [Mod.purity_conjugate_freeFunctorCompExtendScalarsIso,
    Mod.purity_conjugate_freeFunctorCompExtendScalarsIso]
  simp only [freeFunctorCompUpperStarIso, pullIso, Adjunction.pullIsoOfComapIso,
    Equiv.apply_symm_apply, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  change 𝟙 _ = ((comapLowerStarIso a g).hom.app N).hom
  symm
  exact Mod.comapMapModComapIso_hom_app_hom _ _ _ _ _ _ N

end AlgebraicGeometry.ProEtale.CondensedRing
