/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate

/-! # Composition of coefficient restriction and ordinary pullback -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_comapUpperStarIsoComposition
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
private lemma comap_lowerStar_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :
    (Mod.comap (coefficientMap a Z)).map ((lowerStarComp Λ' f g).hom.app K) ≫
        (comapLowerStarIso a (f ≫ g)).hom.app K =
      (comapLowerStarIso a g).hom.app ((f)_*⟦Λ'⟧.obj K) ≫
        (g)_*⟦Λ⟧.map ((comapLowerStarIso a f).hom.app K) ≫
        (lowerStarComp Λ f g).hom.app ((Mod.comap (coefficientMap a X)).obj K) := by
  apply Mod.hom_ext
  change ((lowerStarComp Λ' f g).hom.app K).hom ≫
      ((comapLowerStarIso a (f ≫ g)).hom.app K).hom =
    ((comapLowerStarIso a g).hom.app ((f)_*⟦Λ'⟧.obj K)).hom ≫
      (g)_*[Ab.{u + 1}].map (((comapLowerStarIso a f).hom.app K).hom) ≫
      ((lowerStarComp Λ f g).hom.app ((Mod.comap (coefficientMap a X)).obj K)).hom
  simp only [comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom]
  change ((lowerStarComp Λ' f g).hom.app K).hom ≫ 𝟙 _ =
    𝟙 _ ≫ (g)_*[Ab.{u + 1}].map (𝟙 _) ≫
      ((lowerStarComp Λ f g).hom.app ((Mod.comap (coefficientMap a X)).obj K)).hom
  erw [Category.comp_id]

private lemma upperStarComp_conjugate
    (S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((upperStarLowerStarAdjunction S g).comp
      (upperStarLowerStarAdjunction S f)) (upperStarLowerStarAdjunction S (f ≫ g))
      (upperStarComp S f g).hom = (lowerStarComp S f g).hom := by
  simp only [upperStarComp, Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv,
    Equiv.apply_symm_apply, Iso.symm_inv]

private lemma upperStarComp_inv_conjugate
    (S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (upperStarLowerStarAdjunction S (f ≫ g))
      ((upperStarLowerStarAdjunction S g).comp (upperStarLowerStarAdjunction S f))
      (upperStarComp S f g).inv = (lowerStarComp S f g).inv := by
  simp only [upperStarComp, Iso.symm_inv, conjugateIsoEquiv_symm_apply_hom,
    Equiv.apply_symm_apply, Iso.symm_hom]

-- The mate comparison repeats typeclass searches for module-object adjunctions.
/-- Composition coherence for the ordinary coefficient-restriction comparison.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-comap-upper-star-iso-composition)

Proof. Replace extension along each coefficient-pullback isomorphism by restriction
along its inverse. The coefficient-map composition identity identifies the transported
actions. Under the faithful module forgetful functor, the restriction comparisons have
identity components. Transpose the specified upperStarComp under the ordinary pull/push
adjunctions; its transpose is lowerStarComp by definition of upperStarComp. The
restriction and pushforward comparisons have identity underlying maps and satisfy
composition. Transpose back and apply faithfulness. -/
theorem comapUpperStarIso_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ' Z)) :
    (upperStarComp Λ f g).hom.app ((Mod.comap (coefficientMap a Z)).obj N) =
      (comapUpperStarIso a (f ≫ g)).inv.app N ≫
        (Mod.comap (coefficientMap a X)).map
          ((upperStarComp Λ' f g).hom.app N) ≫
        (comapUpperStarIso a f).hom.app ((g)^*⟦Λ'⟧.obj N) ≫
        (f)^*⟦Λ⟧.map ((comapUpperStarIso a g).hom.app N) := by
  let αf := TwoSquare.mk _ _ _ _ (comapUpperStarIso a f).inv
  let αg := TwoSquare.mk _ _ _ _ (comapUpperStarIso a g).inv
  let αfg := TwoSquare.mk _ _ _ _ (comapUpperStarIso a (f ≫ g)).inv
  have h : TwoSquare.vComp αg αf =
      (αfg.whiskerLeft (upperStarComp Λ' f g).hom).whiskerRight
        (upperStarComp Λ f g).inv := by
    apply (mateEquiv
      ((upperStarLowerStarAdjunction Λ' g).comp (upperStarLowerStarAdjunction Λ' f))
      ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))).injective
    rw [mateEquiv_hcomp,
      mateEquiv_conjugateEquiv_vcomp _ (upperStarLowerStarAdjunction Λ (f ≫ g)),
      conjugateEquiv_mateEquiv_vcomp _ (upperStarLowerStarAdjunction Λ' (f ≫ g))]
    simp only [αf, αg, αfg, comapUpperStarIso_mate, upperStarComp_conjugate,
      upperStarComp_inv_conjugate]
    refine NatTrans.ext (funext fun K ↦ ?_)
    simp only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.mk, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    rw [← Category.assoc, comap_lowerStar_comp, Category.assoc, Category.assoc,
      Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hN := congrArg (fun s ↦ s.app N) h
  simp only [αf, αg, αfg, TwoSquare.vComp, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.mk, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id] at hN
  have hh := congrArg (fun k ↦
    (upperStarComp Λ f g).hom.app ((Mod.comap (coefficientMap a Z)).obj N) ≫ k ≫
      (comapUpperStarIso a f).hom.app ((g)^*⟦Λ'⟧.obj N) ≫
        (f)^*⟦Λ⟧.map ((comapUpperStarIso a g).hom.app N)) hN
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc] at hh
  have hm := (f)^*⟦Λ⟧.map_id ((Mod.comap (coefficientMap a Z) ⋙ (g)^*⟦Λ⟧).obj N)
  rw [hm] at hh
  exact (Category.comp_id _).symm.trans hh

end AlgebraicGeometry.ProEtale.CondensedRing
