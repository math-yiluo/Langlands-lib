/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions

/-! # Ordered exchange for a normalized realization system

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15.
(blueprint: lem-weil-pbc-condensed-e-exchange-mate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] _root_.instCategoryDerivedCategory
  AlgebraicGeometry.ProEtale.upperStar CategoryTheory.Functor.mapMod
  DerivedCategory.homologyFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible]
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarComp
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcCompletedModulesLinear
  AlgebraicGeometry.Scheme.pbcCompletedDerivedLinear
  AlgebraicGeometry.Scheme.pbcIntegralLinear

set_option allowUnsafeReducibility true in
attribute [local reducible] AlgebraicGeometry.Scheme.completedReductionCoefficient
  AlgebraicGeometry.Scheme.reductionCoefficientSystem
  AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.reductionRingModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.AdicCoefficientDatum.pull

attribute [local instance 40000] AlgebraicGeometry.Scheme.reductionRingModulesHasDerivedCategory

set_option allowUnsafeReducibility true in
attribute [local irreducible] AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPull
  AlgebraicGeometry.Scheme.AdicCoefficientDatum.ordinaryToCompleted
  AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPullComp
  AlgebraicGeometry.Scheme.AdicCoefficientDatum.pullId
  AlgebraicGeometry.Scheme.AdicCoefficientDatum.pullComp

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped TensorProduct
namespace WeilConjectures
namespace CondensedERealization

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
variable (D : Data l E k)
variable {X' X Y' Y : Base k}
variable {g' : X'.scheme ⟶ X.scheme} {f' : X'.scheme ⟶ Y'.scheme}
  {f : X.scheme ⟶ Y.scheme} {g : Y'.scheme ⟶ Y.scheme}
variable [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]

private theorem ulift_localization_module (A : Type*) [CommRing A]
    (p : ULift.{u + 1} A) :
    (ULift.module : Module (ULift.{u + 1} A) (Localization.Away p)) =
      (OreLocalization.instModuleOfIsScalarTower :
        Module (ULift.{u + 1} A) (Localization.Away p)) := by
  apply Module.ext'
  intro a x
  induction x using OreLocalization.ind with
  | _ b s => simp only [ULift.smul_def, OreLocalization.smul_oreDiv]

/-- Bundle morphisms so equality transports pullbacks. Source: Stacks Tag 07A7.
(blueprint: lem-weil-pbc-condensed-e-exchange-mate). -/
def integralPullOnOverHom (T U : Base k)
    (h : { h : T.scheme ⟶ U.scheme // h.IsOver (Spec (.of k)) }) :
    Integral l E U.scheme ⥤ Integral l E T.scheme :=
  letI : h.val.IsOver (Spec (.of k)) := h.property
  (D.along T U h.val).pull

/-- The square built from the specified integral compositors. Source: Stacks Tag 07A7.
(blueprint: lem-weil-pbc-condensed-e-exchange-mate). -/
def integralSquare (sq : CommSq g' f' f g) :
    (D.along Y' Y g).pull ⋙ (D.along X' Y' f').pull ≅
      (D.along X Y f).pull ⋙ (D.along X' X g').pull :=
  (D.integralComp X' Y' Y f' g).symm ≪≫
    eqToIso (congrArg (integralPullOnOverHom l E k D X' Y) (Subtype.ext
      (a1 := (⟨f' ≫ g, inferInstance⟩ :
        { h : X'.scheme ⟶ Y.scheme // h.IsOver (Spec (.of k)) }))
      (a2 := (⟨g' ≫ f, inferInstance⟩ :
        { h : X'.scheme ⟶ Y.scheme // h.IsOver (Spec (.of k)) })) sq.w.symm)) ≪≫
      D.integralComp X' X Y g' f

private lemma tensor_eqToHom (T U : Base k)
    (h j : { h : T.scheme ⟶ U.scheme // h.IsOver (Spec (.of k)) })
    (e : h = j) (K : Integral l E U.scheme) :
    (eqToIso (congrArg (Data.pullOnOverHom l E k D T U) e)).hom.app
        (ScalarLocalization.mk K) =
      (ScalarLocalization.localization (PbcIntegralRing l E) (Integral l E T.scheme)
        (pbcUniformizer l E)).map
        ((eqToIso (congrArg (integralPullOnOverHom l E k D T U) e)).hom.app K) := by
  cases e
  rfl

private lemma rationalComp_inv (T U V : Base k) (h : T.scheme ⟶ U.scheme)
    [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme)
    [j.IsOver (Spec (.of k))] (K : Integral l E V.scheme) :
    (D.rationalComp T U V h j).inv.app (ScalarLocalization.mk K) =
      (ScalarLocalization.localization (PbcIntegralRing l E) (Integral l E T.scheme)
        (pbcUniformizer l E)).map ((D.integralComp T U V h j).inv.app K) := by
  have hh := D.rationalComp_normalization T U V h j K
  rw [ulift_localization_module] at hh
  dsimp only [Along.rationalPull, ScalarLocalization.transport, Functor.comp_obj,
    ScalarLocalization.localization] at hh ⊢
  have he := eq_of_heq hh
  apply (cancel_epi ((D.rationalComp T U V h j).hom.app (ScalarLocalization.mk K))).1
  rw [Iso.hom_inv_id_app]
  rw [he]
  change _ = (ScalarLocalization.localization (PbcIntegralRing l E)
    (Integral l E T.scheme) (pbcUniformizer l E)).map
      ((D.integralComp T U V h j).hom.app K) ≫
    (ScalarLocalization.localization (PbcIntegralRing l E)
      (Integral l E T.scheme) (pbcUniformizer l E)).map
        ((D.integralComp T U V h j).inv.app K)
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  symm
  apply CategoryTheory.Functor.map_id

private lemma square_tensor (sq : CommSq g' f' f g) (K : Integral l E Y.scheme) :
    (Data.square l E k D sq).hom.app (ScalarLocalization.mk K) =
      (ScalarLocalization.localization (PbcIntegralRing l E) (Integral l E X'.scheme)
        (pbcUniformizer l E)).map ((integralSquare l E k D sq).hom.app K) := by
  have hc := D.rationalComp_normalization X' X Y g' f K
  rw [ulift_localization_module] at hc
  dsimp only [Along.rationalPull, ScalarLocalization.transport, Functor.comp_obj] at hc
  have hc' := eq_of_heq hc
  dsimp only [Data.square, integralSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Along.rationalPull, ScalarLocalization.transport, Functor.comp_obj]
  have he := tensor_eqToHom l E k D X' Y
    ⟨f' ≫ g, inferInstance⟩ ⟨g' ≫ f, inferInstance⟩ (Subtype.ext sq.w.symm) K
  have hi := rationalComp_inv l E k D X' Y' Y f' g K
  let F := ScalarLocalization.localization (PbcIntegralRing l E)
    (Integral l E X'.scheme) (pbcUniformizer l E)
  calc
    _ = F.map ((D.integralComp X' Y' Y f' g).inv.app K) ≫
        F.map ((eqToIso (congrArg (integralPullOnOverHom l E k D X' Y)
          (Subtype.ext (a1 := (⟨f' ≫ g, inferInstance⟩ :
            { h : X'.scheme ⟶ Y.scheme // h.IsOver (Spec (.of k)) }))
            (a2 := (⟨g' ≫ f, inferInstance⟩ :
              { h : X'.scheme ⟶ Y.scheme // h.IsOver (Spec (.of k)) })) sq.w.symm))).hom.app K) ≫
        F.map ((D.integralComp X' X Y g' f).hom.app K) := by
      exact congrArg₂ (fun a b ↦ a ≫ b) hi
        (congrArg₂ (fun a b ↦ a ≫ b) he hc')
    _ = _ := by rw [F.map_comp, F.map_comp]

end CondensedERealization
end WeilConjectures
