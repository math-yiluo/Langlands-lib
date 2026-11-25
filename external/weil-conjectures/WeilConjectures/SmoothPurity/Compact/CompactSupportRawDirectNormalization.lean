/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare

/-! # Unit normalization of native direct evaluation

Source: Zheng, Construction 4.1; Stacks 0D6E and 0D6J
(blueprint: lem-weil-compact-support-raw-direct-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.ofSequence Functor.ofOpSequence constantSheaf presheafToSheaf Functor.leftAdjoint
  HasDerivedCategory.standard MorphismProperty.Over.pullback
attribute [local implicit_reducible]
  ProEtale.VaryingRing.coefficientTransition RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.evaluation SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

private theorem cochainUnit_eq
    {A B : Type (v + 1)} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex A ℤ) :
    UnboundedExactTower.cochainUnit F I = F.rightDerivedFunctorUnitQ I := by
  unfold UnboundedExactTower.cochainUnit
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  rfl

-- Native and level module categories share a concrete sequence-site presentation.
/-- Native ordinary direct evaluation satisfies the derived unit equation.
Source: Zheng, Construction 4.1; Stacks 0D6E and 0D6J.
(blueprint: lem-weil-compact-support-raw-direct-normalization).
Proof: moduleEvalG is normalized by the ordinary adjunction units, so the inverse-mate
identity identifies its mate with moduleEvalP. Apply the existing localized mate's
cochain normalization to moduleEvalG.symm. Compose with the evaluation localization
factor, cancel its inverse, and identify the cochain unit with rightDerivedFunctorUnitQ.
Unfolding the specified evalP mate then gives precisely the unit-normalization equation. -/
theorem compactSupportRawDirectNormalization
    (R : ℕ → CommRingCat.{u + 1}) (q : ∀ n, R (n + 1) ⟶ R n)
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (n : ℕ) :
    CategoryTheory.ExactDerivedSquare.unitNormalized.{u + 1, u + 2}
      (ProEtale.VaryingRing.push R q g) (ProEtale.StrictTower.moduleDirectImage (R n) g)
      (ProEtale.VaryingRing.eval R q Z n) (ProEtale.VaryingRing.eval R q Y n)
      (ProEtale.VaryingRing.ev R q Z n) (ProEtale.VaryingRing.ev R q Y n)
      (ProEtale.VaryingRing.eval R q Z n).mapDerivedCategoryFactors
      (ProEtale.VaryingRing.eval R q Y n).mapDerivedCategoryFactors
      (ProEtale.VaryingRing.moduleEvalP R q g n).hom
      (ProEtale.VaryingRing.evalP R q g n).hom := by
  let a := ProEtale.VaryingRing.moduleAdj R q g
  let b := proEtaleRingModuleAdjunction g (ProEtale.VaryingRing.coefficients R Y n)
    (ProEtale.VaryingRing.coefficients R Z n)
    (ProEtale.StrictTower.constantRingIso (R n) g)
  have hm : (mateEquiv a b (TwoSquare.mk _ _ _ _
      (ProEtale.VaryingRing.moduleEvalG R q g n).inv)) =
        (ProEtale.VaryingRing.moduleEvalP R q g n).hom := by
    have hi := ProEtale.VaryingRing.inverseMateEqOfUnit a b
      (ProEtale.VaryingRing.eval R q Y n) (ProEtale.VaryingRing.eval R q Z n)
      (ProEtale.VaryingRing.moduleEvalP R q g n).hom
      (ProEtale.VaryingRing.moduleEvalG R q g n)
      (ProEtale.VaryingRing.moduleEvalG_existsUnique R q g n).choose_spec.1
    have hi' : TwoSquare.mk _ _ _ _
        (ProEtale.VaryingRing.moduleEvalG R q g n).inv =
          (mateEquiv a b).symm (ProEtale.VaryingRing.moduleEvalP R q g n).hom :=
      hi.symm
    rw [hi']
    exact Equiv.apply_symm_apply _ _
  intro I
  have h := UnboundedExactTower.localized_mate_cochain_normalization a b
    (ProEtale.VaryingRing.moduleEvalG R q g n).symm I
  simp only [Iso.symm_hom] at h
  rw [hm] at h
  have h' := congrArg (fun z ↦
    (ProEtale.VaryingRing.eval R q Y n).mapDerivedCategoryFactors.hom.app
      (((ProEtale.VaryingRing.push R q g).mapHomologicalComplex (.up ℤ)).obj I) ≫ z) h
  simp only [Iso.hom_inv_id_app_assoc] at h'
  simp only [cochainUnit_eq] at h'
  dsimp only [UnboundedExactTower.localizedSquare] at h'
  simp only [Iso.trans_hom, Iso.symm_hom] at h'
  erw [Functor.mapDerivedCategoryNatIso_symm
    (ProEtale.VaryingRing.moduleEvalG R q g n)] at h'
  simp only [ProEtale.VaryingRing.evalP, ProEtale.VaryingRing.evalPMate,
    ProEtale.VaryingRing.evalG, ProEtale.VaryingRing.adj, ProEtale.VaryingRing.levelAdj,
    Iso.trans_inv, Iso.symm_inv, Category.assoc] at ⊢
  convert h' using 1 <;> rfl

end WeilConjectures
