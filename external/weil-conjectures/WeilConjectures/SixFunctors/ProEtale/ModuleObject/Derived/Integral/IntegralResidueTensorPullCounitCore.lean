/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorPullPresentation
public import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorModel
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorPullCounitCore

/-! The normalized middle composite for the residue tensor-pull counit.

Source: Bhatt--Scholze, Remark 6.8.15 and the proof of Lemma 6.5.9(5), p. 51.
(blueprint: new-integral-residue-tensor-pull-counit-core)
-/

@[expose] public section

universe v u u₁ u₂
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance] CategoryTheory.derivedTensorPresentationBraiding
noncomputable section GenericNormalization
variable {C : Type u₁} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

private theorem tensorPresentation_fac (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    (derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Qh.obj P) ≫
      (β_ ((DerivedCategory.singleFunctor C 0).obj B) (DerivedCategory.Qh.obj P)).inv ≫
      (Functor.tensorModelCoefficientIso B).hom ▷ DerivedCategory.Qh.obj P ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh (Functor.tensorModelCoefficient B) P =
      ε.app P ≫ DerivedCategory.Qh.map ((homotopyTensorSingleIso B).inv.app P) := by
  simpa only [Functor.tensorModelCoefficientIso] using
    derivedTensorPresentationIso_fac B H ε P

variable {D : Type u₂} [Category.{v + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]

omit [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C] in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorPullCounit_fac_port (F : C ⥤ D) [F.Additive]
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (γ : DerivedCategory.Qh ⋙ G ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (B : C) (B' : D)
    (c : G.obj ((DerivedCategory.singleFunctor C 0).obj B) ≅
      (DerivedCategory.singleFunctor D 0).obj B')
    (eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
      Functor.tensorModelCoefficient B')
    (hc : c.inv ≫ G.map (Functor.tensorModelCoefficientIso B).hom ≫
      γ.app (Functor.tensorModelCoefficient B) =
        (Functor.tensorModelCoefficientIso B').hom ≫ DerivedCategory.Qh.map eH.inv)
    (H : DerivedCategory D ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso D (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    (derivedTensorPresentationIso B' H ε).hom.app
        (G.obj (DerivedCategory.Qh.obj P)) ≫
      ((curriedTensor (DerivedCategory D)).flip.mapIso c.symm).hom.app
        (G.obj (DerivedCategory.Qh.obj P)) ≫
      Functor.tensorModelTargetWith F G γ B P =
      H.map (γ.app P) ≫
        ε.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map
          ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
            eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P) := by
  unfold Functor.tensorModelTargetWith
  simp only [Functor.mapIso_hom, Functor.flip_map_app,
    curriedTensor_obj_map, Iso.symm_hom]
  erw [BraidedCategory.braiding_inv_naturality_right_assoc]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc]
  rw [hc]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc,
    ← BraidedCategory.braiding_inv_naturality_left_assoc]
  have hn := (derivedTensorPresentationIso B' H ε).hom.naturality
    (γ.app P)
  dsimp only [Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app] at hn
  erw [← reassoc_of% hn]
  erw [Functor.LaxMonoidal.μ_natural_left]
  simp only [Functor.map_comp]
  erw [reassoc_of% tensorPresentation_fac B' H ε
    ((F.mapHomotopyCategory (.up ℤ)).obj P)]

end GenericNormalization
local instance instEssentiallySmallProfinite_integralIntegralResidueTensorPullCounitCore
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

attribute [local instance 20000] sheafBraidedCategory
attribute [local instance 20000] Functor.tensorModelDerivedMonoidal
  Functor.tensorModelHomotopyMonoidal
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- The coefficient-adjusted tensor model composite factors through the inverse of
its X tensor presentation.  This is the middle identity used to normalize the
full tensor-pull counit.  It is strictly weaker than the target identity: the
X presentation map is absent from the left side and its inverse is present on
the right.

The proof expands the exact-F coefficient comparison and the two defining
left-derived comparison equations.  Naturality of the tensorator and of the
lax map of `DerivedCategory.Qh` moves the coefficient comparison to the first
factor; the defining equation for `derivedTensorPresentationIso` then gives the
presentation counit.  The remaining maps are the displayed homotopy single
comparison and the homotopy image of the ordinary coefficient isomorphism.
This is the explicit formal calculation from Remark 6.8.15, with no flatness
assumption.
(blueprint: new-integral-residue-tensor-pull-counit-core) -/
theorem integralResidue_tensorPullCounit_core {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let B := residueExchangeOrdinaryCoefficient ℓ E Y
    let B' := residueExchangeOrdinaryCoefficient ℓ E X
    let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
    let e : F.obj B ≅ B' :=
      residueOrdinaryRestrictedRegularPullIso (integralCoeff ℓ E) A
        (integralReductionMap ℓ E) f
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
      Functor.tensorModelCoefficient B' := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj B) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    let H := residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X
    let εX : DerivedCategory.Qh ⋙ H ⟶
        (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
      residueExchangeTensorCounit ℓ E X
    let M := DerivedCategory.Qh.obj P
    let a : (residueExchangeUpperStar (integralCoeff ℓ E) f).obj M ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P) :=
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P
    let N :=
      ((curriedTensor (residueExchangeDerived (integralCoeff ℓ E) X)).flip.mapIso
        (residueExchangeCoefficientPullIso ℓ E f).symm).hom.app
          ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫
        residueExchangeTensorModelTarget ℓ E f P
    let R := H.map a ≫
      εX.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
      ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P)
    N = (residueExchangeTensorIso ℓ E X).inv.app
      ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫ R := by
  intro F B B' A e eH H εX M a N R
  apply ((residueExchangeTensorIso ℓ E X).app
    ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M)).eq_inv_comp.mpr
  simp only [Iso.app_hom]
  have := residueExchangeTensorCounit_isLeftDerivedFunctor ℓ E X
  have hc := residueExchangeCoefficientPullIso_counit ℓ E f
  dsimp only at hc
  dsimp -zetaDelta -zeta only [N, R, a, M, εX]
  let G := residueExchangeUpperStar (integralCoeff ℓ E) f
  let γ := residueExchangeUpperStarCounit (integralCoeff ℓ E) f
  let c := residueExchangeCoefficientPullIso ℓ E f
  -- Use the category data of the presentation for the generic specialization.
  -- The kernel checks the application and its conversion to the concrete goal.
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let some tx := target.find? (fun e =>
      e.isAppOf ``residueExchangeTensorIso) | throwError "tensor presentation absent"
    let y ← Lean.Meta.getLocalDeclFromUserName `Y
    let mut ys := tx.getAppArgs
    ys := ys.set! (ys.size - 1) y.toExpr
    let ty := Lean.mkAppN tx.getAppFn ys
    let unfoldPresentation (e : Lean.Expr) : Lean.MetaM (Array Lean.Expr) := do
      let some value ← Lean.Meta.withTransparency .all
          (Lean.Meta.unfoldDefinition? e) |
        throwError "tensor presentation constructor unavailable"
      let mut value := value
      for _ in [:20] do
        match value with
        | .letE _ _ v body _ => value := body.instantiate1 v
        | .mdata _ body => value := body
        | _ => pure ()
      let some generic := value.find? (fun a =>
        a.isAppOf ``CategoryTheory.derivedTensorPresentationIso) |
          throwError "generic tensor constructor absent"
      pure generic.getAppArgs
    let dx ← unfoldPresentation tx
    let cy ← unfoldPresentation ty
    let localExpr (n : Lean.Name) : Lean.MetaM Lean.Expr := do
      pure (← Lean.Meta.getLocalDeclFromUserName n).toExpr
    let F ← localExpr `F
    let additiveType ← Lean.Meta.mkAppM ``CategoryTheory.Functor.Additive #[F]
    let additive ← Lean.Meta.synthInstance additiveType
    let x ← localExpr `X
    let .const _ (level :: _) := (← Lean.Meta.inferType x).getAppFn |
      throwError "scheme universe absent"
    let info ← Lean.getConstInfo ``tensorPullCounit_fac_port
    let levels := info.levelParams.map fun n =>
      if n == `v then level else Lean.Level.succ (Lean.Level.succ level)
    let fn := Lean.mkConst ``tensorPullCounit_fac_port levels
    -- Four parameters specify C and its category, abelian and Grothendieck data.
    -- Nine specify D with its monoidal, closed, braided and flat-resolution data.
    -- The final constructor arguments are B', H, epsilon and its derived property.
    let args := cy[:4].toArray ++ dx[:9].toArray ++ #[F, additive,
      ← localExpr `G, ← localExpr `γ, ← localExpr `B, dx[9]!,
      ← localExpr `c, ← localExpr `eH, ← localExpr `hc,
      dx[10]!, dx[11]!, dx[12]!, ← localExpr `P]
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkAppN fn args)

end AlgebraicGeometry.ProEtale.CondensedRing
