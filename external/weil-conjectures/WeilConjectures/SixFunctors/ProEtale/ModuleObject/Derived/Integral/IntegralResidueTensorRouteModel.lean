/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorModel

/-! Canonical tensor-route normalization, directly from the tensor/counit square.
Source: Bhatt--Scholze, Lemma 6.5.9(5), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-model)

STATEMENT-DISPUTED: the removed arbitrary-monoidal transport assertion used a fixed
canonical model map on the right. Twisting the ordinary monoidal structure by -1
changes the left side's tensor comparison but leaves that model map unchanged.
The canonical theorem below retains its original statement. -/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Functor.leftDerivedTensorComparison
  DerivedCategory.monoidalClosed Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint Mod.extendScalars
attribute [local irreducible] Functor.residueDerivedMonoidal
attribute [local semireducible] residueExchangeTensorModelTarget
  residueExchangeTensorIso Mod.residueDerivedTensorIso residueExchangeUpperStar
  residueExchangeUpperStarCounit
  residueExchangeReduction
local instance instEssentiallySmallProfinite_integralResidueTensorRouteModel
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
set_option linter.style.haveILetI false in
set_option cleanup.letToHave false in
/-- Compute the tensor-route against the ordinary homotopy tensor model.
Source: Bhatt--Scholze, Lemma 6.5.9(5), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-model)

Proof. Use the counit normalization of the fixed derived tensor presentation.
Move the coefficient single-functor comparison through the tensor comparison by
naturality. Compatibility of the derived tensor comparison with symmetry moves
the fixed coefficient to the first tensor factor. Its defining counit identity
then replaces the derived tensor comparison by Qh of the ordinary tensor
comparison. Naturality of the exact-pullback counit moves the homotopy
single-tensor comparison through it. The resulting composite is precisely
the displayed tensor model map. Every equality is an identity of natural
transformations, so no flatness of the residue coefficient or of P is required. -/
theorem integralResidue_tensorRoute_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    letI := residueExchangePullMonoidal ℓ E f
      (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
    let M := DerivedCategory.Qh.obj P
    (residueExchangeUpperStar (integralCoeff ℓ E) f).map
          ((residueExchangeTensorIso ℓ E Y).hom.app M) ≫
        Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
          M (residueExchangeCoefficient ℓ E Y) ≫
        residueExchangeTensorModelTarget ℓ E f P =
      residueExchangeTensorModelMap ℓ E f P := by
  let F := (f)^*⟦integralCoeff ℓ E⟧
  let G := residueExchangeUpperStar (integralCoeff ℓ E) f
  let γ := residueExchangeUpperStarCounit (integralCoeff ℓ E) f
  letI hfp : F.PreservesFlat := hFlat
  letI hm : F.Monoidal := residueExchangeOrdinaryPullMonoidal ℓ E f
  letI hdm : G.Monoidal := residueExchangePullMonoidal ℓ E f
    (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
  have hG := residueOrdinaryUpperStar_braiding (integralCoeff ℓ E) f
  dsimp only
  -- Preserve the constructors' category data rather than synthesizing copies.
  -- The kernel checks the assembled application and its conversion to this goal.
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let some ty := target.find? (fun e =>
      e.isAppOf ``residueExchangeTensorIso) | throwError "tensor presentation absent"
    let x ← Lean.Meta.getLocalDeclFromUserName `X
    let mut xs := ty.getAppArgs
    xs := xs.set! (xs.size - 1) x.toExpr
    let tx := Lean.mkAppN ty.getAppFn xs
    let presentationArgs (e : Lean.Expr) : Lean.MetaM (Array Lean.Expr) := do
      let some value ← Lean.Meta.withTransparency .all
          (Lean.Meta.unfoldDefinition? e) | throwError "tensor constructor absent"
      let mut value := value
      for _ in [:20] do
        match value with
        | .letE _ _ v body _ => value := body.instantiate1 v
        | .mdata _ body => value := body
        | _ => pure ()
      let some generic := value.find? (fun e =>
        e.isAppOf ``CategoryTheory.derivedTensorPresentationIso) |
          throwError "generic tensor constructor absent"
      pure generic.getAppArgs
    let cy ← presentationArgs ty
    let dx ← presentationArgs tx
    let localExpr (n : Lean.Name) : Lean.MetaM Lean.Expr := do
      pure (← Lean.Meta.getLocalDeclFromUserName n).toExpr
    let F ← localExpr `F
    let propInstance (n : Lean.Name) : Lean.MetaM Lean.Expr := do
      Lean.Meta.synthInstance (← Lean.Meta.mkAppM n #[F])
    let .const _ (level :: _) := (← Lean.Meta.inferType x.toExpr).getAppFn |
      throwError "scheme universe absent"
    let info ← Lean.getConstInfo ``CategoryTheory.Functor.tensorModelRoute_fac
    let levels := info.levelParams.map fun n =>
      if n == `v then level else Lean.Level.succ (Lean.Level.succ level)
    let hdm ← localExpr `hdm
    let some hdv := (← Lean.Meta.getLocalDeclFromUserName `hdm).value? |
      throwError "derived monoidal structure is not a let"
    let some value ← Lean.Meta.withTransparency .all
        (Lean.Meta.unfoldDefinition? hdv) | throwError "pull constructor absent"
    let mut value := value
    for _ in [:20] do
      match value with
      | .letE _ _ v body _ => value := body.instantiate1 v
      | .mdata _ body => value := body
      | _ => pure ()
    let some monoidal := value.find? (fun e =>
      e.isAppOf ``CategoryTheory.Functor.residueDerivedMonoidal) |
        throwError "generic derived monoidal constructor absent"
    let mi ← Lean.getConstInfo ``CategoryTheory.Functor.residueDerivedMonoidal
    let ci ← Lean.getConstInfo ``CategoryTheory.Functor.residueDerivedMonoidal_counit
    let parameterLevels := mi.levelParams.zip monoidal.getAppFn.constLevels!
    let clevels := ci.levelParams.map fun n => (parameterLevels.lookup n).get!
    let hδ := Lean.mkAppN
      (Lean.mkConst ``CategoryTheory.Functor.residueDerivedMonoidal_counit clevels)
      monoidal.getAppArgs
    let fn := Lean.mkConst ``CategoryTheory.Functor.tensorModelRoute_fac levels
    let hdmType ← Lean.Meta.inferType hdm
    let gop := Lean.mkAppN
      (Lean.mkConst ``CategoryTheory.Functor.Monoidal.toOplaxMonoidal
        hdmType.getAppFn.constLevels!) (hdmType.getAppArgs.push hdm)
    let args := cy[:9].toArray ++ dx[:9].toArray ++
      #[F, ← propInstance ``CategoryTheory.Functor.Additive,
        ← propInstance ``CategoryTheory.Limits.PreservesFiniteLimits,
        ← propInstance ``CategoryTheory.Limits.PreservesFiniteColimits,
        ← propInstance ``CategoryTheory.Functor.IsLeftAdjoint, ← localExpr `hm,
        ← localExpr `G, ← localExpr `γ,
        gop,
        hδ, ← localExpr `hG,
        cy[9]!, cy[10]!, cy[11]!, cy[12]!, ← localExpr `P]
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkAppN fn args)

end AlgebraicGeometry.ProEtale.CondensedRing
