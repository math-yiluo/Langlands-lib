/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData
public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomNaturality

import all WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomEvaluation
import all WeilConjectures.AlgebraicGeometry.Adic.AdicModuleHomComparisonCore
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionPureTripleExt
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryTensorInverseEvaluation
import all WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryTensorInversePure

/-! # The inverse tensor comparison on pure tensors, canonical form

Source: Stacks 03EK and 03EO, pure tensors and evaluation-normalized inverse mates.
Auxiliary lemmas for `canonical_ordinary_tensor_inverse_associativity`
(blueprint: new-sf-canonical-ordinary-tensor-inverse-associativity).
-/

-- This module only keeps private helpers for the inverse associativity theorem.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures
open CategoryTheory.TwistedActionRingedSite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

-- Elaborating the concrete tensor instances requires large definitional comparisons.
-- The native and ringed tensor instances have separate coefficient and site universes.
/-- `comparison_pure` with its Hom comparison spelled out exactly as in
`canonical_ordinary_tensor_inverse_associativity`, so that the main theorem applies it without
converting between the two presentations. -/
private theorem comparison_pure_canonical
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : ProEtale.AdicModuleHomComparisonCore l Y) :
    let E := ProEtale.NativeFrobenius.equivalence Y l
    let R := ProEtale.NativeFrobenius.ring Y l
    letI : E.inverse.Additive := E.inverse_additive
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    let h : Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)) ⋙ E.functor ≅
        E.functor.op.prod E.functor ⋙ Functor.uncurry.obj (ordinaryIhomBifunctor l Y) :=
      NatIso.ofComponents
      (fun MN ↦ ProEtale.NativeFrobenius.homComparison Y l H MN.1.unop MN.2)
      (fun fg ↦ ProEtale.NativeFrobenius.homComparison_naturality Y l H fg.1.unop fg.2)
    let K := HomComparison.inverseHomComparison E
      (Functor.uncurry.obj (ordinaryIhomBifunctor l Y))
      (Functor.uncurry.obj (SheafOfModules.homFunctor (R := R))) h
    ∀ (d : OrdinaryRingedTensorUnderivedData l Y (WeilFrobeniusAction.topology Y)
        R E.symm K)
      (b : ∀ P Q : ProEtale.AdicSheaf l Y,
        ((ordinaryTensorBifunctor l Y).obj P).obj Q ≅ Q ⊗ P)
      (ν : MonoidalCategory.tensor (ProEtale.AdicSheaf l Y) ⋙ E.inverse ≅
        E.inverse.prod E.inverse ⋙ MonoidalCategory.tensor _),
      (∀ P Q, Mod.tensorπ Q P ≫ (b P Q).hom.hom = Mod.tensorObjπ Q P) →
      (∀ P Q, E.inverse.map (b P Q).hom ≫ ν.hom.app (Q, P) =
        (d.underived P Q).hom) →
      ∀ (P Q : ProEtale.AdicSheaf l Y) (V : Y.ProEtᵒᵖ)
        (x : P.X.obj.obj V) (y : Q.X.obj.obj V),
        (ν.inv.app (P, Q)).val.app (op (AsSmall.up.obj V.unop))
          (pureTensor (E.inverse.obj P) (E.inverse.obj Q)
            (op (AsSmall.up.obj V.unop)) x y) = nativePure P Q V x y := by
  dsimp only
  intro d b ν hb hd
  exact comparison_pure l Y H d b ν hb hd

end AlgebraicGeometry.ProEtaleWeilSheaf
