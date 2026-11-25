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
import all WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryTensorInverseCanonical
import all WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryTensorInverseTriple

/-! # Underived associativity of the normalized canonical comparison

Source: Stacks 03EK and 03EO, pure tensors and evaluation-normalized inverse mates.
(blueprint: new-sf-canonical-ordinary-tensor-inverse-associativity).
-/

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
/-- The canonical evaluation normalization forces inverse underived associativity.
Source: Stacks 03EK and 03EO; normalized inverse closed mates.
(blueprint: new-sf-canonical-ordinary-tensor-inverse-associativity).

Proof: expand the prescribed inverse Hom comparison through the equivalence's
unit and counit. The normalized forward evaluation equation, naturality in the
source and target, and the two inverse equations give its evaluation formula on
the identity slice. Apply the underived uncurrying equation to the adjunct of b.
Ordinary uncurrying evaluates a pure tensor on that same identity slice, while
the native quotient equation evaluates it as the corresponding native pure tensor.
Thus nu inverse sends every sheafified pure tensor to that native pure tensor.
Test the desired equation on pure triples. Tensor-map naturality and the two
associator formulas reduce both sides to the same reassociated native pure triple.
Pure-triple extensionality proves equality. No complex comparison is used. -/
theorem canonical_ordinary_tensor_inverse_associativity
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
      ∀ P Q N : ProEtale.AdicSheaf l Y,
        (ν.inv.app (P, Q) ▷ E.inverse.obj N) ≫ ν.inv.app (P ⊗ Q, N) ≫
            E.inverse.map (α_ P Q N).hom =
          (α_ (E.inverse.obj P) (E.inverse.obj Q) (E.inverse.obj N)).hom ≫
            (E.inverse.obj P ◁ ν.inv.app (Q, N)) ≫ ν.inv.app (P, Q ⊗ N) := by
  dsimp only
  intro d b ν hb hd P Q N
  exact inverse_associativity_of_pure l Y ν (comparison_pure_canonical l Y H d b ν hb hd) P Q N

end AlgebraicGeometry.ProEtaleWeilSheaf
