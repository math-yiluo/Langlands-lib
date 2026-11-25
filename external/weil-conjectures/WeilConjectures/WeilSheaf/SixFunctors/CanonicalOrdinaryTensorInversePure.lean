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

/-! # The inverse tensor comparison on pure tensors

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

section HomParam

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u + 1})
  (E : ProEtale.AdicSheaf l Y ≌ RingedTensorModules.{u + 1, u + 1, u + 1} J R)

/-- The Hom comparison parameter of `OrdinaryRingedTensorUnderivedData`, with its type
elaborated exactly as the structure parameter. -/
private def homParam
    (H : Functor.uncurry.obj (ordinaryIhomBifunctor l Y) ⋙ E.functor ≅
      E.functor.op.prod E.functor ⋙ Functor.uncurry.obj (SheafOfModules.homFunctor (R := R))) :
    Functor.uncurry.obj (ordinaryIhomBifunctor l Y) ⋙ E.functor ≅
      E.functor.op.prod E.functor ⋙ Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)) :=
  H

end HomParam

/-- `kIso` at the type of the Hom comparison parameter, so that statements using it do not
convert the two presentations of the ringed module category. -/
private def kIsoParam (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [(WeilFrobeniusAction.topology Y).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (H : ProEtale.AdicModuleHomComparisonCore l Y) :=
  homParam l Y (WeilFrobeniusAction.topology Y) (ProEtale.NativeFrobenius.ring Y l)
    (ProEtale.NativeFrobenius.equivalence Y l).symm (kIso l Y H)

-- Explicit native and small-site module comparisons require substantial elaboration.
-- Coefficient and site universes differ in the two module models.
private theorem comparison_pure (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : ProEtale.AdicModuleHomComparisonCore l Y) :
    let E := ProEtale.NativeFrobenius.equivalence Y l
    let R := ProEtale.NativeFrobenius.ring Y l
    letI : E.inverse.Additive := E.inverse_additive
    ∀ (d : OrdinaryRingedTensorUnderivedData l Y (WeilFrobeniusAction.topology Y)
      R E.symm (kIsoParam l Y H))
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
  intro d b ν hb hd P Q V x y
  let E := ProEtale.NativeFrobenius.equivalence Y l
  let f : P ⟶ ((ordinaryIhomBifunctor l Y).obj (op Q)).obj (P ⊗ Q) :=
    ((Mod.ihomAdjunction Q).homEquiv P (P ⊗ Q)) ((b Q P).hom)
  have hc : ((Mod.ihomAdjunction Q).homEquiv P (P ⊗ Q)).symm f = (b Q P).hom :=
    Equiv.symm_apply_apply _ _
  have hi : (d.underived Q P).inv ≫ E.inverse.map (b Q P).hom =
      ν.inv.app (P, Q) := by
    apply (cancel_mono (ν.hom.app (P, Q))).1
    rw [Category.assoc, hd Q P, Iso.inv_hom_id, Iso.inv_hom_id_app]
    rfl
  have hu := d.uncurry Q P (P ⊗ Q) f
  rw [hc] at hu
  change (d.underived Q P).inv ≫ E.inverse.map (b Q P).hom = _ at hu
  rw [hi] at hu
  have hu' := congrArg (fun a ↦ a.val.app (op (AsSmall.up.obj V.unop))
    (pureTensor (E.inverse.obj P) (E.inverse.obj Q)
      (op (AsSmall.up.obj V.unop)) x y)) hu
  change (ν.inv.app (P, Q)).val.app (op (AsSmall.up.obj V.unop)) _ =
    (((SheafOfModules.tensorHomAdjunction (ProEtale.NativeFrobenius.ring Y l)
      (E.inverse.obj Q)).homEquiv (E.inverse.obj P) (E.inverse.obj (P ⊗ Q))).symm
        (E.inverse.map f ≫ (kIso l Y H).hom.app (op Q, P ⊗ Q))).val.app
          (op (AsSmall.up.obj V.unop))
      ((β_ (E.inverse.obj P) (E.inverse.obj Q)).hom.val.app
        (op (AsSmall.up.obj V.unop)) (pureTensor _ _ _ x y)) at hu'
  rw [TensorRestriction.pure_braiding, ringed_uncurry_pure] at hu'
  change _ = (((kIso l Y H).hom.app (op Q, P ⊗ Q)).val.app
    (op (AsSmall.up.obj V.unop)) (f.hom.hom.app V x)).app (op (Over.mk (𝟙 _))) y at hu'
  rw [inverse_comparison_evaluation] at hu'
  have ht := relative_uncurry_pure l Y Q P (P ⊗ Q) f V x y
  rw [hc] at ht
  have hp := congrArg (fun a ↦ a.hom.app V (nativePair P.X Q.X V x y)) (hb Q P)
  change (b Q P).hom.hom.hom.app V
    ((Mod.tensorπ P Q).hom.app V (nativePair P.X Q.X V x y)) = nativePure P Q V x y at hp
  exact hu'.trans (ht.symm.trans hp)

end AlgebraicGeometry.ProEtaleWeilSheaf
