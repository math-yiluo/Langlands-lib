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

/-! # Inverse associativity from the inverse comparison on pure tensors

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
private theorem inverse_associativity_of_pure (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    let E := ProEtale.NativeFrobenius.equivalence Y l
    let R := ProEtale.NativeFrobenius.ring Y l
    letI : E.inverse.Additive := E.inverse_additive
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    ∀ (ν : MonoidalCategory.tensor (ProEtale.AdicSheaf l Y) ⋙ E.inverse ≅
        E.inverse.prod E.inverse ⋙ MonoidalCategory.tensor _),
      (∀ (P Q : ProEtale.AdicSheaf l Y) (V : Y.ProEtᵒᵖ)
        (x : P.X.obj.obj V) (y : Q.X.obj.obj V),
        (ν.inv.app (P, Q)).val.app (op (AsSmall.up.obj V.unop))
          (pureTensor (E.inverse.obj P) (E.inverse.obj Q)
            (op (AsSmall.up.obj V.unop)) x y) = nativePure P Q V x y) →
      ∀ P Q N : ProEtale.AdicSheaf l Y,
        (ν.inv.app (P, Q) ▷ E.inverse.obj N) ≫ ν.inv.app (P ⊗ Q, N) ≫
            E.inverse.map (α_ P Q N).hom =
          (α_ (E.inverse.obj P) (E.inverse.obj Q) (E.inverse.obj N)).hom ≫
            (E.inverse.obj P ◁ ν.inv.app (Q, N)) ≫ ν.inv.app (P, Q ⊗ N) := by
  dsimp only
  intro ν hν P Q N
  let E := ProEtale.NativeFrobenius.equivalence Y l
  apply pure_triple_ext
  intro U x y z
  let V : Y.ProEtᵒᵖ := op (AsSmall.down.obj U.unop)
  have hα := CochainPullback.moduleTmul_associator
    (E.inverse.obj P) (E.inverse.obj Q) (E.inverse.obj N) U x y z
  change (α_ (E.inverse.obj P) (E.inverse.obj Q) (E.inverse.obj N)).hom.val.app U
    (pureTensor (E.inverse.obj P ⊗ E.inverse.obj Q) (E.inverse.obj N) U
      (pureTensor (E.inverse.obj P) (E.inverse.obj Q) U x y) z) =
      pureTensor (E.inverse.obj P) (E.inverse.obj Q ⊗ E.inverse.obj N) U x
        (pureTensor (E.inverse.obj Q) (E.inverse.obj N) U y z) at hα
  have hleft := TensorRestriction.pure_map
    (ν.inv.app (P, Q)) (𝟙 (E.inverse.obj N)) U (pureTensor _ _ U x y) z
  have hright := TensorRestriction.pure_map
    (𝟙 (E.inverse.obj P)) (ν.inv.app (Q, N)) U x (pureTensor _ _ U y z)
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hleft hright
  change ((E.inverse.map (α_ P Q N).hom).val.app U)
    ((ν.inv.app (P ⊗ Q, N)).val.app U
      ((ν.inv.app (P, Q) ▷ E.inverse.obj N).val.app U
        (pureTensor (E.inverse.obj P ⊗ E.inverse.obj Q) (E.inverse.obj N) U
          (pureTensor (E.inverse.obj P) (E.inverse.obj Q) U x y) z))) =
    (ν.inv.app (P, Q ⊗ N)).val.app U
      ((E.inverse.obj P ◁ ν.inv.app (Q, N)).val.app U
        ((α_ (E.inverse.obj P) (E.inverse.obj Q) (E.inverse.obj N)).hom.val.app U
          (pureTensor (E.inverse.obj P ⊗ E.inverse.obj Q) (E.inverse.obj N) U
            (pureTensor (E.inverse.obj P) (E.inverse.obj Q) U x y) z)))
  rw [tensorMap, tensorHom_id] at hleft
  rw [tensorMap, id_tensorHom] at hright
  change (ν.inv.app (P, Q) ▷ E.inverse.obj N).val.app U
    (pureTensor (E.inverse.obj P ⊗ E.inverse.obj Q) (E.inverse.obj N) U
      (pureTensor (E.inverse.obj P) (E.inverse.obj Q) U x y) z) =
    pureTensor (E.inverse.obj (P ⊗ Q)) (E.inverse.obj N) U
      ((ν.inv.app (P, Q)).val.app U
        (pureTensor (E.inverse.obj P) (E.inverse.obj Q) U x y)) z at hleft
  change (E.inverse.obj P ◁ ν.inv.app (Q, N)).val.app U
    (pureTensor (E.inverse.obj P) (E.inverse.obj Q ⊗ E.inverse.obj N) U x
      (pureTensor (E.inverse.obj Q) (E.inverse.obj N) U y z)) =
    pureTensor (E.inverse.obj P) (E.inverse.obj (Q ⊗ N)) U x
      ((ν.inv.app (Q, N)).val.app U
        (pureTensor (E.inverse.obj Q) (E.inverse.obj N) U y z)) at hright
  rw [hleft, hα, hright]
  change (α_ P Q N).hom.hom.hom.app V
    ((ν.inv.app (P ⊗ Q, N)).val.app (op (AsSmall.up.obj V.unop))
      (pureTensor (E.inverse.obj (P ⊗ Q)) (E.inverse.obj N)
        (op (AsSmall.up.obj V.unop))
        ((ν.inv.app (P, Q)).val.app (op (AsSmall.up.obj V.unop))
          (pureTensor (E.inverse.obj P) (E.inverse.obj Q)
            (op (AsSmall.up.obj V.unop)) x y)) z)) =
    (ν.inv.app (P, Q ⊗ N)).val.app (op (AsSmall.up.obj V.unop))
      (pureTensor (E.inverse.obj P) (E.inverse.obj (Q ⊗ N))
        (op (AsSmall.up.obj V.unop)) x
        ((ν.inv.app (Q, N)).val.app (op (AsSmall.up.obj V.unop))
          (pureTensor (E.inverse.obj Q) (E.inverse.obj N)
            (op (AsSmall.up.obj V.unop)) y z)))
  rw [hν, hν, hν, hν]
  exact nativePure_associator P Q N V x y z

end AlgebraicGeometry.ProEtaleWeilSheaf
