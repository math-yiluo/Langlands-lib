/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionData

/-! # The coefficient square for the open tensor projection formula
Source: the open-adjunction and clopen expansion of the coherence proof.
-/
@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

private theorem forward_of_inverse
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {X Y : A} {M N : B} (f : X ≅ Y) (g : M ≅ N)
    (q : R.obj X ⟶ M) (r : R.obj Y ⟶ N)
    (h : r ≫ g.inv = R.map f.inv ≫ q) :
    q ≫ g.hom = R.map f.hom ≫ r := by
  apply (cancel_mono g.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  simp only [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]

end WeilConjectures.OpenInterchangeReduction
