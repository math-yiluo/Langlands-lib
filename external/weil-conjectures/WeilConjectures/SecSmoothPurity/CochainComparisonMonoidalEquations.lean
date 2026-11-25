/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrows
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations

set_option linter.privateModule false

/-! # Monoidal equations for the canonical cochain comparison

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option Elab.async false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local instance] HomologicalComplex.monoidalCategoryStruct

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

section Generic
variable {A : Type uE} [Category.{vE} A] [MonoidalCategory A]
  {B : Type uD} [Category.{vD} B] [MonoidalCategory B]

end Generic

-- The graded tensor coproduct choices are shared throughout this module.
private theorem gradedTensorR (X Y : GradedObject ℤ (Modules R)) : X.HasTensor Y :=
  inferInstance
private theorem gradedTensorS (X Y : GradedObject ℤ (Modules S)) : X.HasTensor Y :=
  inferInstance
private theorem gradedTensorFourR (X Y Z W : GradedObject ℤ (Modules R)) :
    GradedObject.HasTensor₄ObjExt X Y Z W := inferInstance
private theorem gradedTensorFourS (X Y Z W : GradedObject ℤ (Modules S)) :
    GradedObject.HasTensor₄ObjExt X Y Z W := inferInstance

-- The graded tensor coproduct choices are shared throughout this module.
private theorem gradedTensorLeftR (X Y Z : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
private theorem gradedTensorLeftS (X Y Z : GradedObject ℤ (Modules S)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
private theorem gradedTensorRightR (X Y Z : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
private theorem gradedTensorRightS (X Y Z : GradedObject ℤ (Modules S)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
attribute [local instance] gradedTensorR gradedTensorS gradedTensorFourR gradedTensorFourS
  gradedTensorLeftR gradedTensorLeftS gradedTensorRightR gradedTensorRightS

set_option maxHeartbeats 80000 in
-- Normalize the uniquely determined module unit without unfolding the sheaf tensor.
private theorem module_right_unit (f : RingedPullback R S) (k : Comparison f)
    (M : Modules R) :
    (k.mu M (𝟙_ _)).hom ≫ (𝟙 _ ⊗ₘ (moduleUnit f k).hom) ≫
      (ρ_ (f.L.obj M)).hom = f.L.map (ρ_ M).hom :=
  (Classical.choose_spec
    (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit
      R S f.RI f.uInv f.I f.coefficient f.L f.hobj f.hmap k)).1 M

attribute [local irreducible] SheafOfModules.monoidalCategory

end CategoryTheory.CochainPullback
