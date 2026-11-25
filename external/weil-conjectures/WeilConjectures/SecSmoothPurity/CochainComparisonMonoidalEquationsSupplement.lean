/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Monoidal equations for the canonical cochain comparison

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(blueprint: lem-pur-cochain-comparison-monoidal-equations)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

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
private theorem gradedTensorLeftR (X Y Z : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
private theorem gradedTensorLeftS (X Y Z : GradedObject ℤ (Modules S)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
private theorem gradedTensorRightR (X Y Z : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
private theorem gradedTensorRightS (X Y Z : GradedObject ℤ (Modules S)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
attribute [local instance] gradedTensorLeftR gradedTensorLeftS gradedTensorRightR
  gradedTensorRightS

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

@[reassoc]
private theorem comparison_ι (f : RingedPullback R S) (k : Comparison f)
    (P Q : Complex R) (p q n : ℤ) (hpq : p + q = n) :
    f.L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n hpq) ≫
        (comparison f k P Q).hom.f n =
      (k.mu (P.X p) (Q.X q)).hom ≫ CochainComplex.ιMapBifunctor
        ((pull f).obj P) ((pull f).obj Q) (curriedTensor (Modules S)) p q n hpq := by
  apply (cancel_mono ((comparison f k P Q).inv.f n)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, HomologicalComplex.id_f]
  change _ = (k.mu (P.X p) (Q.X q)).hom ≫ _ ≫
    (tensorPullbackTotal f.L k.mu k.naturality P Q).f n
  simp only [tensorPullbackTotal, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc, Iso.hom_inv_id_assoc]
  exact Category.comp_id _

-- Work only with the normalized total comparison, before introducing lifted instances.
-- Assemble the ordinary structure and identify its total comparison.
end CategoryTheory.CochainPullback
