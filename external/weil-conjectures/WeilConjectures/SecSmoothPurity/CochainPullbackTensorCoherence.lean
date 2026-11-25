/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrows
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

set_option linter.privateModule false

/-! # Signed tensor comparison and coherence on cochain sheaves

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and sites-modules.tex,
Tag 03EL (auxiliary; not a blueprint node).

The tensor, associator, Koszul symmetry and action unitors below are the existing
homological-complex constructions. Coefficient arrows are characterized on
scalar-extension generators, and composition uses the adjunction conjugate.
-/

@[expose] public section

universe w uC vC uD vD uE vE uA vA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] extensionFunctor
attribute [local irreducible] SheafOfModules.monoidalCategory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

variable {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

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

-- Three ringed functors require repeated dependent termwise conversions.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end CategoryTheory.CochainPullback

universe r m t
namespace CategoryTheory.CochainPullback

end CategoryTheory.CochainPullback
