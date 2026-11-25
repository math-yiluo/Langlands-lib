/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfbHomFilteredColimit.DerivedInternalHomFilteredColimitData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Transpose of the strict normalized Hom numerator

Source: Stacks Project, sites-cohomology.tex, Tag 08J9, and the strict numerator
calculation in the node (blueprint: lem-sfb-hom-strict-numerator-transpose).
The records below package chain maps and their full representative normalizations;
they do not replace the recorded tensor, Hom, or resolution constructions.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r w w2
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SfbHomFilteredColimit

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
  (R : Sheaf J CommRingCat.{max u v r})

/-- Total-tensor map with its two source and target objects explicit.
Source: Stacks 06YN (blueprint: lem-sfb-hom-strict-numerator-transpose). -/
noncomputable def numeratorTotalMap
    {X Y P Q : CochainComplex (Modules.{u, v, r} J R) ℤ}
    (f : X ⟶ Y) (g : P ⟶ Q) :
    (coefficientTotalTensor.{r, u, v} J R).obj (X, P) ⟶
      (coefficientTotalTensor.{r, u, v} J R).obj (Y, Q) :=
  (coefficientTotalTensor.{r, u, v} J R).map (X := (X, P)) (Y := (Y, Q)) (f, g)

attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory
  PresheafOfModules.sheafification PresheafOfModules.sheafificationAdjunction

variable [HasDerivedCategory.{w} (Modules.{u, v, r} J R)]

section Coefficients

variable (R' : Sheaf J CommRingCat.{max u v r}) (φ : R ⟶ R')
  (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
  (P' L' : CochainComplex (Modules.{u, v, r} J R') ℤ)
  (T : Modules.{u, v, r} J R) (T' : Modules.{u, v, r} J R')

end Coefficients


end WeilConjectures.SfbHomFilteredColimit
