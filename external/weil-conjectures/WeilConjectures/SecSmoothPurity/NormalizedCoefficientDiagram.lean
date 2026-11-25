/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrows

/-! # Definition interface for simultaneous strict coefficient comparisons

Source: Stacks 03EL and 07A4; the agent calculations in the eight proof steps of
lem-pur-strict-coefficient-comparison-calculus
(auxiliary; not a blueprint node).

The product index records coefficient changes and all inverse-sequence arrows.
Semilinear arrows are written in their scalar-extension adjoint form. Thus they
are arbitrary chain maps out of scalar extension, including zero maps, rather
than only the scalar-extension units. All tensors are the existing sheafified
module tensor and its signed direct-sum total complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] CategoryTheory.CochainPullback.extensionAdjunction
attribute [local irreducible] CategoryTheory.CochainPullback.extensionFunctor
set_option maxErrors 1
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace CategoryTheory.CochainPullback.StrictCoefficient

/-- Three coefficient rows and an inverse sequence, with all iterated arrows.
Source: the item's statement (auxiliary; not a blueprint node). -/
abbrev Index := Fin 3 × ℕᵒᵖ

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The existing signed direct-sum total tensor, with its instances fixed once.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
noncomputable def total {R : Sheaf J CommRingCat.{w}} (P Q : Complex R) : Complex R := by
  let : ∀ (I₁ I₂ : Type w), HasColimitsOfShape (Discrete I₂)
      (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    fun _ _ ↦ PresheafOfModules.hasColimitsOfShape _ _
  let : HasCoproducts.{0} (Modules R) := fun I ↦ by
    let : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
      PresheafOfModules.hasColimitsOfShape _ _
    exact
      SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  let : HasFiniteCoproducts (Modules R) :=
    hasFiniteCoproducts_of_hasCoproducts (C := Modules R)
  exact P ⊗ Q

/-- The existing tensor map on total complexes, with its instances fixed once.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
abbrev totalMap {R : Sheaf J CommRingCat.{w}} {P Q P' Q' : Complex R}
    (f : P ⟶ P') (g : Q ⟶ Q') : total P Q ⟶ total P' Q' := by
  let : ∀ (I₁ I₂ : Type w), HasColimitsOfShape (Discrete I₂)
      (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    fun _ _ ↦ PresheafOfModules.hasColimitsOfShape _ _
  let : HasCoproducts.{0} (Modules R) := fun I ↦ by
    let : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
      PresheafOfModules.hasColimitsOfShape _ _
    exact
      SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  let : HasFiniteCoproducts (Modules R) :=
    hasFiniteCoproducts_of_hasCoproducts (C := Modules R)
  exact f ⊗ₘ g

/-- Presentation of precisely the ring diagrams in the statement. The fields L,
hobj and hmap present actual scalar extension after the algebraic inverse image;
they are not extra operations or flatness assumptions. The common set adjunction
and the graph equation say that every arrow uses the same geometric morphism.
Source: Stacks 03EL and 07A4
(auxiliary; not a blueprint node). -/
structure Diagram where
  R : Index ⥤ Sheaf J CommRingCat.{w}
  S : Index ⥤ Sheaf K CommRingCat.{w}
  RI : Index ⥤ Sheaf K CommRingCat.{w}
  phi : RI ⟶ S
  inverse : Sheaf J (Type w) ⥤ Sheaf K (Type w)
  direct : Sheaf K (Type w) ⥤ Sheaf J (Type w)
  adj : inverse ⊣ direct
  finiteLimits : PreservesFiniteLimits inverse
  algebraic : ∀ i : Index, SheafOfModules.AlgebraicInverseImage inverse (R.obj i) (RI.obj i)
  graph : ∀ {i j : Index} (t : i ⟶ j),
    inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map (R.map t)) ≫
        (algebraic j).ringUnderlying.hom =
      (algebraic i).ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map (RI.map t)
  L : ∀ i : Index, Modules (R.obj i) ⥤ Modules (S.obj i)
  hobj : ∀ (i : Index) (M : Modules (R.obj i)),
    (L i).obj M = SheafOfModules.changeOfRings (phi.app i) ((algebraic i).modules.obj M)
  hmap : ∀ (i : Index) {M N : Modules (R.obj i)} (f : M ⟶ N),
    (L i).map f = eqToHom (hobj i M) ≫
      SheafOfModules.changeOfRingsHom (phi.app i) ((algebraic i).modules.obj M)
        ((algebraic i).modules.map f) ≫ eqToHom (hobj i N).symm
  V : ∀ i : Index, Modules (S.obj i) ⥤ Modules (R.obj i)
  moduleAdj : ∀ i : Index, L i ⊣ V i
  additive : ∀ i : Index, (L i).Additive

attribute [instance] Diagram.additive

variable (d : Diagram (J := J) (K := K))

variable {d}

end CategoryTheory.CochainPullback.StrictCoefficient
