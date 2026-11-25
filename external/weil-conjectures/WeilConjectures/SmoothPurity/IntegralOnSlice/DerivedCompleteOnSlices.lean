/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted

/-!
# Derived completeness on the global pro-etale site and its slices

Source: Bhatt--Scholze, Definition 3.5.2; Stacks Project, Tag 08TC
(blueprint: def-weil-derived-complete).
The slice predicate uses the actual augmented quotient tower, not a guessed map
into an arbitrarily chosen derived limit. The global case is the recorded predicate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t}) (U : Option X.ProEt)

/-- The canonical derived quotient tower of a good representative. Source: Stacks 06YL
(blueprint: def-weil-derived-complete). -/
def derivedTower (P : (Good l E X U).FullSubcategory) : ℕᵒᵖ ⥤ D l E X U :=
  (tower l E X U).obj P.obj ⋙ DerivedCategory.Q

/-- The canonical legs, transported through the representative isomorphism.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: def-weil-derived-complete). -/
def derivedLeg (P : (Good l E X U).FullSubcategory) (K : D l E X U)
    (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ) :
    K ⟶ (derivedTower l E X U P).obj (op n) :=
  e.inv ≫ DerivedCategory.Q.map (((augmentation l E X U).app P.obj).app (op n))

/-- The exact Roos-triangle condition on this site's reduction tower. Source: Stacks 08TC
(blueprint: def-weil-derived-complete). -/
def RoosComplete (K : D l E X U) : Prop :=
  ∃ (P : (Good l E X U).FullSubcategory) (e : DerivedCategory.Q.obj P.obj ≅ K)
    (hprod : HasProduct (fun n : ℕ ↦ (derivedTower l E X U P).obj (op n))),
    (fun [_productInst : HasProduct (fun n : ℕ ↦ (derivedTower l E X U P).obj (op n))] ↦
      ∃ δ : (∏ᶜ fun n : ℕ ↦ (derivedTower l E X U P).obj (op n)) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ (derivedTower l E X U P).map (homOfLE n.le_succ).op) K
          (Pi.lift (derivedLeg l E X U P K e)) δ) (_productInst := hprod)

/-- Derived completeness on either of the two sites. The global branch reuses the
published definition verbatim. On a slice the same positive-exponent quotient tower
and its x mapped to 1 tensor x augmentation give precisely the same Roos condition.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: def-weil-derived-complete). -/
def IsComplete : D l E X U → Prop :=
  match U with
  | none => IsDerivedCompleteUnrestricted l E X
  | some V => RoosComplete l E X (some V)

end WeilConjectures.IntegralOnSlice
