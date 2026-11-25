/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!

# Additivity of the six functors on bounded constructible complexes

The derived pullback `Lf^*`, the derived pushforward `Rf_*`, the extension by zero `j_!` along an
open immersion and the derived lower shriek `Rf_!` on bounded constructible complexes
`Dᵇc(-)⟦Λ⟧` are additive functors. The pullback is a left adjoint; the other functors are
restrictions (`ObjectProperty.lift`) of additive functors on the ambient derived categories, the
right derived functor `R((f)_*⟦Λ⟧)` of an additive functor and the functor `D((j)_!open⟦Λ⟧)`
induced by an exact functor.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The derived pushforward on bounded constructible complexes is additive. -/
instance additive_boundedConstructibleLowerStar (f : X ⟶ Y) :
    (boundedConstructibleLowerStar ℓ f).Additive := by
  unfold boundedConstructibleLowerStar
  infer_instance

/-- The derived pushforward along a proper morphism on bounded constructible complexes is
additive. -/
instance additive_boundedConstructibleLowerStarOfIsProper (f : X ⟶ Y) [IsProper f.left] :
    (boundedConstructibleLowerStarOfIsProper ℓ f).Additive := by
  unfold boundedConstructibleLowerStarOfIsProper
  infer_instance

/-- The derived pullback `Lf^*` on bounded constructible complexes is additive: it is the
restriction of the left adjoint `L((f)^*⟦Λ⟧)` of the additive functor `R((f)_*⟦Λ⟧)`. -/
instance additive_boundedConstructibleUpperStar (f : X ⟶ Y) :
    (boundedConstructibleUpperStar Λ ℓ f).Additive := by
  have := (derivedUpperStarLowerStarAdjunction Λ f.left).left_adjoint_additive
  unfold boundedConstructibleUpperStar
  infer_instance

/-- The extension by zero along an open immersion on bounded constructible complexes is
additive. -/
instance additive_boundedConstructibleOpenImmersionLowerShriek (j : X ⟶ Y)
    [IsOpenImmersion j.left] : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).Additive := by
  unfold boundedConstructibleOpenImmersionLowerShriek
  infer_instance

/-- The lower shriek `Rf_!^c` attached to a compactification is additive. -/
instance additive_boundedConstructibleLowerShriekOfCompactification
    {f : X ⟶ Y}
    (c : Compactification f.left) :
    (boundedConstructibleLowerShriekOfCompactification ℓ c).Additive := by
  unfold boundedConstructibleLowerShriekOfCompactification
  infer_instance

/-- The derived lower shriek on bounded constructible complexes is additive. -/
instance additive_boundedConstructibleLowerShriek (f : X ⟶ Y) :
    (boundedConstructibleLowerShriek ℓ f).Additive := by
  unfold boundedConstructibleLowerShriek
  infer_instance

namespace ContinuousMapRingObj

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The derived pushforward on bounded constructible `E`-complexes is additive. -/
instance additive_boundedConstructibleLowerStar (f : X ⟶ Y) :
    (boundedConstructibleLowerStar ℓ E f).Additive := by
  unfold boundedConstructibleLowerStar
  infer_instance

/-- The derived pushforward along a proper morphism on bounded constructible complexes is
additive. -/
instance additive_boundedConstructibleLowerStarOfIsProper (f : X ⟶ Y) [IsProper f.left] :
    (boundedConstructibleLowerStarOfIsProper ℓ E f).Additive := by
  unfold boundedConstructibleLowerStarOfIsProper
  infer_instance

/-- The lower shriek `Rf_!^c` on bounded constructible `E`-complexes attached to a
compactification is additive. -/
instance additive_boundedConstructibleLowerShriekOfCompactification {f : X ⟶ Y}
    (c : Compactification f.left) :
    (boundedConstructibleLowerShriekOfCompactification ℓ E c).Additive := by
  unfold boundedConstructibleLowerShriekOfCompactification
  infer_instance

/-- The derived lower shriek on bounded constructible `E`-complexes is additive. -/
instance additive_boundedConstructibleLowerShriek (f : X ⟶ Y) :
    (boundedConstructibleLowerShriek ℓ E f).Additive := by
  unfold boundedConstructibleLowerShriek
  infer_instance

end ContinuousMapRingObj

namespace PadicIntegersRingObj

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The derived pushforward on bounded constructible `𝒪_E`-complexes is additive. -/
instance additive_boundedConstructibleLowerStar (f : X ⟶ Y) :
    (boundedConstructibleLowerStar ℓ E f).Additive := by
  unfold boundedConstructibleLowerStar
  infer_instance

/-- The derived pushforward along a proper morphism on bounded constructible complexes is
additive. -/
instance additive_boundedConstructibleLowerStarOfIsProper (f : X ⟶ Y) [IsProper f.left] :
    (boundedConstructibleLowerStarOfIsProper ℓ E f).Additive := by
  unfold boundedConstructibleLowerStarOfIsProper
  infer_instance

/-- The lower shriek `Rf_!^c` on bounded constructible `𝒪_E`-complexes attached to a
compactification is additive. -/
instance additive_boundedConstructibleLowerShriekOfCompactification {f : X ⟶ Y}
    (c : Compactification f.left) :
    (boundedConstructibleLowerShriekOfCompactification ℓ E c).Additive := by
  unfold boundedConstructibleLowerShriekOfCompactification
  infer_instance

/-- The derived lower shriek on bounded constructible `𝒪_E`-complexes is additive. -/
instance additive_boundedConstructibleLowerShriek (f : X ⟶ Y) :
    (boundedConstructibleLowerShriek ℓ E f).Additive := by
  unfold boundedConstructibleLowerShriek
  infer_instance

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
