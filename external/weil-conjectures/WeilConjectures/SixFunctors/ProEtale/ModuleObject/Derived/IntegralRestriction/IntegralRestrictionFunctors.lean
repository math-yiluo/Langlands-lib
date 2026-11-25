/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBrownAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Functors for integral line and affine-space purity

These are the published functors of `theorem-f-shriek-ell-adic-coefficients--1`, factored into a
statement-only interface so that its geometric proof steps can import them independently.
The definitions and their signatures are unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The published signed Tate line, transported back to internal modules by the existing
sectionwise module equivalence. No new coefficient line or scalar action is chosen.
Source: blueprint sk-thm-int-restriction-line, Tate twist convention
(blueprint: def-sfb-integral-restriction-functors). -/
def tateLine (X : Scheme.{u}) (d : ℤ) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)).inverse.obj
      (spSignedTwist X _ (spIntegralTwist X ℓ E) d)

/-- The actual functor f^*(-)(d)[2d]: derived pullback, right tensor with the published
Tate line in degree zero, and shift by 2d.
Source: blueprint sk-thm-int-restriction-line, displayed right adjoints
(blueprint: def-sfb-integral-restriction-functors). -/
def pullTwistShift {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) Y ⥤
      IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) X :=
  IntegralCompactSupport.pull (Profinite.padicIntegersRingObj ℓ E.val) f ⋙
    (derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).flip.obj
      ((DerivedCategory.singleFunctor _ 0).obj (tateLine ℓ E X (d : ℤ))) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- Restriction of f^*(-)(d)[2d] to the recorded Loc(Dbc) categories. The membership
witness only restricts its codomain and does not replace any functor or morphism.
Source: blueprint sk-thm-int-restriction-line, localizing-category convention
(blueprint: def-sfb-integral-restriction-functors). -/
def restrictedPull {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X
        ((pullTwistShift ℓ E f d).obj K)) :
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory :=
  (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X).lift
    ((IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).ι ⋙
      pullTwistShift ℓ E f d) (fun K ↦ h K.obj K.property)

/-- Restriction of the actual Rf_* to Loc(Dbc), once its preservation is supplied.
Source: blueprint sk-thm-int-restriction-line, projective-line left adjoint
(blueprint: def-sfb-integral-restriction-functors). -/
def restrictedPush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f).obj K)) :
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory ⥤
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory :=
  (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).lift
    ((IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X).ι ⋙
      IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f)
    (fun K ↦ h K.obj K.property)

/-- Comparison with any Brown right adjoint for the chosen boundary compactification.
Brown's theorem does not choose an adjoint, so its isomorphism class is stated using
its defining adjunction. Quantification over compactifications includes the fixed one.
Source: blueprint sk-thm-int-restriction-line, the two f^! comparisons
(blueprint: def-sfb-integral-restriction-functors). -/
def brownComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory) : Prop :=
  ∀ (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.image (Profinite.padicIntegersRingObj ℓ E.val)
          c.obj.obj).obj K))
    (J : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory),
    Nonempty (IntegralCompactSupport.lowerShriek
      (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ J) → Nonempty (J ≅ G)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
