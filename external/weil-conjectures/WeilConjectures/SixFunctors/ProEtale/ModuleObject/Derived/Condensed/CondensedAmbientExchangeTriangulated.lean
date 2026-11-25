/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Triangulated isomorphism locus of the condensed ambient exchange

The ambient exchange is a mate of the shift-compatible inverse-image compositor.
Compatible shifts on its right adjoints make its isomorphism locus triangulated.
Source: the localizing-extension step of the finite-coefficient proper base-change
proof (blueprint: lem-sfb-condensed-ambient-exchange-triangulated).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor CategoryTheory.Obj CategoryTheory.MonoidalClosed

section CachedProofs

attribute [local instance] finiteProperCache1 finiteProperCache2 finiteProperCache3
  finiteProperCache4 finiteProperCache5 finiteProperCache6 finiteProperCache7
  finiteProperCache8 finiteProperCache9 finiteProperCache10 finiteProperCache11 finiteProperCache12
  cachedModuleMonoidal cachedModuleBraided cachedModuleSymmetric cachedDerivedMonoidal
  cachedModuleClosed cachedModuleFlatResolution cachedDerivedTensorStructure

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

section TensorInstanceCache

variable (T : AlgebraicGeometry.Scheme.{u})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

private theorem cachedTensorLeft :
    ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod
      (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance

private theorem cachedTensorRight :
    ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod
      (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance

private theorem cachedTensorColimLeft :
    ∀ M : Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).obj M) := by
  intro M
  infer_instance

private theorem cachedTensorColimRight :
    ∀ M : Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).flip.obj M) := by
  intro M
  infer_instance

omit [IsCommMonObj R] in
private theorem cachedExactIntegerColimits :
    HasExactColimitsOfShape ℤ
      (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

end TensorInstanceCache

attribute [local instance] cachedTensorLeft cachedTensorRight
  cachedTensorColimLeft cachedTensorColimRight cachedExactIntegerColimits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] unboundedLocalizingPullbackCommShift

attribute [local irreducible] CondensedRing.lowerStar CondensedRing.upperStar
  upperStarFromPoint DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategoryStruct
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local irreducible] CondensedRing.condensedAmbientExchange
  CondensedRing.condensedAmbientPullbackComparison CondensedRing.leftDerivedUpperStarComp
  CondensedRing.derivedUpperStarLowerStarAdjunction

namespace CondensedRing

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteProper_normalization_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.CommShift
      (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory.hom ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ
  exact NatTrans.CommShift.of_iso_inv
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteProper_comparison_comp_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.CommShift (leftDerivedUpperStarComp Λ f g).hom ℤ := by
  let := finiteProper_normalization_commShift Λ f
  let := finiteProper_normalization_commShift Λ g
  let := finiteProper_normalization_commShift Λ (f ≫ g)
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_assoc, Iso.symm_self_id_assoc,
    Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

-- Shift synthesis for the exchange mate needs a larger budget.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The isomorphism locus of the specified ambient exchange is triangulated.
No properness or finiteness hypothesis is required for this exactness assertion.
Source: blueprint main-20261015, proposition-proper-base-change-localizing-categories--1,
steps 2--4 (blueprint: lem-sfb-condensed-ambient-exchange-triangulated).

Proof: transport the termwise coherent shifts to each total inverse image through
`leftDerivedUpperStarIsoMapDerivedCategory`. Transport its exactness through the same
isomorphism. For the two derived adjunctions, equip the right adjoints with the unique
compatible shifts; the triangulated right-adjoint theorem supplies their exactness.
The pullback comparison commutes with shifts: after the exact-functor comparisons it
is the localization of the termwise comparison induced by `upperStarComp` and the square
equality. In each degree its component on a shifted complex is its component at the
shifted degree, and additivity respects the signed differential. The derived comparison
is built by precisely these exact-functor identifications. The units and counits commute
with these chosen shifts. Expand `mateEquiv`: its whiskered units, comparison and counit,
and its associators and unitors, all commute with shifts, so their composite does too.
The two composite functors are triangulated. The standard isomorphism-locus theorem
then gives closure under zero, all integer shifts and distinguished triangles. -/
private theorem cached_exchange_isoLocus
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g) :
    (condensedAmbientExchange Λ sq).isoLocus.IsTriangulated := by
  have hcomp : NatTrans.CommShift (condensedAmbientPullbackComparison Λ sq).hom ℤ := by
    have := finiteProper_comparison_comp_commShift Λ p' g
    have := finiteProper_comparison_comp_commShift Λ g' p
    have heq' (f₁ f₂ : X' ⟶ Y) (h : f₁ = f₂) : NatTrans.CommShift
        (eqToIso (congrArg (fun h : X' ⟶ Y ↦ (CondensedRing.upperStar Λ h).leftDerivedFunctor)
          h)).hom ℤ := by
      subst f₂
      change NatTrans.CommShift (𝟙 _) ℤ
      infer_instance
    have := heq' _ _ sq.toCommSq.w.symm
    unfold condensedAmbientPullbackComparison
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have exact_pull {T S : Scheme.{u}} (f : T ⟶ S) :
      (CondensedRing.upperStar Λ f).leftDerivedFunctor.IsTriangulated := by
    have := Functor.CommShift.ofIso_compatibility
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ
    exact Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm
  let := exact_pull p
  let := exact_pull g
  let := exact_pull p'
  let := exact_pull g'
  let a := derivedUpperStarLowerStarAdjunction Λ p
  let a' := derivedUpperStarLowerStarAdjunction Λ p'
  let : (CondensedRing.lowerStar Λ p).rightDerivedFunctor.CommShift ℤ := a.rightAdjointCommShift ℤ
  let : (CondensedRing.lowerStar Λ p').rightDerivedFunctor.CommShift ℤ := a'.rightAdjointCommShift ℤ
  let := a.commShift_of_leftAdjoint ℤ
  let := a'.commShift_of_leftAdjoint ℤ
  let := a.isTriangulated_rightAdjoint
  let := a'.isTriangulated_rightAdjoint
  have : NatTrans.CommShift (condensedAmbientExchange Λ sq) ℤ := by
    unfold condensedAmbientExchange
    exact NatTrans.CommShift.mateEquiv (A := ℤ)
      (G := (CondensedRing.upperStar Λ g).leftDerivedFunctor)
      (H := (CondensedRing.upperStar Λ g').leftDerivedFunctor)
      (L₁ := (CondensedRing.upperStar Λ p).leftDerivedFunctor)
      (R₁ := (CondensedRing.lowerStar Λ p).rightDerivedFunctor)
      (L₂ := (CondensedRing.upperStar Λ p').leftDerivedFunctor)
      (R₂ := (CondensedRing.lowerStar Λ p').rightDerivedFunctor)
      a a' (TwoSquare.mk _ _ _ _ (condensedAmbientPullbackComparison Λ sq).hom)
  exact NatTrans.instIsTriangulatedIsoLocus
    (F₁ := (CondensedRing.lowerStar Λ p).rightDerivedFunctor ⋙
      (CondensedRing.upperStar Λ g).leftDerivedFunctor)
    (F₂ := (CondensedRing.upperStar Λ g').leftDerivedFunctor ⋙
      (CondensedRing.lowerStar Λ p').rightDerivedFunctor)
    (condensedAmbientExchange Λ sq)

end CondensedRing

end AlgebraicGeometry.ProEtale

end CachedProofs

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The specified ambient exchange has a triangulated isomorphism locus.
Source: the localizing extension of finite proper base change
(blueprint: lem-sfb-condensed-ambient-exchange-triangulated).

Proof: the cached argument proves shift compatibility of the pullback comparison,
then of its adjunction mate. Both composite functors are triangulated, and the
isomorphism-locus theorem gives the assertion. No finiteness or properness is used. -/
theorem condensedAmbientExchange_isoLocus_triangulated
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g) :
    (condensedAmbientExchange Λ sq).isoLocus.IsTriangulated := by
  exact cached_exchange_isoLocus Λ sq

end AlgebraicGeometry.ProEtale.CondensedRing
