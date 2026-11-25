/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarProjectionTransformation
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! Shift compatibility of the scalar-first derived projection map.
(blueprint: lem-sfb-scalar-projection-shift)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing

private abbrev scalarProjectionGeneric
    {C D : Type*} [Category* C] [Category* D]
    [mc : MonoidalCategory C] [md : MonoidalCategory D] {L : D ⥤ C} {R : C ⥤ D}
    (adj : L ⊣ R)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj L).obj L).obj (curriedTensor C)) (K : C) :
    tensorRight (R.obj K) ⟶ (L ⋙ tensorRight K) ⋙ R :=
  (adj.rightAdjointProjectionMap
    (T_C := (curriedTensor C).flip) (T_D := (curriedTensor D).flip)
    ((flipFunctor _ _ _).map δ)).app K

private theorem scalarProjectionGeneric_shift
    {C D : Type*} [Category* C] [Category* D]
    [mc : MonoidalCategory C] [md : MonoidalCategory D]
    [HasShift C ℤ] [HasShift D ℤ] {L : D ⥤ C} {R : C ⥤ D}
    [L.CommShift ℤ] [R.CommShift ℤ] (adj : L ⊣ R) [adj.CommShift ℤ]
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj L).obj L).obj (curriedTensor C)) (K : C)
    [(tensorRight (R.obj K)).CommShift ℤ]
    [(tensorRight K).CommShift ℤ]
    [(tensorRight (L.obj (R.obj K))).CommShift ℤ]
    [NatTrans.CommShift
      (F₁ := tensorRight (R.obj K) ⋙ L)
      (F₂ := L ⋙ tensorRight (L.obj (R.obj K)))
      (Adjunction.comparisonFlipApp δ (R.obj K)) ℤ]
    [NatTrans.CommShift
      (F₁ := tensorRight (L.obj (R.obj K))) (F₂ := tensorRight K)
      ((curriedTensor C).flip.map (adj.counit.app K)) ℤ] :
    NatTrans.CommShift (scalarProjectionGeneric adj δ K) ℤ := by
  have hc : NatTrans.CommShift
      (F₁ := tensorRight (R.obj K) ⋙ L)
      (F₂ := L ⋙ tensorRight (L.obj (R.obj K)))
      (((flipFunctor D D C).map δ).app (R.obj K)) ℤ :=
    inferInstanceAs (NatTrans.CommShift
      (F₁ := tensorRight (R.obj K) ⋙ L)
      (F₂ := L ⋙ tensorRight (L.obj (R.obj K)))
      (Adjunction.comparisonFlipApp δ (R.obj K)) ℤ)
  exact Adjunction.commShift_rightAdjointProjectionMap_app adj
    (T_C := (curriedTensor C).flip) (T_D := (curriedTensor D).flip)
    ((flipFunctor _ _ _).map δ) K

/-- The scalar-first projection commutes with shifts in the coefficient variable.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md, cone paragraph.
Identify the generic derived tensor comparison with the native comparison. Its
first-variable shift compatibility and the shift compatibility of the native derived
adjunction imply that the right-adjoint projection for the flipped tensor bifunctors
commutes with shifts. The tensor action of the counit also commutes with shifts.
(blueprint: lem-sfb-scalar-projection-shift)
-/
theorem scalarProjection_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    NatTrans.CommShift (scalarFirstProjection Λ f K) ℤ := by
  unfold scalarFirstProjection
  let _ := upperStar_preservesFlat Λ f
  rw [← leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison Λ f]
  have := commShift_leftDerivedUpperStarTensor_flipApp Λ f
    (((CondensedRing.lowerStar Λ f).rightDerivedFunctor).obj K)
  apply scalarProjectionGeneric_shift

end AlgebraicGeometry.ProEtale.CondensedRing
