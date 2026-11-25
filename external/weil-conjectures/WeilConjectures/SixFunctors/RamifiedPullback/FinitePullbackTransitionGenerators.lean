/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt

/-! # Finite pullback transitions on tensor generators

Source: Stacks 093M, 03EK and 03EL; Bhatt--Scholze 6.8.2(1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem projection_surjective (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Surjective
      ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U) := by
  intro x
  obtain ⟨a, ha⟩ := AlgebraicGeometry.ProEtale.constantQuotient_surjective l E W n U x
  refine ⟨(integralConstantToCompletionOfUniverses l E W).hom.app U a, ?_⟩
  exact (congrArg (fun h ↦ h.hom.app U a)
    (limit.lift_π (integralConstantConeOfUniverses l E W) (op n))).trans ha

private theorem adjacent {X Y : Scheme.{t}} (g : X ⟶ Y)
    (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (V : Y.ProEt)
    (x : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj (op V))
    (y : (integralCoefficientCommRingSheaf l E X (n + 1)).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)) :
    (((integralOperationsPullbackTransition l E g n).app P).f i).val.app _
        (pullTensor l E g (n + 1) P i V x y p) =
      pullTensor l E g n P i V
        ((integralCoefficientSheafTransition l E Y n).hom.app (op V) x)
        ((integralCoefficientSheafTransition l E X n).hom.app _ y) p := by
  let U := op ((Scheme.proEtaleBaseChange g).obj V)
  obtain ⟨s, hs⟩ := projection_surjective l E X (n + 1) U y
  have hproj :
      (integralCoefficientSheafTransition l E X n).hom.app U y =
        (completedIntegralCommRingProjectionUnrestricted l E X n).hom.app U s := by
    rw [← hs]
    have hw := congrArg (fun h ↦ h.hom.app U s)
      (limit.w (integralCoefficientSheafSystem l E X)
        (homOfLE (Nat.le_succ n)).op)
    simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, RingCat.comp_apply] at hw
    with_unfolding_all exact hw
  have hgen := (integralOperationsPullbackTransition_existsUnique l E g n).exists.choose_spec
    P i V (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) (op V) x p)
  have hred := (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec
    P i (op V) x p
  change ((((unrestrictedIntegralTransition l E Y n).app P).f i).val.app (op V))
    (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) (op V) x p) = _ at hred
  change ((((integralOperationsPullbackTransition l E g n).app P).f i).val.app
    (op ((Scheme.proEtaleBaseChange g).obj V)))
      (integralOperationsPullbackGenerator l E g (n + 1) _ V
        (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) (op V) x p)) = _ at hgen
  rw [hred] at hgen
  unfold pullTensor
  rw [← hs]
  change (((integralOperationsPullbackTransition l E g n).app P).f i).val.app U
    (s • (show (((integralOperationsPullbackLevel l E g (n + 1)).obj P).X i).val.obj U
      from integralOperationsPullbackGenerator l E g (n + 1) _ V
        (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) (op V) x p))) = _
  rw [map_smul]
  with_unfolding_all rw [hgen]
  change _ • _ = _ • _
  rw [← hs] at hproj
  with_unfolding_all rw [hproj]
  rfl

/-- Every composite finite pullback transition reduces both finite coefficients.
Source: Stacks 03D2, 03EK, 03EL; the transition construction of the integral operations.
(blueprint: lem-weil-finite-pullback-transition-generators).

Proof: For an adjacent transition its unit equation is the defining equation of
integralOperationsPullbackTransition. Apply the finite reduction transition formula
to the inner pure tensor. For the outer coefficient, lift it locally through the
surjective completed coefficient projection and use completed linearity. The limit
projection identity replaces that lift's high residue by its low residue. Equality
of sheaf sections is local, so this gives the adjacent formula without choosing
any global lift. For equal indices use the functor identity. Induct on b-a for a
composite transition: the tower functor composes its maps, and both coefficient
systems compose their quotient reductions. Apply the adjacent formula followed
by the induction hypothesis. This proves the formula for every cochain degree
and every input complex, with no boundedness or flatness restriction. -/
theorem pullTensor_transition {X Y : Scheme.{t}} (g : X ⟶ Y)
    (a b : ℕ) (h : a ≤ b) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (V : Y.ProEt)
    (x : (integralCoefficientCommRingSheaf l E Y b).obj.obj (op V))
    (y : (integralCoefficientCommRingSheaf l E X b).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)) :
    ((transition l E g a b h P).f i).val.app _
        (pullTensor l E g b P i V x y p) =
      pullTensor l E g a P i V
        (((integralCoefficientSheafSystem l E Y).map (homOfLE h).op).hom.app (op V) x)
        (((integralCoefficientSheafSystem l E X).map (homOfLE h).op).hom.app _ y) p := by
  induction b, h using Nat.le_induction with
  | base =>
    simp only [transition, homOfLE_refl, op_id]
    with_unfolding_all rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
    rfl
  | succ b h ih =>
    have hp : (homOfLE (Nat.le_trans h (Nat.le_succ b))).op =
        (homOfLE (Nat.le_succ b)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    have hc := congrArg (fun k ↦ k.hom.app _ y)
      ((integralCoefficientSheafSystem l E X).map_comp
        (homOfLE (Nat.le_succ b)).op (homOfLE h).op)
    have hc' := congrArg (fun k ↦ k.hom.app (op V) x)
      ((integralCoefficientSheafSystem l E Y).map_comp
        (homOfLE (Nat.le_succ b)).op (homOfLE h).op)
    unfold transition
    rw [hp, Functor.map_comp]
    simp only [integralOperationsPullbackTowerFunctor, Functor.flip_obj_map,
      Functor.ofOpSequence_map_homOfLE_succ]
    change ((transition l E g a b h P).f i).val.app _
      ((((integralOperationsPullbackTransition l E g b).app P).f i).val.app _
        (pullTensor l E g (b + 1) P i V x y p)) = _
    rw [adjacent, ih]
    congr 1
    · simp only [← hp, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ, ObjectProperty.FullSubcategory.comp_hom,
        NatTrans.comp_app, RingCat.comp_apply] at hc'
      exact hc'.symm
    · simp only [← hp, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ, ObjectProperty.FullSubcategory.comp_hom,
        NatTrans.comp_app, RingCat.comp_apply] at hc
      exact hc.symm

end WeilConjectures.RamifiedPullback
