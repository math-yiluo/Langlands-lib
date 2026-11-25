/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismStrictQuotientModels
import all WeilConjectures.TraceFormula.QuotientTensor.QuotientTensorInsertion

/-! # Multiplication on the strict quotient tower

Source: Stacks 03CZ, 03EK, 06YY, 08TC and 0941; the strict quotient-cone argument
of `lem-trf-isomorphism-multiplication-cone-descent`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local instance 3000] integralTowerHasDerivedCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralOperationsGoodComplex coefficientSequenceLimit TrfCompletionRoosNormalized
  integralDerivedPullback integralDerivedPullbackComparison integralPullbackDescent
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategory DerivedCategory.Q
  integralOperationsRoosMap

private theorem insertion_transition
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    (trfInverseImageComplex l E g).map ((unrestrictedIntegralTransition l E Y n).app Q) ≫
        QuotientTensor.insertion l E g n
          ((unrestrictedIntegralFiniteComplex l E Y n).obj Q) =
      QuotientTensor.insertion l E g (n + 1)
          ((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj Q) ≫
        (integralOperationsPullbackTransition l E g n).app Q := by
  ext i U x
  obtain ⟨U⟩ := U
  change ((QuotientTensor.insertion l E g n
      ((unrestrictedIntegralFiniteComplex l E Y n).obj Q)).f i).val.app (op U)
        ((((unrestrictedIntegralTransition l E Y n).app Q).f i).val.app
          (op ((proEtaleIsoPostcompose g).obj U)) x) =
    (((integralOperationsPullbackTransition l E g n).app Q).f i).val.app (op U)
      (((QuotientTensor.insertion l E g (n + 1)
        ((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj Q)).f i).val.app (op U) x)
  erw [QuotientTensor.insertion_apply, QuotientTensor.insertion_apply]
  simp only [QuotientTensor.tensorSection, one_smul]
  let V := (proEtaleIsoPostcompose g).obj U
  let z := integralOperationsPullbackGenerator l E g (n + 1)
    (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj Q).X i) V x
  have hr := congrArg (fun k ↦ k z)
    ((((integralOperationsPullbackTransition l E g n).app Q).f i).val.naturality
      (proEtaleIsoCommaArrow g U).op)
  have ht := (integralOperationsPullbackTransition_existsUnique l E g n).exists.choose_spec
    Q i V x
  calc
    _ = ((((integralOperationsPullbackLevel l E g n).obj Q).X i).val.map
        (proEtaleIsoCommaArrow g U).op)
        ((((integralOperationsPullbackTransition l E g n).app Q).f i).val.app
          (op ((proEtaleBaseChange g).obj V)) z) := by
      exact congrArg
        ((((integralOperationsPullbackLevel l E g n).obj Q).X i).val.map
          (proEtaleIsoCommaArrow g U).op) ht.symm
    _ = _ := hr.symm

private def insertion_tower
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((trfQuotientTowerFunctor l E Y ⋙ trfInverseImageTower l E g).obj Q) ⟶
      (integralOperationsPullbackTowerFunctor l E g).obj Q :=
  NatTrans.ofOpSequence
    (fun n ↦ QuotientTensor.insertion l E g n
      ((unrestrictedIntegralFiniteComplex l E Y n).obj Q)) (fun n ↦ by
        simp only [trfQuotientTowerFunctor, trfInverseImageTower, Functor.comp_obj,
          Functor.whiskeringRight_obj_obj, Functor.comp_map, Functor.flip_obj_map,
          integralOperationsPullbackTowerFunctor,
          Functor.ofOpSequence_map_homOfLE_succ]
        exact insertion_transition l E g Q n)

private def insertion_iso
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    trfQuotientTowerFunctor l E Y ⋙ trfInverseImageTower l E g ≅
      integralOperationsPullbackTowerFunctor l E g := by
  have hi (Q : CochainComplex (integralTowerModules l E Y) ℤ) :
      IsIso (insertion_tower l E g Q) := by
    have (n : ℕᵒᵖ) : IsIso ((insertion_tower l E g Q).app n) :=
      QuotientTensor.insertion_isIso l E g n.unop _
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.ofComponents (fun Q ↦ asIso (insertion_tower l E g Q)) (by
    intro Q R f
    apply NatTrans.ext
    funext n
    exact QuotientTensor.insertion_naturality l E g n.unop
      ((unrestrictedIntegralFiniteComplex l E Y n.unop).map f))

/-- Multiplication identifies the actual finite pullback tower with inverse image of
all strict quotients, naturally in good complexes, with its two unit-generator formulas.
Source: Stacks 03CZ (lemma-adjointness-tensor-restrict), 03EK, and steps 3--4 of
lem-trf-isomorphism-multiplication-cone-descent.
(blueprint: lem-trf-isomorphism-strict-quotient-multiplication).

Proof in words: identify inverse image under the site equivalence with postcomposition.
At level n apply scalar extension along the finite coefficient isomorphism: multiplication
is s tensor x to c_n inverse(s) times x, and its inverse is x to 1 tensor x. Tensor
balancing proves both inverse identities. The completed coefficient projection equation
proves completed linearity after restriction of scalars. These maps descend uniquely
through module sheafification; equality is tested before sheafification on pure tensors.
Naturality of c_n proves commutation with restrictions and differentials. For the actual
transition, reduction sends s tensor x to reduction(s) tensor tau(x); the coefficient
reduction square gives c_n inverse(reduction(s)) tau(x) =
tau(c_(n+1) inverse(s) x). Thus the level isomorphisms assemble into a strict tower
isomorphism. The same tensor calculation for any chain map proves naturality in Q.
The canonical comma arrow identifies the unit generator with its postcomposed section,
so multiplication and its inverse have precisely the two displayed section formulas. -/
theorem isomorphismStrictQuotientMultiplication
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    ∃ (j : (integralOperationsGoodComplex l E Y).ι ⋙
          integralOperationsPullbackTowerFunctor l E g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙
          trfQuotientTowerFunctor l E Y ⋙ trfInverseImageTower l E g),
      (∀ (Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) (i : ℤ)
        (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (((j.hom.app Q).app (op n)).f i).val.app (op U)
            ((((integralOperationsPullbackLevel l E g n).obj Q.obj).X i).val.map
              (proEtaleIsoCommaArrow g U).op
              (integralOperationsPullbackGenerator l E g n
                (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i)
                ((proEtaleIsoPostcompose g).obj U) x)) = x) ∧
      (∀ (Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) (i : ℤ)
        (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (((j.inv.app Q).app (op n)).f i).val.app (op U) x =
          ((((integralOperationsPullbackLevel l E g n).obj Q.obj).X i).val.map
            (proEtaleIsoCommaArrow g U).op
            (integralOperationsPullbackGenerator l E g n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i)
              ((proEtaleIsoPostcompose g).obj U) x))) := by
  let j := Functor.isoWhiskerLeft (integralOperationsGoodComplex l E Y).ι
    (insertion_iso l E g).symm
  refine ⟨j, ?_, ?_⟩
  · intro Q n i U x
    have h := congrArg (fun k ↦ ((k.app (op n)).f i).val.app (op U) x)
      ((insertion_iso l E g).hom_inv_id_app Q.obj)
    change (((j.hom.app Q).app (op n)).f i).val.app (op U)
      (((QuotientTensor.insertion l E g n
        ((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj)).f i).val.app (op U) x)
        = x at h
    rw [QuotientTensor.insertion_apply] at h
    simp only [QuotientTensor.tensorSection, one_smul] at h
    exact h
  · intro Q n i U x
    change ((QuotientTensor.insertion l E g n
      ((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj)).f i).val.app (op U) x = _
    have h := QuotientTensor.insertion_apply l E g n
      ((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj) i U x
    simp only [QuotientTensor.tensorSection, one_smul] at h
    exact h

end WeilConjectures
