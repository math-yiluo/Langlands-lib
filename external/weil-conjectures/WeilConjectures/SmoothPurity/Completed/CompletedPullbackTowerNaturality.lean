/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # Naturality of the strict pullback tower

Source: Stacks Project, Cohomology on Sites, Tag 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

section CoherentSystems

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem pullbackTensorNaturality_of_components
    {C : Type*} [Category* C] {A B A' B' : C} {a : A ⟶ B} {b : A' ⟶ B'}
    {eA eA' : A ≅ A'} {eB eB' : B ≅ B'} (hA : eA = eA') (hB : eB = eB')
    (h : a ≫ eB'.hom = eA'.hom ≫ b) : a ≫ eB.hom = eA.hom ≫ b :=
  (congrArg (fun e : B ≅ B' ↦ a ≫ e.hom) hB).trans
    (h.trans (congrArg (fun e : A ≅ A' ↦ e.hom ≫ b) hA).symm)

attribute [local irreducible] coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingSheafUnrestricted in
/-- The prescribed pullback tower components are natural in the integral complex.
Source: Stacks Project, Cohomology on Sites, Tag 0941
(blueprint: lem-pur-strict-pullback-tower-naturality).
Proof: evaluate the square at n. The prescribed component is the composite of
reordering, sequence pullback evaluation, and the inverse reduction evaluation.
These are natural isomorphisms of cochain functors, so their composite is natural.
Replace each prescribed component with the chosen tower component, using its
normalization, and conclude by extensionality of natural transformations. -/
theorem pullbackTensorPullbackTower_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {P Q : CochainComplex (integralTowerModules l E Y) ℤ} (g : P ⟶ Q) :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map
          (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).map
            (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).map g))) ≫
      (pullbackTensorPullbackTower l E f Q).hom =
    (pullbackTensorPullbackTower l E f P).hom ≫
      (integralOperationsPullbackTowerFunctor l E f).map g := by
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  have hP := (pullbackTensorPullbackTower_existsUnique l E f P).exists.choose_spec n
  have hQ := (pullbackTensorPullbackTower_existsUnique l E f Q).exists.choose_spec n
  change _ ≫ ((pullbackTensorPullbackTower l E f Q).app (op n)).hom =
    ((pullbackTensorPullbackTower l E f P).app (op n)).hom ≫ _
  change (pullbackTensorPullbackTower l E f P).app (op n) = _ at hP
  change (pullbackTensorPullbackTower l E f Q).app (op n) = _ at hQ
  let R := (pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)
  let I := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
  let S := (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)
  let T := (integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)
  let a := Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceRestriction l E X ⋙
      (evaluation ℕᵒᵖ (integralTowerModules l E X)).obj (op n))) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (coefficientSequenceEvaluation l E X n ⋙
        scalarReductionRestriction l E X n)) (.up ℤ)).symm
  let b := Functor.isoWhiskerLeft (R ⋙ I) a
  let c := Functor.isoWhiskerLeft R
    (Functor.isoWhiskerRight (pullbackTensorInverseEvaluationComplex l E f n).symm S)
  let d := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (pullbackTensorReductionEvaluationComplex l E Y n).symm T) S
  have h := (b.hom ≫ c.hom ≫ d.hom).naturality g
  exact pullbackTensorNaturality_of_components hP hQ h

end CoherentSystems
end WeilConjectures
