/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedStageData
public import WeilConjectures.SixFunctors.AdicFiniteRealization.LocallyFiniteAdicFiniteCondensedRealization
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSystem
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedRawIntegralFormula
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedCoefficientSquare

/-! # The constructed finite condensed integral tensor model

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: def-sf-finite-condensed-integral-tensor-model)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization
attribute [local irreducible] finiteCondensedClosureFunctor finiteFunctor
  pbcDerivedRestrict CoefficientPresentation.integralMap sections
  reductionDerivedChange integralDetailedTransport sfRationalConstructibleLocalization
  AlgebraicGeometry.Scheme.rationalCoefficientSheaf
  AlgebraicGeometry.Scheme.integralCoefficientSheaf pbcIntegralDatum
  completedIntegralCommRingSheafUnrestricted sfIntegralConstructible purCoefficientIso
set_option cleanup.letToHave false

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

variable [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The raw integral formula, transported through section reconstruction and the
continuous realization, with the two scalar extensions still separate.
Source: BS 6.8.2 and 6.8.14(2); raw identity and section encoding counit.
(blueprint: def-sf-finite-condensed-integral-tensor-model). -/
@[irreducible] def finiteCondensedIntegralRawModel (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l)) :=
  let Q := sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X
  let r := (A.realization E).integralIso.hom ≫ (A.realization E).inclusion
  let a := Functor.isoWhiskerLeft Q (finiteCondensedClosureSectionComparison l X A E)
  let b := Functor.isoWhiskerRight (eqToIso (finiteRawIntegralFormula l X A E))
    (pbcDerivedExtend (A.closure.leg E))
  let d := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (A.stage E).integral.functor
      (continuousIntegralComparison l X A E)) (pbcDerivedExtend (A.closure.leg E))
  let g := Functor.isoWhiskerRight (eqToIso (A.stage E).integral_identity)
    (pbcDerivedExtend r ⋙ pbcDerivedExtend (A.closure.leg E))
  a ≪≫ b ≪≫ d ≪≫ g

/-- The explicit finite realization has its ordinary integral tensor model.
Source: BS 6.8.2 and 6.8.14(2): compose the integral raw comparison, continuous
realization formula, section reconstruction and the normalized coefficient square.
(blueprint: def-sf-finite-condensed-integral-tensor-model). -/
@[irreducible] def finiteCondensedIntegralTensorModel (A : FiniteCondensedData l X)
    (C : CoefficientSystem l X) (E : Index l (PadicAlgCl l)) :
    letI := C.commutative
    let R := pbcDerivedRestrict
      (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))
    let S := integralSections l X
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        finiteCondensedClosureFunctor l X A E ⋙ S ≅
      (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
        pbcDerivedExtend ((C.coefficient E).integralMap l X) ⋙ R := by
  letI := C.commutative
  let I := (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
  let r := (A.realization E).integralIso.hom ≫ (A.realization E).inclusion
  let s := r ≫ A.closure.leg E
  let t := ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X)
  letI := sectionRingMap_isIso X (condensedNativeMap l X)
  let m := tensorThroughCoefficientSquare X (purCoefficientIso l
      (Coefficient.{u} l (PadicAlgCl l) E) X) (asIso t) s
    ((C.coefficient E).integralMap l X)
    (by
      dsimp only [asIso_hom]
      dsimp only [s, r]
      simp only [Category.assoc]
      exact finiteCondensedIntegralCoefficientSquare l X A E (C.coefficient E))
  let c : pbcDerivedExtend r ⋙ pbcDerivedExtend (A.closure.leg E) ≅
      pbcDerivedExtend s :=
    Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction r)
      (pbcDerivedScalarAdjunction (A.closure.leg E)) (pbcDerivedScalarAdjunction s)
      (pbcDerivedRestrictComp r (A.closure.leg E) s rfl)
  let f := Functor.isoWhiskerLeft (I ⋙ integralDetailedTransport X l
    (Coefficient.{u} l (PadicAlgCl l) E)) c
  let j := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft I (eqToIso (integralDetailedTransport_eq l X
      (Coefficient.{u} l (PadicAlgCl l) E)))) (pbcDerivedExtend s)
  let k := Functor.isoWhiskerLeft I m.symm
  have raw := finiteCondensedIntegralRawModel l X A E
  exact raw ≪≫ f ≪≫ j ≪≫ k

end WeilConjectures.LocallyFiniteAdicRealization
