/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSystem
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicOrdinaryRawIntegralTransition
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedCoefficientSquare

/-! # Integral normalization of the ordinary finite closure comparison

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-finite-ordinary-coefficient-integral-transition)
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

/-- Integral coefficient transport after the continuous realization, with the
ordinary coefficient extensions still separate on its source.
Source: BS 6.8.2 and 6.8.14(2), the prescribed integral coefficient square.
(blueprint: lem-sf-finite-ordinary-coefficient-integral-transition). -/
@[irreducible] def finiteOrdinaryCoefficientIntegralModel (A : FiniteCondensedData l X)
    (C : CoefficientSystem l X) (E : Index l (PadicAlgCl l)) :
    letI := C.commutative
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
        integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E) ⋙
          pbcDerivedExtend ((A.realization E).integralIso.hom ≫
            (A.realization E).inclusion) ⋙ pbcDerivedExtend (A.closure.leg E) ≅
      (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
        pbcDerivedExtend ((C.coefficient E).integralMap l X) ⋙
          pbcDerivedRestrict
            (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X)) := by
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
  exact f ≪≫ j ≪≫ k

/-- The completion comparison is preserved by the prescribed coefficient tensor
transport, independently of raw-stage rationalization or section reconstruction.
Source: BS 6.8.2, 6.8.14(2), and the quotient-normalized completion comparison.
(blueprint: lem-sf-finite-ordinary-coefficient-integral-transition).

Proof in words: retain the specified ambient completed comparison of A.raw.integral.
Package the given raw stage and scalar data as the finite coefficient comparison.
Apply the normalized common-stage descent theorem, retaining its scalar comparison. The fixed
coefficient scalar completion identification gives inverse ordinary coefficient
transport followed by detailed transport of scalarCompletionIso. Compare the
ordinary scalar and completion models on all universal cochain counits; their
normalized comparison sends the latter map to completedTensorComparison. The
integral coefficient square identifies each source coefficient ring isomorphism
with purCoefficientIso, and the native balancing square identifies its target.
Both ways of transporting the ordinary scalar comparison are mates of the same
restriction square. The restriction compositors have their sectionwise identity
cocycle, so left-adjoint composition associativity identifies these tensor maps.
Naturality then moves the completed comparison through the native balancing
isomorphism. The result is native restriction of inverse reduction normalization
followed by native extension of completedTensorComparison. The normalization
uses all cochain counits, so it holds for every derived representative and is
independent of choices. Equal fields, ramified extensions and zero objects obey
the same comparison equation; no finite quotient scalar map is inverted.
-/
theorem finiteOrdinaryCoefficientIntegralModel_transition
    (A : FiniteCondensedData l X) (C : CoefficientSystem l X) :
    letI := C.commutative
    let R := pbcDerivedRestrict
      (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))
    ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      let T := (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
        E L h).obj K
      let t :=
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((C.coefficient L).integralMap l X) ((C.coefficient E).integralMap l X)
          (C.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((C.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h)).app
              K.obj)
      integralTensorSquare (finiteOrdinaryRawIntegralTransition l X A h K)
        ((finiteOrdinaryCoefficientIntegralModel l X A C E).app K)
        ((finiteOrdinaryCoefficientIntegralModel l X A C L).app T) (R.map t) := by sorry

end WeilConjectures.LocallyFiniteAdicRealization
