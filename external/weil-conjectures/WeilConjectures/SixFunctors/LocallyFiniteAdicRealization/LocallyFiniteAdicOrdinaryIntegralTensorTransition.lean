/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSystem
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedRawIntegralFormula
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedCoefficientSquare
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicOrdinaryRawIntegralTransition
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicOrdinaryCoefficientIntegralTransition

/-! # Integral normalization of the ordinary finite closure comparison

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-finite-ordinary-integral-tensor-transition)
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

/-- The ordinary part of the constructed integral model, before section reconstruction.
The composite consists only of raw integral transport, continuous realization and
coefficient tensor comparisons; it contains no condensed closure transition.
Source: BS 6.8.2 and 6.8.14(2).
(blueprint: lem-sf-finite-ordinary-integral-tensor-transition). -/
@[irreducible] def finiteOrdinaryIntegralTensorModel (A : FiniteCondensedData l X)
    (C : CoefficientSystem l X) (E : Index l (PadicAlgCl l)) :
    letI := C.commutative
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        finiteFunctor l X A.toCore E ⋙ pbcDerivedExtend (A.closure.leg E) ≅
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
  let b := Functor.isoWhiskerRight (eqToIso (finiteRawIntegralFormula l X A E))
    (pbcDerivedExtend (A.closure.leg E))
  let d := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (A.stage E).integral.functor
      (continuousIntegralComparison l X A E)) (pbcDerivedExtend (A.closure.leg E))
  let g := Functor.isoWhiskerRight (eqToIso (A.stage E).integral_identity)
    (pbcDerivedExtend r ⋙ pbcDerivedExtend (A.closure.leg E))
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
  exact b ≪≫ d ≪≫ g ≪≫ f ≪≫ j ≪≫ k

attribute [local semireducible] sfRationalConstructibleLocalization

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  sfRationalConstructibleLocalization
  closureRing pbcFiniteField pbcFiniteFieldField pbcFiniteFieldAlgebra ringSheaf
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory
  ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall

private theorem natIso_objs_congr
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (_e : F ≅ G) {X Y : A} (h : X = Y) :
    F.obj X = F.obj Y ∧ G.obj X = G.obj Y :=
  ⟨congrArg F.obj h, congrArg G.obj h⟩

private theorem natIso_app_heq
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (e : F ≅ G) {X Y : A} (h : X = Y) : HEq (e.app X) (e.app Y) := by
  cases h
  rfl

private theorem integralTensorSquare_paste_hetero
    {D : Type*} [Category D] {X Y U V V' M N N' : D}
    (f : X ⟶ Y) (g : U ⟶ V') (a : X ≅ U) (b : Y ≅ V)
    (p : U ≅ M) (q : V ≅ N) (q' : V' ≅ N')
    (t : M ⟶ N') (hV : V = V') (hN : N = N') (hq : HEq q q')
    (ha : integralTensorSquare f a b g)
    (hp : integralTensorSquare g p q' t) :
    integralTensorSquare f (a ≪≫ p) (b ≪≫ q) t := by
  subst V'
  subst N'
  have hq' := eq_of_heq hq
  subst q'
  apply heq_of_eq
  have ha' := eq_of_heq ha
  have hp' := eq_of_heq hp
  change f ≫ (b.hom ≫ q.hom) = (a.hom ≫ p.hom) ≫ t
  rw [← Category.assoc, ha', Category.assoc, hp', Category.assoc]

private theorem integralTensorSquare_paste_hetero_named
    {D : Type*} [Category D] {X Y U V V' M N N' : D}
    (f : X ⟶ Y) (g : U ⟶ V') (a : X ≅ U) (b : Y ≅ V)
    (p : U ≅ M) (q : V ≅ N) (q' : V' ≅ N')
    (c : X ≅ M) (d : Y ≅ N) (hc : c = a ≪≫ p) (hd : d = b ≪≫ q)
    (t : M ⟶ N') (hV : V = V') (hN : N = N') (hq : HEq q q')
    (ha : integralTensorSquare f a b g)
    (hp : integralTensorSquare g p q' t) : integralTensorSquare f c d t := by
  subst c
  subst d
  exact integralTensorSquare_paste_hetero f g a b p q q' t hV hN hq ha hp

private theorem iso_factor_six
    {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₃ ≅ X₄) (e : X₄ ≅ X₅) (f : X₅ ≅ X₆) :
    a ≪≫ b ≪≫ c ≪≫ d ≪≫ e ≪≫ f = (a ≪≫ b ≪≫ c) ≪≫ (d ≪≫ e ≪≫ f) := by
  simp only [Iso.trans_assoc]

private theorem finiteOrdinaryIntegralTensorModel_factor
    (A : FiniteCondensedData l X) (C : CoefficientSystem l X)
    (E : Index l (PadicAlgCl l)) :
    finiteOrdinaryIntegralTensorModel l X A C E =
      finiteOrdinaryRawIntegralModel l X A E ≪≫
        finiteOrdinaryCoefficientIntegralModel l X A C E := by
  unfold finiteOrdinaryIntegralTensorModel finiteOrdinaryRawIntegralModel
    finiteOrdinaryCoefficientIntegralModel
  -- Keep the component constructions in local definitions while reassociating the composite.
  extract_lets
  simp only [Iso.trans_assoc]
  rfl

/-- The ordinary finite closure comparison has the prescribed integral tensor map.

Source: BS 6.8.14(2), the raw and continuous integral scalar normalizations.
(blueprint: lem-sf-finite-ordinary-integral-tensor-transition).

Proof in words: expand closureComparison and scalarComparison, and substitute the
raw scalar_lift equation on K. Substitute the continuous integral normalization
on the integral identity image of K. The pbcScalarIntegralComparison factors in
these two equations cancel. The restriction and chi equations of the raw integral
comparison identify its remaining factor with the prescribed completed scalar
comparison transported through the coefficient isomorphisms. The integral identity
and the literal raw object equation give the required target-object transport.
Finally paste the coefficient squares: their scalar-composition comparisons are
mates of the same restriction square. Associativity of left-adjoint composition
identifies their two composites. Naturality moves the completed comparison through
this tensor square, leaving inverse native balancing followed by extension of
completedTensorComparison. This argument does not use condensed section scalar
comparisons or their coherence. All maps are fixed on K-flat representatives by
their counits; equality descends to K by the derived universal property. Repeated
fields use multiplication by one and the completion unit, and zero objects have
the same equations.
-/
theorem finiteOrdinaryIntegralTensorModel_transition
    (A : FiniteCondensedData l X) (C : CoefficientSystem l X) :
    letI := C.commutative
    let R := pbcDerivedRestrict
      (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))
    let q := finiteOrdinaryIntegralTensorModel l X A C
    ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      let B :=
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj
      let T := (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
        E L h).obj K
      let f :
          (finiteFunctor l X A.toCore E ⋙ pbcDerivedExtend (A.closure.leg E)).obj
            ((sfRationalConstructibleLocalization l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) ⟶
          (finiteFunctor l X A.toCore L ⋙ pbcDerivedExtend (A.closure.leg L)).obj
            ((sfRationalConstructibleLocalization l
              (Coefficient.{u} l (PadicAlgCl l) L) X).obj B) :=
        (closureComparison l X A.toCore A.scalar A.closure h).inv.app
        ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)
      let t :
          (pbcDerivedExtend ((C.coefficient E).integralMap l X)).obj
            ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K) ⟶
            (pbcDerivedExtend ((C.coefficient L).integralMap l X)).obj
            ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) L) X).ι.obj T) :=
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
      integralTensorSquare f ((q E).app K) ((q L).app B) (R.map t) := by
  letI := C.commutative
  intro R q E L h K B T f t
  have hB : B = T := finiteCondensedStageIntegralObject l X E L h K
  obtain ⟨hV, hN⟩ :=
    natIso_objs_congr (finiteOrdinaryCoefficientIntegralModel l X A C L) hB
  have hq : HEq ((finiteOrdinaryCoefficientIntegralModel l X A C L).app B)
      ((finiteOrdinaryCoefficientIntegralModel l X A C L).app T) :=
    natIso_app_heq (finiteOrdinaryCoefficientIntegralModel l X A C L) hB
  exact integralTensorSquare_paste_hetero_named f
    (finiteOrdinaryRawIntegralTransition l X A h K)
    ((finiteOrdinaryRawIntegralModel l X A E).app K)
    ((finiteOrdinaryRawIntegralModel l X A L).app B)
    ((finiteOrdinaryCoefficientIntegralModel l X A C E).app K)
    ((finiteOrdinaryCoefficientIntegralModel l X A C L).app B)
    ((finiteOrdinaryCoefficientIntegralModel l X A C L).app T)
    ((q E).app K) ((q L).app B)
    ((congrArg (fun e ↦ e.app K) (finiteOrdinaryIntegralTensorModel_factor l X A C E)).trans
      (NatIso.trans_app _ _ K))
    ((congrArg (fun e ↦ e.app B) (finiteOrdinaryIntegralTensorModel_factor l X A C L)).trans
      (NatIso.trans_app _ _ B))
    (R.map t) hV hN hq
    (finiteOrdinaryRawIntegralModel_transition l X A E L h K)
    (finiteOrdinaryCoefficientIntegralModel_transition l X A C E L h K)

end WeilConjectures.LocallyFiniteAdicRealization
