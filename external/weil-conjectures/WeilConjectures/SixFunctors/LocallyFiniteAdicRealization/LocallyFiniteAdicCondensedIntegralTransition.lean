/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedTensorNormalization
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedClosureSectionTransition
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicOrdinaryIntegralTensorTransition

/-! # Integral tensor transition for the finite condensed realization

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-finite-condensed-integral-tensor-transition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization

-- Expose category aliases only to implicit matching in the comparison calculations.
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  closureRing finiteCondensedClosureFunctor ProEtale.constructibleToPadicAlgCl
  pbcFiniteField pbcFiniteFieldField pbcFiniteFieldAlgebra
  sfRationalConstructibleLocalization
  ringSheaf ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory
  ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall

private theorem integralTensorSquare_paste
    {D : Type*} [Category D] {X Y U V M N N' : D}
    (f : X ⟶ Y) (g : U ⟶ V) (a : X ≅ U) (b : Y ≅ V)
    (p : U ≅ M) (q : V ≅ N) (t : M ⟶ N') (hN : N = N')
    (hf : f ≫ b.hom = a.hom ≫ g)
    (hg : integralTensorSquare g p q t) :
    integralTensorSquare f (a ≪≫ p) (b ≪≫ q) t := by
  subst N'
  apply heq_of_eq
  have hg' := eq_of_heq hg
  change f ≫ (b.hom ≫ q.hom) = (a.hom ≫ p.hom) ≫ t
  rw [← Category.assoc, hf, Category.assoc, hg', Category.assoc]

private theorem iso_factor_seven
    {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : D}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (d : X₃ ≅ X₄)
    (e : X₄ ≅ X₅) (f : X₅ ≅ X₆) (g : X₆ ≅ X₇) :
    (a ≪≫ b ≪≫ c ≪≫ d) ≪≫ e ≪≫ f ≪≫ g =
      a ≪≫ b ≪≫ c ≪≫ d ≪≫ e ≪≫ f ≪≫ g := by
  simp only [Iso.trans_assoc]

private theorem integralTensorSquare_paste_named
    {D : Type*} [Category D] {X Y U V M N N' : D}
    (f : X ⟶ Y) (g : U ⟶ V) (a : X ≅ U) (b : Y ≅ V)
    (p : U ≅ M) (q : V ≅ N) (p' : X ≅ M) (q' : Y ≅ N)
    (hp : p' = a ≪≫ p) (hq : q' = b ≪≫ q) (t : M ⟶ N') (hN : N = N')
    (hf : f ≫ b.hom = a.hom ≫ g)
    (hg : integralTensorSquare g p q t) : integralTensorSquare f p' q' t := by
  subst p'
  subst q'
  exact integralTensorSquare_paste f g a b p q t hN hf hg

private theorem integralTensorModel_factor
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (A : FiniteCondensedData l X) (C : CoefficientSystem l X)
    (E : Index l (PadicAlgCl l)) :
    finiteCondensedIntegralTensorModel l X A C E =
      Functor.isoWhiskerLeft
        (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X)
        (finiteCondensedClosureSectionComparison l X A E) ≪≫
      finiteOrdinaryIntegralTensorModel l X A C E := by
  dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory]
  unfold finiteCondensedIntegralTensorModel finiteCondensedIntegralRawModel
    finiteOrdinaryIntegralTensorModel
  exact iso_factor_seven _ _ _ _ _ _ _

/-- The fixed integral tensor models commute with one finite-field inclusion.
This is a tensor-coherence equation without a native common-stage functor.

Source: BS 6.8.14(2) and Remark 6.8.15.
(blueprint: lem-sf-finite-condensed-integral-tensor-transition).

Proof in words: unfold the constructed tensor models and the closure transition.
Cancel the section reconstruction counits and use the unit equation defining the
section scalar comparison. Substitute A.raw.scalar_lift for the raw scalar comparison
on integral objects and A.scalar.integral for the continuous scalar comparison.
The completion comparison then remains as the specified completedTensorComparison.
The coefficient squares identify the scalar maps. The two composites of adjunction
mates both flatten b tensor (a tensor k) to ba tensor k on K-flat representatives.
Tensor associativity and the derived universal property equate these composites.
For an identity inclusion the same equation uses the completion unitor; for the zero
complex and empty scheme all component equations retain their unique zero maps.
-/
theorem finiteCondensedIntegralTensorTransition
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (A : FiniteCondensedData l X) (C : CoefficientSystem l X) :
    letI := C.commutative
    let R := pbcDerivedRestrict
      (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))
    let S := integralSections l X
    let q := finiteCondensedIntegralTensorModel l X A C
    ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      let B :=
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj
      let T := (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
        E L h).obj K
      let f :
          (finiteCondensedClosureFunctor l X A E).obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) ⟶
            (finiteCondensedClosureFunctor l X A L).obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) L) X).obj B) :=
        (finiteCondensedClosureTransition l X A h).hom.app
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
      integralTensorSquare (S.map f) ((q E).app K) ((q L).app B) (R.map t) := by
  letI := C.commutative
  intro R S q E L h K
  let B :=
    (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj
  let T := (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
    E L h).obj K
  have hB : B = T := finiteCondensedStageIntegralObject l X E L h K
  exact integralTensorSquare_paste_named _ _
    ((finiteCondensedClosureSectionComparison l X A E).app
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))
    ((finiteCondensedClosureSectionComparison l X A L).app
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) L) X).obj B))
    ((finiteOrdinaryIntegralTensorModel l X A C E).app K)
    ((finiteOrdinaryIntegralTensorModel l X A C L).app B) _ _
    (congrArg (fun e ↦ e.app K) (integralTensorModel_factor l X A C E))
    (congrArg (fun e ↦ e.app B) (integralTensorModel_factor l X A C L)) _
    (congrArg (fun (Z : sfIntegralConstructibleCategory l
      (Coefficient.{u} l (PadicAlgCl l) L) X) ↦ (pbcDerivedRestrict
      (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))).obj
        ((pbcDerivedExtend ((C.coefficient L).integralMap l X)).obj Z.obj)) hB)
    (finiteCondensedClosureSectionComparison_transition l X A h
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))
    (finiteOrdinaryIntegralTensorModel_transition l X A C E L h K)

end WeilConjectures.LocallyFiniteAdicRealization
