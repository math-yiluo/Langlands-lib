/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorIntegralConstruction

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients

attribute [local irreducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf
attribute [local irreducible] coefficientTensorGenerator coefficientTotalTensor
  pullbackTensorSequenceCochain

attribute [local irreducible] Functor.leftAdjoint
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

private def G {X Y : Scheme.{u}} (f : X ⟶ Y) (r : coefficientSequenceCommRingSheaf l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X)) :=
    SheafOfModules.pushforward.{u + 1} (F := integralComparisonSequenceBaseChange f)
      (J := coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (K := coefficientSequenceTopology (Scheme.ProEt.topology X))
      (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E Y))
      (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E X))
      ⟨Functor.whiskerRight r.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private def H {X Y : Scheme.{u}} (f : X ⟶ Y) (r) (hG : (G l E f r).IsRightAdjoint) :=
    letI := hG
    let F := (G l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)
    fun e : ScalarExtensionTower.tensor l E Y ⋙ F ≅
        F.prod F ⋙ ScalarExtensionTower.tensor l E X ↦
      ∀ (A B : StrictQuotient.Complex l E Y) (p q k : ℤ) (h : p + q = k)
        (V : ℕ × Y.ProEt) (x : (A.X p).val.obj (op V))
        (y : (B.X q).val.obj (op V)),
        ((e.hom.app (A,B)).f k).val.app
          (op ((pullbackTensorSequenceBase f).obj V))
          (((Adjunction.ofIsRightAdjoint (G l E f r)).unit.app
            (((ScalarExtensionTower.tensor l E Y).obj (A,B)).X k)).val.app (op V)
            (coefficientTensorGenerator.{u, u + 1, u}
              (coefficientSequenceTopology (Scheme.ProEt.topology Y))
              (coefficientSequenceCommRingSheaf l E Y) A B p q k h (op V) x y)) =
        coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X) (F.obj A) (F.obj B)
          p q k h (op ((pullbackTensorSequenceBase f).obj V))
          (((Adjunction.ofIsRightAdjoint (G l E f r)).unit.app (A.X p)).val.app (op V) x)
          (((Adjunction.ofIsRightAdjoint (G l E f r)).unit.app (B.X q)).val.app (op V) y)

private theorem transport_norm {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r r') (hr : (G l E f r).IsRightAdjoint)
      (hr' : (G l E f r').IsRightAdjoint) (e : r = r')
      (eF : @Functor.leftAdjoint _ _ _ _ (G l E f r) hr =
        @Functor.leftAdjoint _ _ _ _ (G l E f r') hr')
      (a : letI := hr
        ScalarExtensionTower.tensor l E Y ⋙
          (G l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ) ≅
        ((G l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)).prod
          ((G l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)) ⋙
            ScalarExtensionTower.tensor l E X) :
      H l E f r hr a → H l E f r' hr'
        (Functor.isoWhiskerLeft (ScalarExtensionTower.tensor l E Y)
            (NatIso.mapHomologicalComplex (eqToIso eF) (.up ℤ)).symm ≪≫ a ≪≫
          Functor.isoWhiskerRight
            (NatIso.prod (NatIso.mapHomologicalComplex (eqToIso eF) (.up ℤ))
              (NatIso.mapHomologicalComplex (eqToIso eF) (.up ℤ)))
            (ScalarExtensionTower.tensor l E X)) := by
    subst r'
    have hi : NatIso.mapHomologicalComplex (eqToIso eF) (.up ℤ) = Iso.refl _ := by
      apply Iso.ext
      apply NatTrans.ext
      funext A
      apply HomologicalComplex.hom_ext
      intro i
      simp
    rw [hi]
    have hp : NatIso.prod
        (Iso.refl ((G l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)))
        (Iso.refl ((G l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ))) = Iso.refl _ := by
      apply Iso.ext
      rfl
    rw [hp]
    simp

private theorem unique_norm {X Y : Scheme.{u}} (f : X ⟶ Y) (r) (hr : (G l E f r).IsRightAdjoint)
      (a b : letI := hr
        ScalarExtensionTower.tensor l E Y ⋙
          (G l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ) ≅
        ((G l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)).prod
          ((G l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)) ⋙
            ScalarExtensionTower.tensor l E X)
      (ha : H l E f r hr a) (hb : H l E f r hr b) : a = b := by
    let := hr
    apply Iso.ext
    apply NatTrans.ext
    funext V
    rcases V with ⟨A, B⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ((Adjunction.ofIsRightAdjoint (G l E f r)).homEquiv _ _).injective
    apply WeilConjectures.total_tensor_sections_ext l E Y A B n
    intro p q hpq V x y
    subst n
    exact (ha A B p q (p + q) rfl V.unop x y).trans
      (hb A B p q (p + q) rfl V.unop x y).symm

private theorem conjugate_app
    {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) (F G : C ⥤ D) (b : F ≅ G)
    (a : T ⋙ F ≅ F.prod F ⋙ U) (P Q : C) :
    (Functor.isoWhiskerLeft T b.symm ≪≫ a ≪≫
      Functor.isoWhiskerRight (NatIso.prod b b) U).app (P, Q) =
    (b.app (T.obj (P, Q))).symm ≪≫ a.app (P, Q) ≪≫
      U.mapIso (Iso.prod (b.app P) (b.app Q)) := by
  apply Iso.ext
  rfl

-- Normalize the two cochain interfaces on all total-tensor generators.
private theorem comparison_test {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : StrictQuotient.Complex l E Y) :
    comparison l E f P Q = ((ScalarExtensionTower.comparisons l).c E f).app (P, Q) := by
  have hr := WeilConjectures.pullbackTensorSequenceRing_eq l E f
  have hn := transport_norm l E f (pullbackTensorSequenceRing l E f)
    (integralComparisonSequenceRingMap l E f)
    (pullbackTensorSequenceDirect_rightAdjoint l E f)
    (integralComparisonSequenceDirectImage_isRightAdjoint l E f)
    hr
    (sequencePullback_eq l E f) (pullbackTensorSequenceCochain l E f)
    (by
      unfold pullbackTensorSequenceCochain
      exact (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose_spec)
  have hc : H l E f (integralComparisonSequenceRingMap l E f)
      (integralComparisonSequenceDirectImage_isRightAdjoint l E f)
      ((ScalarExtensionTower.comparisons l).c E f) := by
    intro A B p q k hpq V x y
    subst k
    rcases V with ⟨m, U⟩
    dsimp only [H, G, ScalarExtensionTower.tensor,
      pullbackTensorSequenceBase, integralComparisonSequenceBaseChange]
    with_unfolding_all
      convert ScalarExtensionTower.pull_tensor_section l E f A B p q m U x y using 1 <;>
        simp only [ScalarExtensionTower.pullSection,
      ScalarExtensionTower.generator, integralComparisonSequenceGenerator,
      ScalarExtensionTower.pull, ScalarExtensionTower.tensor, Functor.prod_obj, Functor.id_obj,
      integralComparisonSequencePullback, integralComparisonSequenceDirectImage]
    all_goals rfl
  have he := unique_norm l E f _ _ _ _ hn hc
  have he' := congrArg (fun e ↦ e.app (P, Q)) he
  have ha := conjugate_app (ScalarExtensionTower.tensor l E Y)
    (ScalarExtensionTower.tensor l E X)
    ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ))
    ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ))
    (NatIso.mapHomologicalComplex (eqToIso (sequencePullback_eq l E f)) (.up ℤ))
    (pullbackTensorSequenceCochain l E f) P Q
  have hb := ha.symm.trans he'
  unfold comparison pullBridge
  exact hb

/-- The strict scalar square for the transported quotient comparison.
Source: Stacks 03EL, 07A4, 0941; scalar route coordinate proof step 1.
(blueprint: lem-pur-completed-scalar-strict-square).

Proof: identify each transported comparison with the generator-normalized comparison
of ScalarExtensionTower. Equality of the two ring maps identifies the direct images
and their chosen adjunctions. Transport preserves the tensor-generator formula;
adjunction transposition and total-tensor generator extensionality give uniqueness.
The existing strict scalar square then applies, and evaluation at the two complexes
gives the claimed equality of isomorphisms of whole coefficient systems. -/
theorem completedScalarStrictSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : StrictQuotient.Complex l E Y) :
    scalarLeft l E L ι f P Q = scalarRight l E L ι f P Q := by
  unfold scalarLeft scalarRight
  rw [comparison_test l L, comparison_test l E]
  exact congrArg (fun e ↦ e.app (P, Q)) (ScalarExtensionTower.square l E L ι f)

end WeilConjectures.CompletedQuotient
