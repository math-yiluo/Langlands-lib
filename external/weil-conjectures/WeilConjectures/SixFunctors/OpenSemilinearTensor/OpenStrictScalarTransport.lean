/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenFiniteScalarComparison
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenScalarTransitionCompatibility
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemIsoAssembly

/-! # Strict scalar comparison transported from the open slice

Source: Stacks Project, Tags 03DI, 03EK, 0941 and 0E8I.
(blueprint: lem-sf-open-strict-scalar-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

-- Keep the scalar and sequence constructions closed during component comparisons.
attribute [local irreducible] WeilConjectures.scalarReductionExtension
  WeilConjectures.scalarReductionExistence
  WeilConjectures.OpenSemilinearTensor.scalarLevelComparison
  WeilConjectures.IntegralOpenReduction.extensionEvaluation
  CategoryTheory.Functor.leftAdjoint CategoryTheory.constantSheaf
  CategoryTheory.presheafToSheaf CategoryTheory.Functor.ofSequence
  CategoryTheory.Functor.ofOpSequence
  WeilConjectures.SemilinearSections.coefficientMap
  WeilConjectures.SemilinearSections.transition

-- The two interfaces use the same finite rings and the same sequence-site data.
attribute [local implicit_reducible] WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.integralCoefficientSheaf
  CategoryTheory.sheafCompose
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf
  WeilConjectures.SemilinearSections.rings
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.coefficientSequenceCommRingSystem

universe t u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.OpenSemilinearTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j) (AX : OrdinaryReduction l E X) (AU : OrdinaryReduction l E U)

/-- The finite comparison obtained by evaluating one ordinary strict-system
comparison and conjugating by the recorded evaluations. This is a construction,
with no choice of a finite comparison.
Source: Stacks 0941 (blueprint: lem-sf-open-strict-scalar-transport). -/
def ordinaryScalarEvaluationComparison
    (a : IntegralOpenReduction.extension l E j o ⋙ AX.functor ≅
      AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o) (n : ℕ) :
    IntegralOpenReduction.extension l E j o ⋙ scalarReductionExtension l E X n ≅
      scalarReductionExtension l E U n ⋙ IntegralOpenReduction.finiteExtension l E j o n :=
  Functor.isoWhiskerLeft (IntegralOpenReduction.extension l E j o) (AX.evaluation n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight a (coefficientSequenceEvaluation l E X n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft AU.functor (IntegralOpenReduction.extensionEvaluation l E j o n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (AU.evaluation n) (IntegralOpenReduction.finiteExtension l E j o n)

private theorem systemHom_ext {A B : coefficientSequenceModules l E X} {f g : A ⟶ B}
    (h : ∀ n, (coefficientSequenceEvaluation l E X n).map f =
      (coefficientSequenceEvaluation l E X n).map g) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  exact congrArg (fun k ↦ k.val.app (op W.unop.2) x) (h W.unop.1)

/-- There is a strict-system comparison whose evaluated finite maps preserve the
actual scalar units on every extension summand. Only the scalar part is asserted:
the open operations and both quotient-compatible ordinary reductions are inputs.
Source: Stacks 03DI, 03EK, 0941 and 0E8I
(blueprint: lem-sf-open-strict-scalar-transport).

Proof: form the completed projection cone on the actual quotient tower of X and
apply `exists_semilinearSliceScalarGenerators`. Its two scalar tower functors
have the actual quotient tensors at every level, with every horizontal map fixed
on pure tensors. Identify them with AX and the slice transport of AU as follows.
At level n compare the scalar-extension adjunction with the recorded finite
adjunction by the unique unit-preserving left-adjoint comparison; compose with
AX.evaluation n or AU.evaluation n. On unit tensors the two transition composites
both insert the quotient coefficient map. Scalar-extension Hom extensionality
therefore proves the transition squares for all indices, giving isomorphisms of
strict systems, natural in the original module. The same procedure for the
termwise slice extension and o.openSystems.extension uses their adjunctions:
the identity-on-sections restriction evaluation and the recorded unit-evaluation
equation make the level comparison preserve each original extension summand.
Transport the generic strict comparison along these three system isomorphisms
and along o.systems. This gives a single natural isomorphism a before evaluation.
By the generic `component_eq`, evaluation of a, conjugated by AX.evaluation,
extensionEvaluation and AU.evaluation, is its coefficient-linear component.
The generic `generator` with coefficient one is precisely the displayed formula,
since the finite-adjoint comparisons preserve units. The quotient equations in
AX and AU are essential here: they ensure these level identifications are maps
of strict systems rather than unrelated choices at each coefficient. -/
theorem openStrictScalarTransport
    (hrestriction : ∀ (n : ℕ) N V x,
      HEq ((((o.openSystems.restrictionEvaluation n).hom.app N).val.app V) x) x) :
    ∃ a : IntegralOpenReduction.extension l E j o ⋙ AX.functor ≅
        AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o,
      ∀ (n : ℕ) (M : scalarReductionSource l E U) (V : X.ProEt)
        (b : V ⟶ IntegralOpenReduction.openObject j)
        (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk b)))),
        ((ordinaryScalarEvaluationComparison l E j o AX AU a n).hom.app M).val.app (op V)
          (coefficientIntegralScalarUnitSection l E X n
            ((IntegralOpenReduction.extension l E j o).obj M) (op V)
            (IntegralOpenReduction.extensionSection l E j o M V b x)) =
          IntegralOpenReduction.finiteExtensionSection l E j o n
            ((scalarReductionExtension l E U n).obj M) V b
            (coefficientIntegralScalarUnitSection l E U n M
              (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk b))) x) := by
  classical
  obtain ⟨tc, -, -⟩ := existsUnique_openFiniteScalarComparison l E j o
  let e := scalarLevelComparison l E j o AX AU tc
  have hm (M : scalarReductionSource l E U) :
      ∃ a : (IntegralOpenReduction.extension l E j o ⋙ AX.functor).obj M ≅
          (AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o).obj M,
        ∀ n, (coefficientSequenceEvaluation l E X n).map a.hom = (e n).hom.app M := by
    have h := SemilinearSections.systemIsoOfEvaluation_exists.{t + 1, t, max u (t + 1)}
      (ProEt.topology X) (IntegralOpenReduction.rings l E X)
      (IntegralOpenReduction.transitions l E X)
      (M := (IntegralOpenReduction.extension l E j o ⋙ AX.functor).obj M)
      (N := (AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o).obj M)
    refine h (fun n ↦ (e n).app M) ?_
    intro m n hh
    dsimp only [e, Iso.app_hom]
    exact openScalarTransitionCompatibility l E j o AX AU hrestriction tc M
      (m := m) (n := n) hh
  choose a₀ ha₀ using hm
  let a : IntegralOpenReduction.extension l E j o ⋙ AX.functor ≅
      AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o :=
    NatIso.ofComponents a₀ (by
      intro M N f
      apply systemHom_ext l E
      intro n
      simp only [Functor.map_comp, ha₀]
      exact (e n).hom.naturality f)
  refine ⟨a, ?_⟩
  have ha (n : ℕ) (M : scalarReductionSource l E U) :
      (coefficientSequenceEvaluation l E X n).map (a.hom.app M) = (e n).hom.app M :=
    ha₀ M n
  have he (n : ℕ) : ordinaryScalarEvaluationComparison l E j o AX AU a n =
      tc.ordinary n := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    change (AX.evaluation n).inv.app ((IntegralOpenReduction.extension l E j o).obj M) ≫
      (coefficientSequenceEvaluation l E X n).map (a.hom.app M) ≫
      (IntegralOpenReduction.extensionEvaluation l E j o n).hom.app (AU.functor.obj M) ≫
      (IntegralOpenReduction.finiteExtension l E j o n).map
        ((AU.evaluation n).hom.app M) = _
    rw [ha]
    dsimp only [e]
    unfold scalarLevelComparison
    change (AX.evaluation n).inv.app ((IntegralOpenReduction.extension l E j o).obj M) ≫
      ((AX.evaluation n).hom.app ((IntegralOpenReduction.extension l E j o).obj M) ≫
        (tc.ordinary n).hom.app M ≫
        (IntegralOpenReduction.finiteExtension l E j o n).map ((AU.evaluation n).inv.app M) ≫
        (IntegralOpenReduction.extensionEvaluation l E j o n).inv.app (AU.functor.obj M)) ≫
      (IntegralOpenReduction.extensionEvaluation l E j o n).hom.app (AU.functor.obj M) ≫
      (IntegralOpenReduction.finiteExtension l E j o n).map
        ((AU.evaluation n).hom.app M) = _
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app]
    rw [(IntegralOpenReduction.finiteExtension l E j o n).map_id]
    exact Category.comp_id ((tc.ordinary n).hom.app M)
  intro n M V b x
  rw [he]
  exact tc.generators n M V b x

end WeilConjectures.OpenSemilinearTensor
