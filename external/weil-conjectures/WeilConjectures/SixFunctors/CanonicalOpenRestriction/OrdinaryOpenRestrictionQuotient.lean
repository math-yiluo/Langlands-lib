/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.OrdinaryOpenFiniteRestrictionMate
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.OrdinaryOpenRestrictionFiniteComponents
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.OrdinaryOpenTensorSystemAssembly
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-! # Ordinary quotient restriction

Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I; Tag 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.scalarReductionExtension WeilConjectures.scalarReductionExistence
  WeilConjectures.SemilinearSections.transition
  WeilConjectures.SemilinearSections.coefficientMap
  WeilConjectures.OpenSemilinearTensor.scalarLevelComparison
  WeilConjectures.IntegralOpenReduction.extensionEvaluation
attribute [local implicit_reducible] WeilConjectures.coefficientSequenceEvaluation
  WeilConjectures.SemilinearSections.evaluation
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf
  WeilConjectures.SemilinearSections.rings
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.coefficientSequenceCommRingSystem
  WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.integralCoefficientSheaf
  CategoryTheory.sheafCompose
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

private theorem systemHom_ext
    {C : Type (t + 1)} [Category.{t} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max u (t + 1)} C]
    (B : ℕ → Sheaf J CommRingCat.{max u (t + 1)}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {M N : SemilinearSections.Systems.{t + 1, t, max u (t + 1)} J B τ} {f g : M ⟶ N}
    (h : ∀ n, (SemilinearSections.evaluation J B τ n).map f =
      (SemilinearSections.evaluation J B τ n).map g) : f = g := by
  ext V x
  exact congrArg (fun k ↦ k.val.app (op V.unop.2) x) (h V.unop.1)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j)

-- Reconcile the concrete coefficient categories without unfolding chosen scalar functors.
/-- Ordinary strict quotient restriction and its finite adjunction normalization.
Source: Stacks, Modules on Sites, Tags 03DJ and 0E8I; Cohomology on Sites, Tag 0941.
(blueprint: lem-sf-open-restriction-ordinary-quotient).

Proof: the normalized extension tensor comparison has compatible finite components
by openScalarTransitionCompatibility. Assemble them, using the model evaluations,
into a natural isomorphism of strict systems. Take the right mate of its inverse
under the ordinary integral and system open adjunctions. This is already a map of
strict systems, so no separate transition compatibility has to be imposed on it.
The evaluated system counit and naturality identify its finite evaluation with
the right mate of inverse tensor.ordinary, retaining every coefficient-equivalence
unit and counit. Each of those finite mates is invertible by the finite slice tensor
comparison. Joint faithfulness of the ordinary evaluations then detects invertibility
of the system map. The finite mate's component formula is exactly the displayed
unit/inverse-tensor/counit word. No equality of derived maps is detected by evaluation.
The argument includes zero modules, level zero and the empty open. -/
theorem ordinaryRestrictionQuotient
    (tensor : TensorComparison l E j o)
    (MX : CompletionUnit.OrdinaryModel l E X)
    (MU : CompletionUnit.OrdinaryModel l E U) :
    ∃ f : restriction l E j o ⋙ MU.tensor ≅ MX.tensor ⋙ systemRestriction l E j o,
      ∀ (N : scalarReductionSource l E X) (n : ℕ),
        (coefficientSequenceEvaluation l E U n).map (f.hom.app N) ≫
          ((o.finite n).unitIso.app _ ≪≫
    (o.finite n).inverse.mapIso
      ((o.transportEvaluation n).app ((systemRestriction l E j o).obj (MX.tensor.obj N))).symm ≪≫
    (o.finite n).inverse.mapIso
      ((SemilinearSections.evaluation.{t+1, t, max u (t+1)}
        ((ProEt.topology X).over (openObject j))
        (fun k ↦ (rings l E X k).over (openObject j))
        (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
          (openObject j)).map (transitions l E X k)) n).mapIso
        (o.systems.counitIso.app _)) ≪≫
    (o.finite n).inverse.mapIso
      ((o.openSystems.restrictionEvaluation n).app (MX.tensor.obj N))).hom ≫
          (finiteRestriction l E j o n).map ((MX.evaluation n).hom.app N) =
        (MU.evaluation n).hom.app ((restriction l E j o).obj N) ≫ (((o.finite n).toAdjunction.comp
          (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
            (rings l E X n) (openObject j))).unit.app _ ≫
    (finiteRestriction l E j o n).map
      ((tensor.ordinary n).inv.app ((restriction l E j o).obj N)) ≫
    (finiteRestriction l E j o n).map
      ((scalarReductionExtension l E X n).map
        ((ordinaryAdjunction l E j o).counit.app N))) := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : EssentiallySmall.{max u (t + 1)} U.ProEt := essentiallySmallSelf _
  let AX : OpenSemilinearTensor.OrdinaryReduction l E X :=
    { functor := MX.tensor
      evaluation := MX.evaluation
      quotient := fun M _ _ h ↦ MX.transition M h }
  let AU : OpenSemilinearTensor.OrdinaryReduction l E U :=
    { functor := MU.tensor
      evaluation := MU.evaluation
      quotient := fun M _ _ h ↦ MU.transition M h }
  obtain ⟨r, hr⟩ := ordinaryExtensionTensorAssembly l E j o AX AU tensor
  let s : restriction l E j o ⋙ MU.tensor ⟶ MX.tensor ⋙ systemRestriction l E j o :=
    (mateEquiv (ordinaryAdjunction l E j o) (ordinarySystemAdjunction l E j o)
      (TwoSquare.mk _ _ _ _ r.inv))
  have hs (N : scalarReductionSource l E X) (n : ℕ) :
      (coefficientSequenceEvaluation l E U n).map (s.app N) ≫
        (ordinaryRestrictionEvaluation l E j o n).hom.app (MX.tensor.obj N) ≫
          (finiteRestriction l E j o n).map ((MX.evaluation n).hom.app N) =
      (MU.evaluation n).hom.app ((restriction l E j o).obj N) ≫
        (finiteRestrictionMate l E j o tensor n).app N := by
    apply evaluation_right_mate
      (ordinaryAdjunction l E j o) (ordinarySystemAdjunction l E j o)
      (finiteOpenAdjunction l E j o n) MU.tensor MX.tensor
      (coefficientSequenceEvaluation l E U n) (coefficientSequenceEvaluation l E X n)
      (scalarReductionExtension l E U n) (scalarReductionExtension l E X n)
      (MX.evaluation n) (MU.evaluation n) (extensionEvaluation l E j o n)
      (ordinaryRestrictionEvaluation l E j o n) ?_ r (tensor.ordinary n) ?_ N
    · intro Z
      have h := openSystemCounitEvaluation l E j o n Z
      rw [← ordinaryRestrictionEvaluation_app l E j o n Z] at h
      exact h
    · intro M
      rw [hr]
      dsimp only [AX, AU] at ⊢
      simp only [OpenSemilinearTensor.scalarLevelComparison, Iso.trans_hom,
        Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
        Category.comp_id, Category.assoc]
      rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
        (finiteExtension l E j o n).map_id]
      exact congrArg (fun k ↦ (MX.evaluation n).hom.app ((extension l E j o).obj M) ≫ k)
        (CategoryTheory.Category.comp_id ((tensor.ordinary n).hom.app M))
  have he (N : scalarReductionSource l E X) (n : ℕ) :
      IsIso ((coefficientSequenceEvaluation l E U n).map (s.app N)) := by
    have := finiteRestrictionMate_isIso l E j o tensor n
    have hh : IsIso
        ((coefficientSequenceEvaluation l E U n).map (s.app N) ≫
          (ordinaryRestrictionEvaluation l E j o n).hom.app (MX.tensor.obj N) ≫
          (finiteRestriction l E j o n).map ((MX.evaluation n).hom.app N)) := by
      rw [hs]
      infer_instance
    simpa only [isIso_comp_right_iff] using hh
  have hj : JointlyFaithful
      (SemilinearSections.evaluation (ProEt.topology U) (rings l E U)
        (transitions l E U)) := by
    constructor
    intro M N f g h
    exact systemHom_ext (ProEt.topology U) (rings l E U) (transitions l E U) h
  have (N : scalarReductionSource l E X) : IsIso (s.app N) := by
    have (n : ℕ) : IsIso ((SemilinearSections.evaluation (ProEt.topology U)
      (rings l E U) (transitions l E U) n).map (s.app N)) := he N n
    exact hj.jointlyReflectsIsomorphisms.isIso (s.app N)
  have : IsIso s := NatIso.isIso_of_isIso_app s
  refine ⟨asIso s, ?_⟩
  intro N n
  change (coefficientSequenceEvaluation l E U n).map (s.app N) ≫
      (counitRestrictionEvaluation l E j o n (MX.tensor.obj N)).hom ≫
        (finiteRestriction l E j o n).map ((MX.evaluation n).hom.app N) = _
  rw [← ordinaryRestrictionEvaluation_app]
  change (coefficientSequenceEvaluation l E U n).map (s.app N) ≫
      (ordinaryRestrictionEvaluation l E j o n).hom.app (MX.tensor.obj N) ≫
        (finiteRestriction l E j o n).map ((MX.evaluation n).hom.app N) = _
  rw [hs, finiteRestrictionMate_app]

end WeilConjectures.CanonicalOpenRestriction
