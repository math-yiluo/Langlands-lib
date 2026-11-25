/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! # Finite evaluation of the ordinary system open counit

Source: Stacks 03DI, 03DJ and 0941; ordinary open-factor argument of fix-prop-coherence.
(blueprint: lem-sf-ordinary-open-finite-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev rings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))

private abbrev transition (n : ℕ) : rings l E (n + 1) ⟶ rings l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift

private theorem direct_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDirect l E f =
      ProEtale.VaryingRing.push (rings l E) (transition l E) f := by
  unfold pullbackTensorSequenceDirect
  rw [pullbackTensorSequenceRing_eq]
  rfl

private theorem finiteDirect_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    coefficientProEtaleModuleDirectImage.{u, u} f (rings l E n) =
      ProEtale.StrictTower.moduleDirectImage (rings l E n) f := by
  have h : proEtaleRingDirectImageMap f
      (ProEtale.VaryingRing.coefficients (rings l E) Y n)
      (ProEtale.VaryingRing.coefficients (rings l E) X n)
      (ProEtale.StrictTower.constantRingIso (rings l E n) f) =
      coefficientProEtaleDirectRingMap.{u, u} f (rings l E n) :=
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  unfold ProEtale.StrictTower.moduleDirectImage proEtaleRingModuleDirectImage
    coefficientProEtaleModuleDirectImage
  rw [h]
  rfl

private theorem inverseMate_change_left
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (b₁ : L₁' ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₂ : L₂' ⊣ R₂)
    (w : TwoSquare R₁ H G R₂)
    [IsIso ((mateEquiv b₁ b₂).symm w)] :
    IsIso ((mateEquiv a₁ a₂).symm w) := by
  have hw : (mateEquiv a₁ a₂).symm w = TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft G (a₂.leftAdjointUniq b₂).hom ≫
        ((mateEquiv b₁ b₂).symm w) ≫
          Functor.whiskerRight (a₁.leftAdjointUniq b₁).inv H) := by
    apply (mateEquiv a₁ a₂).injective
    rw [Equiv.apply_symm_apply, mateEquiv_leftAdjointUniq, Equiv.apply_symm_apply]
  rw [hw]
  dsimp only [TwoSquare.mk]
  apply IsIso.comp_isIso'
  · exact (Functor.isoWhiskerLeft G (a₂.leftAdjointUniq b₂)).isIso_hom
  · apply IsIso.comp_isIso'
    · infer_instance
    · exact (Functor.isoWhiskerRight (a₁.leftAdjointUniq b₁).symm H).isIso_hom

private theorem normalizedFunction {A B D : Type u}
    (hA : A = D) (hB : B = D) (f : A → B) (hf : ∀ x, HEq (f x) x) :
    HEq f (fun x : D ↦ x) := by
  subst A B
  exact heq_of_eq (funext fun x ↦ eq_of_heq (hf x))

attribute [local irreducible] constantSheaf presheafToSheaf
  Functor.ofOpSequence Functor.ofSequence
  proEtaleRingDirectImageMap proEtaleConstantDirectImageMap
  ProEtale.StrictTower.constantRingIso

attribute [local implicit_reducible] ProEtale.StrictTower.modulePullback
  ProEtale.StrictTower.moduleDirectImage ProEtale.VaryingRing.coefficientTransition

open Opposite in
private theorem normalizedFiniteEvaluation
    (R : ℕ → CommRingCat.{u + 1}) (τ : ∀ k, R (k + 1) ⟶ R k)
    {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ)
    (F : ProEtale.VaryingRing.Modules R τ X ⥤ ProEtale.VaryingRing.Modules R τ Y)
    [hFadj : F.IsRightAdjoint]
    (hF : F = ProEtale.VaryingRing.push R τ j)
    (Q : ProEtale.StrictTower.Modules (R n) Y ⥤ ProEtale.StrictTower.Modules (R n) X)
    (Fn : ProEtale.StrictTower.Modules (R n) X ⥤ ProEtale.StrictTower.Modules (R n) Y)
    (hFn : Fn = ProEtale.StrictTower.moduleDirectImage (R n) j)
    (b : Q ⊣ Fn)
    (O : ProEtale.VaryingRing.Modules R τ X ⥤ ProEtale.VaryingRing.Modules R τ Y)
    (a : O ⊣ F.leftAdjoint)
    (d : F ⋙ ProEtale.VaryingRing.eval R τ Y n ≅
      ProEtale.VaryingRing.eval R τ X n ⋙ Fn)
    (hd : ∀ (M : ProEtale.VaryingRing.Modules R τ X) (U : Y.ProEt)
      (x : ((F ⋙ ProEtale.VaryingRing.eval R τ Y n).obj M).val.obj (op U)),
      HEq ((d.hom.app M).val.app (op U) x) x)
    (β : ProEtale.VaryingRing.eval R τ Y n ⋙ Q ≅
      F.leftAdjoint ⋙ ProEtale.VaryingRing.eval R τ X n)
    (hβ : ∀ M, b.homEquiv _ _ (β.hom.app M) =
      (ProEtale.VaryingRing.eval R τ Y n).map
        ((Adjunction.ofIsRightAdjoint F).unit.app M) ≫ d.hom.app (F.leftAdjoint.obj M)) :
    ∃ (L : ProEtale.StrictTower.Modules (R n) X ⥤ ProEtale.StrictTower.Modules (R n) Y)
      (adj : L ⊣ Q)
      (e : O ⋙ ProEtale.VaryingRing.eval R τ Y n ≅
        ProEtale.VaryingRing.eval R τ X n ⋙ L),
      ∀ N : ProEtale.VaryingRing.Modules R τ Y,
        (ProEtale.VaryingRing.eval R τ Y n).map (a.counit.app N) =
          e.hom.app (F.leftAdjoint.obj N) ≫ L.map (β.inv.app N) ≫
            adj.counit.app ((ProEtale.VaryingRing.eval R τ Y n).obj N) := by
  subst F
  subst Fn
  let EY := ProEtale.VaryingRing.eval R τ Y n
  let ag := ProEtale.VaryingRing.moduleAdj R τ j
  let bg := proEtaleRingModuleAdjunction j
    (ProEtale.VaryingRing.coefficients R Y n)
    (ProEtale.VaryingRing.coefficients R X n)
    (ProEtale.StrictTower.constantRingIso (R n) j)
  let g := ProEtale.VaryingRing.moduleEvalG R τ j n
  -- The prescribed direct comparison is fixed on every underlying section.
  have hd' : d = ProEtale.VaryingRing.moduleEvalP R τ j n := by
    apply ProEtale.VaryingRing.moduleFunctorIso_ext
    intro M U x
    have hD : HEq (fun y ↦ (d.hom.app M).val.app U y)
        (fun y : M.val.obj (op (n, (proEtaleBaseChange j).obj U.unop)) ↦ y) :=
      normalizedFunction rfl rfl _ (hd M U.unop)
    have hP : HEq
        (fun y ↦ ((ProEtale.VaryingRing.moduleEvalP R τ j n).hom.app M).val.app U y)
        (fun y : M.val.obj (op (n, (proEtaleBaseChange j).obj U.unop)) ↦ y) := by
      apply heq_of_eq
      funext y
      dsimp only [ProEtale.VaryingRing.moduleEvalP]
      exact (ProEtale.VaryingRing.moduleEvalP_existsUnique R τ j n).choose_spec.1 M U.unop y
    exact congrFun (eq_of_heq (hD.trans hP.symm)) x
  subst d
  -- Transport the finite inverse image while retaining its unit normalization.
  let q := b.leftAdjointUniq bg
  have hg (M : ProEtale.VaryingRing.Modules R τ Y) :
      bg.homEquiv _ _ (g.inv.app M) = EY.map (ag.unit.app M) ≫
        (ProEtale.VaryingRing.moduleEvalP R τ j n).hom.app _ := by
    rw [Adjunction.homEquiv_unit]
    change bg.unit.app (EY.obj M) ≫
      (ProEtale.StrictTower.moduleDirectImage (R n) j).map (g.inv.app M) = _
    apply (cancel_mono ((ProEtale.StrictTower.moduleDirectImage (R n) j).map
      (g.hom.app M))).mp
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    exact ((ProEtale.VaryingRing.moduleEvalG_existsUnique R τ j n).choose_spec.1 M).symm
  have hb : β = Functor.isoWhiskerLeft EY q ≪≫ g.symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (b.homEquiv _ _).injective
    rw [hβ]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Adjunction.homEquiv_unit,
      Functor.map_comp, ← Category.assoc]
    rw [b.unit_leftAdjointUniq_hom_app bg]
    exact (hg M).symm
  -- The existing open mate theorem supplies the finite extension isomorphism.
  let bn := ProEtale.StrictTower.moduleJAdj (R n) j
  let α := ((mateEquiv a bn).symm (TwoSquare.mk _ _ _ _ g.hom))
  have hα : IsIso α := by
    have : IsIso ((mateEquiv (ProEtale.VaryingRing.moduleJAdj R τ j) bn).symm
        (TwoSquare.mk _ _ _ _ g.hom)) :=
      ProEtale.VaryingRing.ordinaryOpenMateIso R τ j n
    exact inverseMate_change_left a (ProEtale.VaryingRing.moduleJAdj R τ j)
      bn bn (TwoSquare.mk _ _ _ _ g.hom)
  let e := (@asIso _ _ _ _ α hα).symm
  let adj := bn.ofNatIsoRight q.symm
  refine ⟨ProEtale.StrictTower.moduleJ (R n) j, adj, e, ?_⟩
  intro N
  have hc := mateEquiv_counit_symm a bn (TwoSquare.mk _ _ _ _ g.hom) N
  have hc' : EY.map (a.counit.app N) = e.hom.app _ ≫
      (ProEtale.StrictTower.moduleJ (R n) j).map (g.hom.app N) ≫
        bn.counit.app (EY.obj N) := by
    rw [hc]
    exact (Iso.inv_hom_id_app_assoc (asIso α) _ _).symm
  -- The mate counit identity and cancellation of q give the prescribed formula.
  rw [hc', hb]
  let J := ProEtale.StrictTower.moduleJ (R n) j
  change e.hom.app _ ≫ J.map (g.hom.app N) ≫ bn.counit.app _ =
    e.hom.app _ ≫ J.map (g.hom.app N ≫ q.inv.app (EY.obj N)) ≫
      (J.map (q.hom.app (EY.obj N)) ≫ bn.counit.app _)
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  exact congrArg (fun t ↦ e.hom.app _ ≫ J.map t ≫ bn.counit.app (EY.obj N))
    (Category.comp_id (g.hom.app N)).symm

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceBase pullbackTensorSequenceDirect pullbackTensorSequenceInverse
  pullbackTensorSequenceAdjunction coefficientSequenceEvaluation integralOperationsLevelPullback
  pullbackTensorSequenceInverseEvaluation pullbackTensorSequenceDirectEvaluation
  coefficientSequenceCommRingTransition integralCoefficientSheafTransition
  coefficientProEtaleModuleAdjunction coefficientProEtaleModulePullback in
/-- Evaluation carries the ordinary open counit to its finite-level counit.
Source: Stacks 03DI, 03DJ and 0941; fix-prop-coherence, ordinary open-factor argument.
(blueprint: lem-sf-ordinary-open-finite-evaluation).

Proof: identify the pro-etale site of the open with the ambient slice. On the sequence
site this identification is its product with the coefficient index. Extension by zero
is the direct-sum presheaf followed by module sheafification. Restriction to one index
commutes with both constructions, since covers are vertical. This gives the finite
left adjoint and the evaluation isomorphism. On each original extension summand the
counit is evaluation at the corresponding factorization through the open, so the
counit square commutes. The inverse-image evaluation comparison is the canonical
adjoint transpose of identity on direct-image sections, hence is precisely
pullbackTensorSequenceInverseEvaluation. Sheafification uniqueness proves the square
for all sections. Finally transport from this extension to the supplied o by uniqueness
of left adjoints; this transport preserves the counit. Empty opens have empty sums,
and the identity open has its single identity summand. No module flatness is used. -/
theorem ordinaryOpenFiniteEvaluation {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (o : Open l E j) (n : ℕ) :
    ∃ (L : normalizedDVRModules l E X n ⥤ normalizedDVRModules l E Y n)
      (adj : L ⊣ integralOperationsLevelPullback l E j n)
      (e : o.ordinary ⋙ coefficientSequenceEvaluation l E Y n ≅
        coefficientSequenceEvaluation l E X n ⋙ L),
      ∀ N : coefficientSequenceModules l E Y,
        (coefficientSequenceEvaluation l E Y n).map (o.adjunction.counit.app N) =
          e.hom.app ((pullbackTensorSequenceInverse l E j).obj N) ≫
            L.map ((pullbackTensorSequenceInverseEvaluation l E j n).inv.app N) ≫
            adj.counit.app ((coefficientSequenceEvaluation l E Y n).obj N) := by
  exact normalizedFiniteEvaluation (rings l E) (transition l E) j n
    (pullbackTensorSequenceDirect l E j)
    (hFadj := pullbackTensorSequenceDirect_rightAdjoint l E j) (direct_eq l E j)
    (integralOperationsLevelPullback l E j n)
    (coefficientProEtaleModuleDirectImage.{u, u} j (rings l E n))
    (finiteDirect_eq l E j n)
    (coefficientProEtaleModuleAdjunction.{u, u} j (rings l E n))
    o.ordinary o.adjunction (pullbackTensorSequenceDirectEvaluation l E j n)
    (pullbackTensorSequenceDirectEvaluation_existsUnique l E j n).exists.choose_spec
    (pullbackTensorSequenceInverseEvaluation l E j n)
    (pullbackTensorSequenceInverseEvaluation_existsUnique l E j n).exists.choose_spec

end WeilConjectures.IntegralSystemRealization
