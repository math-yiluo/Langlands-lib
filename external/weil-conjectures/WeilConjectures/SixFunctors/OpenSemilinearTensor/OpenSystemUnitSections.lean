/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData

/-! # Section calculus for the ordinary open-system unit

Source: Stacks Project, Tags 03DI--03DJ and evaluation before 0941.
(blueprint: lem-sf-open-system-unit-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] WeilConjectures.scalarReductionExtension
  WeilConjectures.scalarReductionExistence
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.coefficientSequenceTransition
  WeilConjectures.coefficientOrdinaryQuotient
  WeilConjectures.coefficientIntegralScalarUnitSection
  WeilConjectures.coefficientOrdinaryQuotientComponent
  WeilConjectures.coefficientQuotientNatTrans
  WeilConjectures.IntegralOpenReduction.extensionEvaluation
  CategoryTheory.Functor.leftAdjoint CategoryTheory.constantSheaf
  CategoryTheory.presheafToSheaf CategoryTheory.Functor.ofSequence
  CategoryTheory.Functor.ofOpSequence
  WeilConjectures.SemilinearSections.coefficientMap
  WeilConjectures.SemilinearSections.transition

attribute [local implicit_reducible] WeilConjectures.coefficientSequenceEvaluation
  WeilConjectures.SemilinearSections.evaluation
  WeilConjectures.SemilinearSections.openTransitions
  CategoryTheory.Functor.sheafPushforwardContinuous
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.integralCoefficientSheaf
  CategoryTheory.sheafCompose
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf
  WeilConjectures.SemilinearSections.rings
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.coefficientSequenceCommRingSystem
  SheafOfModules.overFunctor SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalarsObj
  ModuleCat.RestrictScalars.obj' ModuleCat.RestrictScalars.map'
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars

universe t u a c v w
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem functor_eqToHom_section_heq
    {A : Type a} {C : Type c} [Category.{v} A] [Category.{w} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {F G : A ⥤ SheafOfModules.{u} R}
    (e : F = G) (M : A) (V : Cᵒᵖ) (x : (F.obj M).val.obj V) :
    HEq (((eqToHom e).app M).val.app V x) x := by
  cases e
  rfl

namespace WeilConjectures.OpenSemilinearTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j) (AX : OrdinaryReduction l E X) (AU : OrdinaryReduction l E U)

private theorem presheaf_naturality_apply {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat} {M N : PresheafOfModules.{u} R} (f : M ⟶ N)
    {V W : Cᵒᵖ} (g : V ⟶ W) (x : M.obj V) :
    f.app W (M.presheaf.map g x) = N.presheaf.map g (f.app V x) :=
  PresheafOfModules.naturality_apply f g x

private theorem pushforward_naturality_apply
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {R : Sheaf K RingCat.{u}} {S : Sheaf J RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (M : SheafOfModules.{u} R) {N : SheafOfModules.{u} S}
    (f : N ⟶ (SheafOfModules.pushforward φ).obj M)
    {V W : Cᵒᵖ} (g : V ⟶ W) (x : N.val.obj V) :
    f.val.app W (N.val.presheaf.map g x) =
      M.val.presheaf.map (F.map g.unop).op (f.val.app V x) :=
  presheaf_naturality_apply f.val g x

/-- Transport a section through the recorded literal system pushforward.
Source: Stacks 03DJ (blueprint: lem-sf-open-system-unit-sections). -/
def transportedSection (N : coefficientSequenceModules l E U) (n : ℕ)
    (W : Over (IntegralOpenReduction.openObject j))
    (x : N.val.obj (op (n, (IntegralOpenReduction.sliceSite j).obj W))) :
    (o.systems.functor.obj N).val.obj (op (n, W)) :=
  ((eqToHom o.systemsFunctor.symm).app N).val.app (op (n, W)) x

/-- The ordinary open-system adjunction unit applied to a transported section.
Source: Stacks 03DI--03DJ (blueprint: lem-sf-open-system-unit-sections). -/
def systemUnit (N : coefficientSequenceModules l E U) (n : ℕ)
    (W : Over (IntegralOpenReduction.openObject j))
    (x : N.val.obj (op (n, (IntegralOpenReduction.sliceSite j).obj W))) :
    ((IntegralOpenReduction.systemExtension l E j o).obj N).val.obj (op (n, W.left)) :=
  (o.openSystems.ordinaryAdjunction.unit.app (o.systems.functor.obj N)).val.app
    (op (n, W)) (transportedSection l E j o N n W x)

private theorem transportedSection_horizontal (N : coefficientSequenceModules l E U)
    {m n : ℕ} (h : n ≤ m) (W : Over (IntegralOpenReduction.openObject j))
    (x : N.val.obj (op (m, (IntegralOpenReduction.sliceSite j).obj W))) :
    (o.systems.functor.obj N).val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 W)).op
        (transportedSection l E j o N m W x) =
      transportedSection l E j o N n W
        (N.val.presheaf.map (Prod.mkHom (homOfLE h)
          (𝟙 ((IntegralOpenReduction.sliceSite j).obj W))).op x) := by
  unfold transportedSection
  have hn := (presheaf_naturality_apply
    (((eqToHom o.systemsFunctor.symm).app N).val)
    (Prod.mkHom (homOfLE h) (𝟙 W)).op x).symm
  change (o.systems.functor.obj N).val.presheaf.map _
      (((eqToHom o.systemsFunctor.symm).app N).val.app (op (m, W)) x) =
    (((eqToHom o.systemsFunctor.symm).app N).val.app (op (n, W)))
      (N.val.presheaf.map (((𝟭 ℕ).prod (IntegralOpenReduction.sliceSite j)).map
        (Prod.mkHom (homOfLE h) (𝟙 W))).op x) at hn
  simp only [Functor.prod_map, Functor.id_map] at hn
  rw [CategoryTheory.Functor.map_id] at hn
  exact hn

private theorem systemUnit_horizontal (N : coefficientSequenceModules l E U)
    {m n : ℕ} (h : n ≤ m) (W : Over (IntegralOpenReduction.openObject j))
    (x : N.val.obj (op (m, (IntegralOpenReduction.sliceSite j).obj W))) :
    ((IntegralOpenReduction.systemExtension l E j o).obj N).val.presheaf.map
        (Prod.mkHom (homOfLE h) (𝟙 W.left)).op (systemUnit l E j o N m W x) =
      systemUnit l E j o N n W
        (N.val.presheaf.map (Prod.mkHom (homOfLE h)
          (𝟙 ((IntegralOpenReduction.sliceSite j).obj W))).op x) := by
  have hn := (pushforward_naturality_apply
    (eqToHom (SemilinearSections.openRing.{t + 1, t, max u (t + 1)}
      (ProEt.topology X) (IntegralOpenReduction.rings l E X)
      (IntegralOpenReduction.transitions l E X) (IntegralOpenReduction.openObject j)).symm)
    (o.openSystems.extension.obj (o.systems.functor.obj N))
    (N := o.systems.functor.obj N)
    (o.openSystems.ordinaryAdjunction.unit.app (o.systems.functor.obj N))
    (Prod.mkHom (homOfLE h) (𝟙 W)).op
    (transportedSection l E j o N m W x)).symm
  have ht := congrArg
    (fun y ↦ (o.openSystems.ordinaryAdjunction.unit.app
      (o.systems.functor.obj N)).val.app (op (n, W)) y)
    (transportedSection_horizontal l E j o N h W x)
  have hr := hn.trans ht
  simp only [Opposite.unop_op] at hr
  exact hr

private theorem finiteSection_unit (n : ℕ) (M : normalizedDVRModules l E U n)
    (V : X.ProEt) (a : V ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    ((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
      (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).unit.app
        ((o.finite n).functor.obj M)).val.app (op (Over.mk a))
        (((eqToHom (o.finiteFunctor n).symm).app M).val.app (op (Over.mk a)) x) =
      IntegralOpenReduction.finiteExtensionSection l E j o n M V a x := by
  exact (SheafOfModules.localizedSystemAdjunction_existsUnique.{t + 1, t, max u (t + 1)}
    (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).exists.choose_spec
      _ _ _

private theorem finiteSection_map (n : ℕ) {M N : normalizedDVRModules l E U n}
    (f : M ⟶ N) (V : X.ProEt) (a : V ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    ((IntegralOpenReduction.finiteExtension l E j o n).map f).val.app (op V)
        (IntegralOpenReduction.finiteExtensionSection l E j o n M V a x) =
      IntegralOpenReduction.finiteExtensionSection l E j o n N V a
        (f.val.app (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x) := by
  rw [← finiteSection_unit l E j o, ← finiteSection_unit l E j o]
  have hn := congrArg (fun q ↦ q.val.app (op (Over.mk a))
    (((eqToHom (o.finiteFunctor n).symm).app M).val.app (op (Over.mk a)) x))
    ((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
      (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).unit.naturality
        ((o.finite n).functor.map f))
  have ht := congrArg (fun q ↦ q.val.app (op (Over.mk a)) x)
    ((eqToHom (o.finiteFunctor n).symm).naturality f)
  change (((eqToHom (o.finiteFunctor n).symm).app N).val.app (op (Over.mk a)))
      (f.val.app (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x) =
    ((o.finite n).functor.map f).val.app (op (Over.mk a))
      (((eqToHom (o.finiteFunctor n).symm).app M).val.app (op (Over.mk a)) x) at ht
  change ((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
      (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).unit.app
        ((o.finite n).functor.obj N)).val.app (op (Over.mk a))
      (((o.finite n).functor.map f).val.app (op (Over.mk a))
        (((eqToHom (o.finiteFunctor n).symm).app M).val.app (op (Over.mk a)) x)) =
    ((IntegralOpenReduction.finiteExtension l E j o n).map f).val.app (op V)
      (((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
        (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).unit.app
          ((o.finite n).functor.obj M)).val.app (op (Over.mk a))
        (((eqToHom (o.finiteFunctor n).symm).app M).val.app (op (Over.mk a)) x)) at hn
  rw [← ht] at hn
  exact hn.symm

/-- Evaluation of the system unit is the original finite extension summand.

Source: Stacks 03DI--03DJ and sequence-site evaluation before 0941.
(blueprint: lem-sf-open-system-unit-sections).

Proof: apply the given unit-evaluation equation to the transported section.
Identity on sections removes restrictionEvaluation. The transportSections equation
and the sectionwise identity of eqToHom identify transportEvaluation with the
finite coefficient transport. Naturality of the finite localized adjunction unit
moves that transport through the unit. Finally its prescribed direct-sum injection
is precisely finiteExtensionSection. The argument applies to every finite level,
every slice object and every section, also for the empty open. -/
theorem systemUnit_evaluation
    (hrestriction : ∀ (n : ℕ) N V x,
      HEq ((((o.openSystems.restrictionEvaluation n).hom.app N).val.app V) x) x)
    (N : coefficientSequenceModules l E U) (n : ℕ) (V : X.ProEt)
    (a : V ⟶ IntegralOpenReduction.openObject j)
    (x : ((coefficientSequenceEvaluation l E U n).obj N).val.obj
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    ((IntegralOpenReduction.extensionEvaluation l E j o n).hom.app N).val.app (op V)
        (systemUnit l E j o N n (Over.mk a) x) =
      IntegralOpenReduction.finiteExtensionSection l E j o n
        ((coefficientSequenceEvaluation l E U n).obj N) V a x := by
  have hu := congrArg (fun q ↦ q.val.app (op (Over.mk a))
    (transportedSection l E j o N n (Over.mk a) x))
    (o.openSystems.unit_evaluation n (o.systems.functor.obj N))
  have ht := o.transportSections n N (op (Over.mk a))
    (transportedSection l E j o N n (Over.mk a) x)
  have he := functor_eqToHom_section_heq
    (F := _) (G := o.systems.functor) o.systemsFunctor.symm N
    (op (n, Over.mk a)) x
  have hf := functor_eqToHom_section_heq
    (F := _) (G := (o.finite n).functor) (o.finiteFunctor n).symm
    ((coefficientSequenceEvaluation l E U n).obj N) (op (Over.mk a)) x
  have ht' : ((o.transportEvaluation n).hom.app N).val.app (op (Over.mk a))
      (transportedSection l E j o N n (Over.mk a) x) =
    ((eqToHom (o.finiteFunctor n).symm).app
      ((coefficientSequenceEvaluation l E U n).obj N)).val.app (op (Over.mk a)) x :=
    by
      unfold transportedSection at ht
      exact eq_of_heq (ht.trans (he.trans hf.symm))
  unfold systemUnit at hu ⊢
  change ((o.openSystems.extensionEvaluation n).hom.app (o.systems.functor.obj N)).val.app
      (op V)
      (((o.openSystems.restrictionEvaluation n).hom.app
        (o.openSystems.extension.obj (o.systems.functor.obj N))).val.app (op (Over.mk a))
        (systemUnit l E j o N n (Over.mk a) x)) = _ at hu
  have hr := congrArg
    (fun y ↦ ((o.openSystems.extensionEvaluation n).hom.app
      (o.systems.functor.obj N)).val.app (op V) y)
    (eq_of_heq (hrestriction n
      (o.openSystems.extension.obj (o.systems.functor.obj N)) (op (Over.mk a))
      (systemUnit l E j o N n (Over.mk a) x)))
  replace hu := hr.symm.trans hu
  have hn := congrArg (fun q ↦ q.val.app (op (Over.mk a))
    (transportedSection l E j o N n (Over.mk a) x))
    ((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
      (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).unit.naturality
        ((o.transportEvaluation n).hom.app N))
  unfold IntegralOpenReduction.extensionEvaluation
  change ((SheafOfModules.localizedSystemExtension.{t + 1, t, max u (t + 1)}
    (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).map
      ((o.transportEvaluation n).hom.app N)).val.app (op V)
      (((o.openSystems.extensionEvaluation n).hom.app (o.systems.functor.obj N)).val.app
        (op V) (systemUnit l E j o N n (Over.mk a) x)) = _
  rw [hu]
  change ((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
      (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).unit.app
        ((o.finite n).functor.obj ((coefficientSequenceEvaluation l E U n).obj N))).val.app
      (op (Over.mk a)) (((o.transportEvaluation n).hom.app N).val.app (op (Over.mk a))
        (transportedSection l E j o N n (Over.mk a) x)) =
    ((SheafOfModules.localizedSystemExtension.{t + 1, t, max u (t + 1)}
      (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).map
        ((o.transportEvaluation n).hom.app N)).val.app (op V)
      (((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
        (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).unit.app
          _).val.app (op (Over.mk a))
          (transportedSection l E j o N n (Over.mk a) x)) at hn
  exact hn.symm.trans ((congrArg
    (fun y ↦ ((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
      (IntegralOpenReduction.rings l E X n) (IntegralOpenReduction.openObject j)).unit.app
        ((o.finite n).functor.obj ((coefficientSequenceEvaluation l E U n).obj N))).val.app
          (op (Over.mk a)) y) ht').trans
      (finiteSection_unit l E j o n _ V a x))

end WeilConjectures.OpenSemilinearTensor
