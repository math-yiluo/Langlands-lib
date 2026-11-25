/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationQuotientUnits
import all WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSystemUnitSections

/-! # Quotient compatibility of the finite open scalar comparisons

Source: Stacks Project, Modules on Sites, Tags 03DI, 03EK, 0941 and 0E8I.
(blueprint: lem-sf-open-scalar-transition-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] WeilConjectures.scalarReductionExtension
  WeilConjectures.scalarReductionExistence
  WeilConjectures.CoefficientExtensionAssociation.quotientAdjunction
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

private theorem iso_inv_hom_section
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (e : M ≅ N) (V : Cᵒᵖ) (x : N.val.obj V) :
    e.hom.val.app V (e.inv.val.app V x) = x :=
  congrArg (fun f ↦ f.val.app V x) e.inv_hom_id

private theorem iso_hom_section_injective
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (e : M ≅ N) (V : Cᵒᵖ) : Function.Injective (fun x ↦ e.hom.val.app V x) := by
  intro x y h
  exact (iso_inv_hom_section e.symm V x).symm.trans
    ((congrArg (fun z ↦ e.inv.val.app V z) h).trans (iso_inv_hom_section e.symm V y))

private theorem ab_function_heq {A B A' B' : AddCommGrpCat.{u}}
    (a : A = A') (b : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : eqToHom a.symm ≫ f ≫ eqToHom b = g) :
    HEq (fun x : A ↦ f x) (fun x : A' ↦ g x) := by
  subst a
  subst b
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact heq_of_eq (congrArg (fun k ↦ fun x ↦ k x) h)

private theorem adjunction_hom_ext
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {M : C} {N : D}
    (f g : F.obj M ⟶ N)
    (h : adj.unit.app M ≫ G.map f = adj.unit.app M ≫ G.map g) : f = g := by
  apply (adj.homEquiv M N).injective
  simpa only [Adjunction.homEquiv_unit] using h

namespace WeilConjectures.OpenSemilinearTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j) (AX : OrdinaryReduction l E X) (AU : OrdinaryReduction l E U)

/-- Conjugate a finite comparison to the evaluations of the two strict functors.
This definition does not assume that the resulting maps commute with transitions.
Source: Stacks 0941 (blueprint: lem-sf-open-scalar-transition-compatibility). -/
def scalarLevelComparison (tc : IntegralOpenReduction.TensorComparison l E j o) (n : ℕ) :
    (IntegralOpenReduction.extension l E j o ⋙ AX.functor) ⋙
        coefficientSequenceEvaluation l E X n ≅
      (AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o) ⋙
        coefficientSequenceEvaluation l E X n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (IntegralOpenReduction.extension l E j o) (AX.evaluation n) ≪≫
    tc.ordinary n ≪≫
    Functor.isoWhiskerRight (AU.evaluation n).symm
      (IntegralOpenReduction.finiteExtension l E j o n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft AU.functor (IntegralOpenReduction.extensionEvaluation l E j o n).symm ≪≫
    (Functor.associator _ _ _).symm

attribute [local irreducible] scalarLevelComparison

@[irreducible] private def reductionUnit {T : Scheme.{t}} (A : OrdinaryReduction l E T)
    (M : scalarReductionSource l E T) (n : ℕ) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (A.functor.obj M).val.obj (op (n, V.unop)) :=
  ((A.evaluation n).inv.app M).val.app V
    (CoefficientExtensionAssociation.finiteUnitSection l E T M n V x)

private theorem nativeUnit_eq (T : Scheme.{t}) (M : scalarReductionSource l E T)
    (n : ℕ) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    CoefficientExtensionAssociation.finiteUnitSection l E T M n V x =
      coefficientIntegralScalarUnitSection l E T n M V x := by
  unfold CoefficientExtensionAssociation.finiteUnitSection
    CoefficientExtensionAssociation.normalizedUnitSection
    CoefficientExtensionAssociation.quotientAdjunction coefficientIntegralScalarUnitSection
  rfl

private theorem reductionUnit_transition {T : Scheme.{t}}
    (A : OrdinaryReduction l E T) (M : scalarReductionSource l E T)
    {m n : ℕ} (h : n ≤ m) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    HEq (((coefficientSequenceTransition l E T h).app (A.functor.obj M)).val.app V
        (reductionUnit l E A M m V x)) (reductionUnit l E A M n V x) := by
  have hl := CoefficientExtensionAssociation.transportedUnitLaw
    (CoefficientExtensionAssociation.coefficientProjection l E T m)
    (normalizedDVRQuotient l E T h)
    (CoefficientExtensionAssociation.coefficientProjection l E T n)
    (coefficientRestrictionComp l E T h)
    (CoefficientExtensionAssociation.quotientAdjunction l E T m)
    (CoefficientExtensionAssociation.quotientAdjunction l E T n) M
    ((A.evaluation m).app M) ((A.evaluation n).app M)
    ((coefficientSequenceTransition l E T h).app (A.functor.obj M))
    (coefficientOrdinaryQuotient l E T h)
    (CoefficientExtensionAssociation.quotient_mate_law l E T h) (A.quotient M m n h)
  unfold reductionUnit
  unfold CoefficientExtensionAssociation.finiteUnitSection
  exact hl.unit V x

private theorem module_forget_function_eq {R : Type*} [Ring R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (fun x : M ↦ ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map f) x) =
      (fun x : M ↦ f x) := rfl

private theorem presheaf_function_eq {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat} (N : PresheafOfModules.{u} R)
    {V V' : Cᵒᵖ} (f : V ⟶ V') :
    (fun x : N.obj V ↦ N.presheaf.map f x) = (fun x : N.obj V ↦ N.map f x) := rfl

private theorem coefficientTransition_function_heq (T : Scheme.{t})
    (N : coefficientSequenceModules l E T) {m n : ℕ} (h : n ≤ m) (V : T.ProEtᵒᵖ) :
    HEq (fun x : ((coefficientSequenceEvaluation l E T m).obj N).val.obj V ↦
      ((coefficientSequenceTransition l E T h).app N).val.app V x)
      (fun x : N.val.obj (op (m, V.unop)) ↦
        N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) := by
  have hc := (coefficientSequenceTransition_exists l E T h).exists.choose_spec N V
  have he := ab_function_heq
    (coefficientSequenceEvaluationAb_eq l E T N m V)
    (coefficientSequenceRestrictedEvaluationAb_eq l E T N h V) _ _ hc
  unfold coefficientSequenceTransition
  exact (heq_of_eq (module_forget_function_eq _)).symm.trans
    he

private theorem coefficientTransition_apply_heq (T : Scheme.{t})
    (N : coefficientSequenceModules l E T) {m n : ℕ} (h : n ≤ m) (V : T.ProEtᵒᵖ)
    (x : N.val.obj (op (m, V.unop))) :
    HEq (((coefficientSequenceTransition l E T h).app N).val.app V x)
      (N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) :=
  heq_of_eq (congr_heq
    (γ := (N.val.obj (op (n, V.unop)) : Type _))
    (coefficientTransition_function_heq l E T N h V) (HEq.refl x))

private theorem semilinearTransition_apply (N : coefficientSequenceModules l E X)
    {m n : ℕ} (h : n ≤ m) (V : X.ProEtᵒᵖ)
    (x : N.val.obj (op (m, V.unop))) :
    ((SemilinearSections.transition.{t + 1, t, max u (t + 1)}
      (ProEt.topology X) (IntegralOpenReduction.rings l E X)
      (IntegralOpenReduction.transitions l E X) h).app N).val.app V x =
      N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x := by
  unfold SemilinearSections.transition
  have hh := (SemilinearSections.transition_exists.{t + 1, t, max u (t + 1)}
    (ProEt.topology X) (IntegralOpenReduction.rings l E X)
      (IntegralOpenReduction.transitions l E X) h).exists.choose_spec N V
  exact congrFun (eq_of_heq (hh.trans
    (heq_of_eq (presheaf_function_eq N.val _).symm))) x

private theorem reductionUnit_horizontal {T : Scheme.{t}}
    (A : OrdinaryReduction l E T) (M : scalarReductionSource l E T)
    {m n : ℕ} (h : n ≤ m) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (A.functor.obj M).val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op
        (reductionUnit l E A M m V x) = reductionUnit l E A M n V x := by
  have he := coefficientTransition_apply_heq l E T (A.functor.obj M) h V
    (reductionUnit l E A M m V x)
  exact eq_of_heq (he.symm.trans (reductionUnit_transition l E A M h V x))

private theorem extensionSection_ext (M : scalarReductionSource l E U)
    (N : scalarReductionSource l E X)
    (f g : (IntegralOpenReduction.extension l E j o).obj M ⟶ N)
    (h : ∀ (V : X.ProEt) (a : V ⟶ IntegralOpenReduction.openObject j)
      (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
      f.val.app (op V) (IntegralOpenReduction.extensionSection l E j o M V a x) =
        g.val.app (op V) (IntegralOpenReduction.extensionSection l E j o M V a x)) : f = g := by
  unfold IntegralOpenReduction.extension at f g
  apply ((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
    (completedIntegralCommRingSheafUnrestricted l E X)
    (IntegralOpenReduction.openObject j)).homEquiv (o.integral.functor.obj M) N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext y
  let x := ((eqToHom o.integralFunctor).app M).val.app W y
  have hx : (((eqToHom o.integralFunctor.symm).app M).val.app W) x = y := by
    dsimp only [x]
    have hh : eqToHom o.integralFunctor ≫ eqToHom o.integralFunctor.symm =
        𝟙 o.integral.functor :=
      (CategoryTheory.eqToHom_trans _ _).trans (CategoryTheory.eqToHom_refl _ _)
    exact congrArg (fun q ↦ (q.app M).val.app W y) hh
  have hs := h W.unop.left W.unop.hom x
  have hu := (SheafOfModules.localizedSystemAdjunction_existsUnique.{t + 1, t, max u (t + 1)}
    (completedIntegralCommRingSheafUnrestricted l E X)
    (IntegralOpenReduction.openObject j)).exists.choose_spec (o.integral.functor.obj M) W y
  change f.val.app (op W.unop.left)
    (((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E X)
      (IntegralOpenReduction.openObject j)).unit.app (o.integral.functor.obj M)).val.app W y) =
    g.val.app (op W.unop.left)
    (((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E X)
      (IntegralOpenReduction.openObject j)).unit.app (o.integral.functor.obj M)).val.app W y)
  unfold SheafOfModules.localizedSystemAdjunction
  rw [hu]
  dsimp only [IntegralOpenReduction.extensionSection] at hs
  have hx' : (((eqToHom o.integralFunctor.symm).app M).val.app
      (op (Over.mk W.unop.hom))) x = y := hx
  rw [hx'] at hs
  exact hs

private theorem reductionUnit_ext (M : scalarReductionSource l E U) (n : ℕ)
    (N : normalizedDVRModules l E X n)
    (f g : (coefficientSequenceEvaluation l E X n).obj
      (AX.functor.obj ((IntegralOpenReduction.extension l E j o).obj M)) ⟶ N)
    (h : ∀ (V : X.ProEt) (a : V ⟶ IntegralOpenReduction.openObject j)
      (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
      f.val.app (op V) (reductionUnit l E AX _ n (op V)
        (IntegralOpenReduction.extensionSection l E j o M V a x)) =
      g.val.app (op V) (reductionUnit l E AX _ n (op V)
        (IntegralOpenReduction.extensionSection l E j o M V a x))) : f = g := by
  apply (cancel_epi ((AX.evaluation n).inv.app _)).mp
  apply adjunction_hom_ext (scalarReductionExtension_adjunction l E X n).choose
  apply extensionSection_ext l E j o M _
  intro V a x
  have hs := h V a x
  unfold reductionUnit at hs
  have hu := nativeUnit_eq l E X ((IntegralOpenReduction.extension l E j o).obj M) n
    (op V) (IntegralOpenReduction.extensionSection l E j o M V a x)
  have hf := congrArg (fun z ↦ f.val.app (op V)
    (((AX.evaluation n).inv.app _).val.app (op V) z)) hu
  have hg := congrArg (fun z ↦ g.val.app (op V)
    (((AX.evaluation n).inv.app _).val.app (op V) z)) hu
  unfold coefficientIntegralScalarUnitSection at hf hg
  exact hf.symm.trans (hs.trans hg)

private theorem scalarLevelComparison_generator
    (hrestriction : ∀ (n : ℕ) N V x,
      HEq ((((o.openSystems.restrictionEvaluation n).hom.app N).val.app V) x) x)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (M : scalarReductionSource l E U) (n : ℕ) (V : X.ProEt)
    (a : V ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    ((scalarLevelComparison l E j o AX AU tc n).hom.app M).val.app (op V)
        (reductionUnit l E AX _ n (op V)
          (IntegralOpenReduction.extensionSection l E j o M V a x)) =
      systemUnit l E j o (AU.functor.obj M) n (Over.mk a)
        (reductionUnit l E AU M n
          (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x) := by
  apply iso_hom_section_injective
    ((IntegralOpenReduction.extensionEvaluation l E j o n).app (AU.functor.obj M)) (op V)
  have hu := systemUnit_evaluation l E j o hrestriction (AU.functor.obj M) n V a
    (reductionUnit l E AU M n (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)
  refine Eq.trans ?_ hu.symm
  unfold scalarLevelComparison
  unfold reductionUnit
  rw [nativeUnit_eq l E X ((IntegralOpenReduction.extension l E j o).obj M) n
      (op V) (IntegralOpenReduction.extensionSection l E j o M V a x),
    nativeUnit_eq l E U M n (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x]
  change ((IntegralOpenReduction.extensionEvaluation l E j o n).hom.app
      (AU.functor.obj M)).val.app (op V)
      (((IntegralOpenReduction.extensionEvaluation l E j o n).inv.app
        (AU.functor.obj M)).val.app (op V)
        (((IntegralOpenReduction.finiteExtension l E j o n).map
          ((AU.evaluation n).inv.app M)).val.app (op V)
          (((tc.ordinary n).hom.app M).val.app (op V)
            (((AX.evaluation n).hom.app _).val.app (op V)
              (((AX.evaluation n).inv.app _).val.app (op V)
                (coefficientIntegralScalarUnitSection l E X n _ (op V)
                  (IntegralOpenReduction.extensionSection l E j o M V a x))))))) = _
  have hax := iso_inv_hom_section ((AX.evaluation n).app
    ((IntegralOpenReduction.extension l E j o).obj M)) (op V)
    (coefficientIntegralScalarUnitSection l E X n _ (op V)
      (IntegralOpenReduction.extensionSection l E j o M V a x))
  have hgen := (congrArg
    (fun y ↦ ((tc.ordinary n).hom.app M).val.app (op V) y) hax).trans
      (tc.generators n M V a x)
  have hmap := congrArg
    (fun y ↦ ((IntegralOpenReduction.finiteExtension l E j o n).map
      ((AU.evaluation n).inv.app M)).val.app (op V) y) hgen
  have hnat := finiteSection_map l E j o n ((AU.evaluation n).inv.app M) V a
    (coefficientIntegralScalarUnitSection l E U n M
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)
  have hext := iso_inv_hom_section
    ((IntegralOpenReduction.extensionEvaluation l E j o n).app (AU.functor.obj M))
    (op V) (((IntegralOpenReduction.finiteExtension l E j o n).map
      ((AU.evaluation n).inv.app M)).val.app (op V)
      (((tc.ordinary n).hom.app M).val.app (op V)
        (((AX.evaluation n).hom.app _).val.app (op V)
          (((AX.evaluation n).inv.app _).val.app (op V)
            (coefficientIntegralScalarUnitSection l E X n _ (op V)
              (IntegralOpenReduction.extensionSection l E j o M V a x))))))
  exact hext.trans (hmap.trans hnat)

/-- The finite normalized maps commute with every horizontal restriction of the actual
sequence-site presheaves. No lift to a morphism of systems is asserted here.
Source: Stacks 03DI, 03EK, 0941 and 0E8I; transition-square step of strict scalar transport
(blueprint: lem-sf-open-scalar-transition-compatibility).

Proof: conjugate the square by AX.evaluation and AU.evaluation. Their quotient fields
replace the two source transitions by the actual scalar quotient maps. By the
open-system adjunction's unit_evaluation equation and identity restrictionEvaluation,
the target transition sends an original extension summand to the extension of its
coefficient transition. The section normalization of transportEvaluation identifies
this with the original finite extension summand. Precompose both composites with the
scalar-adjunction unit. On every original completed extension summand the two maps
now agree: both send [x] to [x tensor 1], followed by the coefficient quotient, which
preserves one. The open-extension Hom equivalence proves equality on the completed
extension, and the scalar-extension Hom equivalence proves equality on its scalar
extension. Cancel the evaluation isomorphisms. This gives the displayed section
identity for every n ≤ m, including identity transitions and the empty open. -/
theorem openScalarTransitionCompatibility
    (hrestriction : ∀ (n : ℕ) N V x,
      HEq ((((o.openSystems.restrictionEvaluation n).hom.app N).val.app V) x) x)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (M : scalarReductionSource l E U) {m n : ℕ} (h : n ≤ m) :
    (SemilinearSections.transition.{t + 1, t, max u (t + 1)}
      (ProEt.topology X) (IntegralOpenReduction.rings l E X)
      (IntegralOpenReduction.transitions l E X) h).app
        ((IntegralOpenReduction.extension l E j o ⋙ AX.functor).obj M) ≫
      (SemilinearSections.res.{t + 1, t, max u (t + 1)}
        (SemilinearSections.coefficientMap.{t + 1, t, max u (t + 1)}
          (ProEt.topology X) (IntegralOpenReduction.rings l E X)
          (IntegralOpenReduction.transitions l E X) h)).map
            ((scalarLevelComparison l E j o AX AU tc n).hom.app M) =
      (scalarLevelComparison l E j o AX AU tc m).hom.app M ≫
        (SemilinearSections.transition.{t + 1, t, max u (t + 1)}
          (ProEt.topology X) (IntegralOpenReduction.rings l E X)
          (IntegralOpenReduction.transitions l E X) h).app
            ((AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o).obj M) := by
  apply reductionUnit_ext l E j o AX M m _
  intro V a x
  change ((scalarLevelComparison l E j o AX AU tc n).hom.app M).val.app (op V)
      (((SemilinearSections.transition.{t + 1, t, max u (t + 1)}
        (ProEt.topology X) (IntegralOpenReduction.rings l E X)
        (IntegralOpenReduction.transitions l E X) h).app
          (AX.functor.obj ((IntegralOpenReduction.extension l E j o).obj M))).val.app (op V)
        (reductionUnit l E AX _ m (op V)
          (IntegralOpenReduction.extensionSection l E j o M V a x))) =
    ((SemilinearSections.transition.{t + 1, t, max u (t + 1)}
      (ProEt.topology X) (IntegralOpenReduction.rings l E X)
      (IntegralOpenReduction.transitions l E X) h).app
        ((IntegralOpenReduction.systemExtension l E j o).obj (AU.functor.obj M))).val.app
      (op V) (((scalarLevelComparison l E j o AX AU tc m).hom.app M).val.app (op V)
        (reductionUnit l E AX _ m (op V)
          (IntegralOpenReduction.extensionSection l E j o M V a x)))
  have hs := semilinearTransition_apply l E
    (AX.functor.obj ((IntegralOpenReduction.extension l E j o).obj M)) h (op V)
    (reductionUnit l E AX _ m (op V)
      (IntegralOpenReduction.extensionSection l E j o M V a x))
  have hx := reductionUnit_horizontal l E AX
    ((IntegralOpenReduction.extension l E j o).obj M) h (op V)
    (IntegralOpenReduction.extensionSection l E j o M V a x)
  have hcn := scalarLevelComparison_generator l E j o AX AU hrestriction tc M n V a x
  have hcm := scalarLevelComparison_generator l E j o AX AU hrestriction tc M m V a x
  have ht := semilinearTransition_apply l E
    ((IntegralOpenReduction.systemExtension l E j o).obj (AU.functor.obj M)) h (op V)
    (((scalarLevelComparison l E j o AX AU tc m).hom.app M).val.app (op V)
      (reductionUnit l E AX _ m (op V)
        (IntegralOpenReduction.extensionSection l E j o M V a x)))
  have hu := systemUnit_horizontal l E j o (AU.functor.obj M) h (Over.mk a)
    (reductionUnit l E AU M m
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)
  have hy := reductionUnit_horizontal l E AU M h
    (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x
  have hr := ht.trans ((congrArg
    (fun y ↦ (((IntegralOpenReduction.systemExtension l E j o).obj
      (AU.functor.obj M)).val.presheaf).map (Prod.mkHom (homOfLE h) (𝟙 V)).op y) hcm).trans
        (hu.trans (congrArg (systemUnit l E j o (AU.functor.obj M) n (Over.mk a)) hy)))
  exact (congrArg
    (fun y ↦ ((scalarLevelComparison l E j o AX AU tc n).hom.app M).val.app (op V) y)
    (hs.trans hx)).trans (hcn.trans hr.symm)

end WeilConjectures.OpenSemilinearTensor
