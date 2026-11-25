/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicTensorLocalization
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensorCoherence
import all WeilConjectures.SmoothPurity.Sf.SfRationalScalarExactOfIntegral
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.IntrinsicScalarNormalizationFormulas

/-! # Comparing the integral and rational scalar stage systems

Source: blueprint orders 1460, 1462 and 1828; Stacks Tag 05R6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option linter.all false
attribute [local irreducible] HasDerivedCategory.standard

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] ScalarLocalization.category
  sfRationalTriangulationDatum sfRationalScalarExtension ScalarLocalization.composition

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The comparison on integral representatives, before transporting the stage system.
Source: blueprint order 1828 (blueprint: lem-sf-native-integral-rational-scalar-comparison). -/
def integralRationalScalarComparison
    (E L : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (h : E →ₐ[Padic l] L) :
    sfRationalConstructibleLocalization l (E) X ⋙
        sfRationalScalarExtension l E X 0 (Fact.out : l.Prime).ne_zero L h ≅
      sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero E L h X ⋙
        sfRationalConstructibleLocalization l (L) X := by
  let F := sfRationalScalarExtension l E X 0 (Fact.out : l.Prime).ne_zero L h
  let T := sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero E L h X
  let Q := sfRationalConstructibleLocalization l (E) X
  let Q' := sfRationalConstructibleLocalization l (L) X
  have hobj := sfRationalScalarExtension_obj l (E) X
    0 (Fact.out : l.Prime).ne_zero (L)
    (h)
  refine NatIso.ofComponents (F := Q ⋙ F) (G := T ⋙ Q') (fun K ↦ eqToIso (hobj (Q.obj K))) ?_
  intro K K' f
  change F.map (Q.map f) ≫ eqToHom (hobj (Q.obj K')) =
    eqToHom (hobj (Q.obj K)) ≫ Q'.map (T.map f)
  have hm := sfRationalScalarExtension_map_tmul l
    (E) X 0 (Fact.out : l.Prime).ne_zero
    (L) (h)
    K K' f 1
  have hm' : HEq (F.map (Q.map f)) (Q'.map (T.map f)) := by
    simp only [map_one] at hm
    dsimp only [F, Q, Q', sfRationalConstructibleLocalization,
      ScalarLocalization.localization, T] at hm ⊢
    with_unfolding_all exact hm
  exact eq_of_heq ((comp_eqToHom_heq _ _).trans
    (hm'.trans (eqToHom_comp_heq _ _).symm))

private theorem integralLocalization_shift_hom
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X) :
    HEq (((sfRationalConstructibleLocalization l E X).commShiftIso (1 : ℤ)).hom.app K)
      (𝟙 ((sfRationalConstructibleLocalization l E X).obj (K⟦(1 : ℤ)⟧))) := by
  exact (((sfRationalTriangulationDatum l E X
    ).choose_spec.choose_spec.2).choose_spec.choose_spec).1 K

private theorem integralAssociator_image
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) :
    HEq ((GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k).hom.app
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj K))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω M) X).map
        ((integralTensorAssociator l X Ω h k).hom.app K)) := by
  rw [integralTensorAssociator_eq]
  exact GeneralAlgebraicallyClosedCoefficients.intrinsicRationalScalarAssociator_image
    l Ω X E L M h k K

/-- The raw integral-image object formula, typed in the named stage categories.
Source: blueprint order 1828
(blueprint: lem-sf-native-integral-rational-scalar-comparison). -/
theorem rationalIntegralTransitionRaw_obj {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (GeneralAlgebraicallyClosedCoefficients.transition l (PadicAlgCl l) X E L h).obj
        ((stageLocalization l X E).obj K) =
      (stageLocalization l X L).obj
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition
          l (PadicAlgCl l) X E L h).obj K) := by
  exact sfRationalScalarExtension_obj l (Coefficient.{u} l (PadicAlgCl l) E) X
    0 (Fact.out : l.Prime).ne_zero (Coefficient.{u} l (PadicAlgCl l) L)
    (coefficientInclusion l (PadicAlgCl l) E L h) _

/-- The comparison on integral representatives, before transporting the stage system.
Source: blueprint order 1828 (blueprint: lem-sf-native-integral-rational-scalar-comparison). -/
def rationalIntegralTransitionRaw {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    stageLocalization l X E ⋙
        GeneralAlgebraicallyClosedCoefficients.transition l (PadicAlgCl l) X E L h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X E L h ⋙
        stageLocalization l X L := by
  let Q := stageLocalization l X E
  let Q' := stageLocalization l X L
  let F := GeneralAlgebraicallyClosedCoefficients.transition l (PadicAlgCl l) X E L h
  let T := GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X E L h
  have hobj := rationalIntegralTransitionRaw_obj l X h
  refine NatIso.ofComponents (F := Q ⋙ F) (G := T ⋙ Q')
    (fun K ↦ eqToIso (hobj K)) ?_
  intro K K' f
  exact (integralRationalScalarComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
    (Coefficient.{u} l (PadicAlgCl l) L)
    (coefficientInclusion l (PadicAlgCl l) E L h)).hom.naturality f

private theorem rationalIntegralTransitionRaw_shift_one
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    NatTrans.CommShiftCore (rationalIntegralTransitionRaw l X h).hom (1 : ℤ) := by
  let F := GeneralAlgebraicallyClosedCoefficients.transition l (PadicAlgCl l) X E L h
  let T := GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X E L h
  let Q := stageLocalization l X E
  let Q' := stageLocalization l X L
  let c := rationalIntegralTransitionRaw l X h
  have hobj := rationalIntegralTransitionRaw_obj l X h
  have hc (K) : c.hom.app K = eqToHom (hobj K) := by rfl
  have qobj (K) : Q.obj (K⟦(1 : ℤ)⟧) = (Q.obj K)⟦(1 : ℤ)⟧ := by
    change (sfRationalConstructibleLocalization l
      (Coefficient.{u} l (PadicAlgCl l) E) X).obj (K⟦(1 : ℤ)⟧) =
      (shiftFunctor (sfRationalConstructibleCategory l
        (Coefficient.{u} l (PadicAlgCl l) E) X) (1 : ℤ)).obj _
    rw [(sfRationalTriangulationDatum l (Coefficient.{u} l (PadicAlgCl l) E)
      X).choose_spec.choose_spec.1]
    rfl
  have qobj' (K) : Q'.obj (K⟦(1 : ℤ)⟧) = (Q'.obj K)⟦(1 : ℤ)⟧ := by
    change (sfRationalConstructibleLocalization l
      (Coefficient.{u} l (PadicAlgCl l) L) X).obj (K⟦(1 : ℤ)⟧) =
      (shiftFunctor (sfRationalConstructibleCategory l
        (Coefficient.{u} l (PadicAlgCl l) L) X) (1 : ℤ)).obj _
    rw [(sfRationalTriangulationDatum l (Coefficient.{u} l (PadicAlgCl l) L)
      X).choose_spec.choose_spec.1]
    rfl
  have nQ (K) : HEq ((Q.commShiftIso (1 : ℤ)).hom.app K)
      (𝟙 (Q.obj (K⟦(1 : ℤ)⟧))) :=
    integralLocalization_shift_hom l X (Coefficient.{u} l (PadicAlgCl l) E) K
  have nQ' (K) : HEq ((Q'.commShiftIso (1 : ℤ)).hom.app K)
      (𝟙 (Q'.obj (K⟦(1 : ℤ)⟧))) :=
    integralLocalization_shift_hom l X (Coefficient.{u} l (PadicAlgCl l) L) K
  have nF (K) : HEq ((F.commShiftIso (1 : ℤ)).hom.app (Q.obj K))
      (Q'.map ((T.commShiftIso (1 : ℤ)).hom.app K)) := by
    exact (GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
      l (PadicAlgCl l) X E L h).exists.choose_spec (Q.obj K)
  exact localized_comparison_core Q Q' T F (fun K ↦ hobj K) c hc
    qobj qobj' nQ nQ' nF

instance rationalIntegralTransitionRaw_shift {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    NatTrans.CommShift (rationalIntegralTransitionRaw l X h).hom ℤ :=
  commShift_of_one _ (rationalIntegralTransitionRaw_shift_one l X h)

private theorem eqIso_commShift
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (F G : A ⥤ B) (h : F = G) (s : G.CommShift ℤ) :
    letI := s
    letI : F.CommShift ℤ := cast (congrArg (fun H ↦ H.CommShift ℤ) h.symm) s
    NatTrans.CommShift (eqToIso h).hom ℤ := by
  cases h
  dsimp
  change NatTrans.CommShift (𝟙 F) ℤ
  infer_instance

/-- The stage system uses the stated scalar functor with its transported shift.
Source: blueprint order 1462 (blueprint: lem-sf-native-integral-rational-scalar-comparison). -/
def rationalStageTransport {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ≅
      GeneralAlgebraicallyClosedCoefficients.transition l (PadicAlgCl l) X E L h :=
  eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l (PadicAlgCl l) X).exists.choose_spec.1 E L h)

instance rationalStageTransport_shift {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    NatTrans.CommShift (rationalStageTransport l X h).hom ℤ :=
  eqIso_commShift _ _ _ (GeneralAlgebraicallyClosedCoefficients.transitionCommShift
    l (PadicAlgCl l) X E L h)

/-- Integral scalar extension followed by rationalization agrees with stage extension.
Source: blueprint order 1828 (blueprint: lem-sf-native-integral-rational-scalar-comparison). -/
def rationalIntegralTransition {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    stageLocalization l X E ⋙
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X E L h ⋙
        stageLocalization l X L :=
  Functor.isoWhiskerLeft _ (rationalStageTransport l X h) ≪≫
    rationalIntegralTransitionRaw l X h

instance rationalIntegralTransition_shift {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    NatTrans.CommShift (rationalIntegralTransition l X h).hom ℤ := by
  dsimp only [rationalIntegralTransition, Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

/-- Equality of objects underlying the integral-image comparison.
Source: blueprint order 1828 (blueprint: lem-sf-native-integral-rational-scalar-comparison). -/
theorem rationalIntegralTransition_obj {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
        ((stageLocalization l X E).obj K) =
      (stageLocalization l X L).obj
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition
          l (PadicAlgCl l) X E L h).obj K) := by
  rw [(GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l (PadicAlgCl l) X).exists.choose_spec.1 E L h]
  exact sfRationalScalarExtension_obj l (Coefficient.{u} l (PadicAlgCl l) E) X
    0 (Fact.out : l.Prime).ne_zero (Coefficient.{u} l (PadicAlgCl l) L)
    (coefficientInclusion l (PadicAlgCl l) E L h) _

private theorem eqToHom_app_comp
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (e : F = G) (P : A) {Q : B} (h : G.obj P = Q) (k : F.obj P = Q) :
    (eqToIso e).hom.app P ≫ eqToHom h = eqToHom k := by
  cases e
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, eqToHom_refl, Category.id_comp]

/-- The comparison is just the literal object transport, not a fresh automorphism.
Source: blueprint order 1828 (blueprint: lem-sf-native-integral-rational-scalar-comparison). -/
theorem rationalIntegralTransition_hom {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (rationalIntegralTransition l X h).hom.app K =
      eqToHom (rationalIntegralTransition_obj l X h K) := by
  dsimp only [rationalIntegralTransition, rationalStageTransport,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  have hc : (rationalIntegralTransitionRaw l X h).hom.app K =
      eqToHom (rationalIntegralTransitionRaw_obj l X h K) := by rfl
  rw [hc]
  exact eqToHom_app_comp _ _ _ _

/-- The inverse comparison also carries only the literal object transport.
Source: blueprint order 1828 (blueprint: lem-sf-native-integral-rational-scalar-comparison). -/
theorem rationalIntegralTransition_inv {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (rationalIntegralTransition l X h).inv.app K =
      eqToHom (rationalIntegralTransition_obj l X h K).symm := by
  have he : (rationalIntegralTransition l X h).app K =
      eqToIso (rationalIntegralTransition_obj l X h K) :=
    Iso.ext (rationalIntegralTransition_hom l X h K)
  exact congrArg Iso.inv he

private theorem isoApp_heq
    {A B : Type*} [Category A] [Category B]
    {F G F' G' : A ⥤ B} (hF : F = F') (hG : G = G')
    (a : F ≅ G) (b : F' ≅ G') (h : HEq a b) (K : A) :
    HEq (a.hom.app K) (b.hom.app K) := by
  cases hF
  cases hG
  cases h
  rfl

private theorem normalizedStageAssociator_heq
    (S : StageSystem (GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X))
    (hS : ∀ E L (h : E ≤ L), S.T h =
      GeneralAlgebraicallyClosedCoefficients.transition l (PadicAlgCl l) X E L h)
    (hA : ∀ E L M (h : E ≤ L) (k : L ≤ M), HEq (S.assoc h k)
      (GeneralAlgebraicallyClosedCoefficients.associator l (PadicAlgCl l) X E L M h k))
    {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    HEq ((S.assoc h k).hom.app ((stageLocalization l X E).obj K))
      ((stageLocalization l X M).map
        ((integralTensorAssociator l X (PadicAlgCl l) h k).hom.app K)) := by
  have hcomp : HEq
      ((S.assoc h k).hom.app ((stageLocalization l X E).obj K))
      ((GeneralAlgebraicallyClosedCoefficients.associator l (PadicAlgCl l) X
        E L M h k).hom.app ((stageLocalization l X E).obj K)) := isoApp_heq
    (congrArg₂ (fun F G ↦ F ⋙ G) (hS E L h) (hS L M k))
    (hS E M (h.trans k)) _ _ (hA E L M h k)
    ((stageLocalization l X E).obj K)
  have hx : HEq
      ((GeneralAlgebraicallyClosedCoefficients.associator l (PadicAlgCl l) X
        E L M h k).hom.app ((stageLocalization l X E).obj K))
      ((stageLocalization l X M).map
        ((integralTensorAssociator l X (PadicAlgCl l) h k).hom.app K)) := by
    rw [stageLocalization_eq, stageLocalization_eq]
    exact integralAssociator_image l X (PadicAlgCl l) E L M h k K
  exact hcomp.trans hx

/-- The selected stage-system associator is the localized integral tensor associator.
Source: blueprint orders 1462 and 1828
(blueprint: lem-sf-native-integral-rational-scalar-comparison). -/
theorem rationalIntegralAssociator_heq {E L M : Index l (PadicAlgCl l)}
    (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    HEq
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).assoc h k).hom.app
          ((stageLocalization l X E).obj K))
      ((stageLocalization l X M).map
        ((integralTensorAssociator l X (PadicAlgCl l) h k).hom.app K)) := by
  have hs := (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l (PadicAlgCl l) X).exists.choose_spec
  exact normalizedStageAssociator_heq l X _ hs.1 hs.2 h k K

/-- Compatibility of the integral-image comparisons with the literal associators.
Source: blueprint order 1828 (blueprint: lem-sf-native-integral-rational-scalar-comparison). -/
theorem rationalIntegralTransition_tower {E L M : Index l (PadicAlgCl l)}
    (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T k).map
        ((rationalIntegralTransition l X h).hom.app K) ≫
      (rationalIntegralTransition l X k).hom.app
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition
          l (PadicAlgCl l) X E L h).obj K) ≫
      (stageLocalization l X M).map
        ((integralTensorAssociator l X (PadicAlgCl l) h k).hom.app K) =
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).assoc h k).hom.app
          ((stageLocalization l X E).obj K) ≫
      (rationalIntegralTransition l X (h.trans k)).hom.app K := by
  with_unfolding_all simp only [rationalIntegralTransition_hom, eqToHom_map]
  apply eq_of_heq
  exact ((eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _)).trans
    ((rationalIntegralAssociator_heq l X h k K).symm.trans
      (comp_eqToHom_heq _ _).symm)

end WeilConjectures.LocallyFiniteAdicRealization
