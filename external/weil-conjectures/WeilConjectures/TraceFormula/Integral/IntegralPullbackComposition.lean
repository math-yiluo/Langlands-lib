/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
import WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence
import WeilConjectures.PoincareDuality.Integral.IntegralSystemPullbackLiftAssociativity

/-!
# Composition of completed integral derived pullbacks

Source: Stacks Project, Tags 099N(2),(5) and 0D6D; Bhatt--Scholze,
Lemmas 3.5.5 and 3.5.7
(blueprint: lem-pod-integral-pullback-composition).

All categories use modules over the completed integral coefficient sheaf. The
positive exponent is n+1. The reduction comparison is the actual projection-adjoint
map, expressed in the published finite ring-sheaf presentation. Quantification over
all good representatives makes the reduction clause independent of choices.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical reduction rho of integral pullback, computed using any good resolution.
The first factor is the actual projection-adjoint map, whose invertibility is precisely
part (1) of integralOperations_preserve_constructible. The other factors only change
finite pullback presentation and identify the reduction of the representative with
that of K through the universal reduction counit.
Source: Stacks Tag 099N(5); Bhatt--Scholze, Lemma 6.5.9(5)
(blueprint: lem-pod-integral-pullback-composition). -/
def integralPullbackReductionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj
        ((constructibleIntegralPullback l E f).obj K).obj ≅
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f).obj
        ((scalarReductionDerivedExtension l E Y n).obj K.obj) :=
  integralSystemPullbackReductionIso l E f K P e n

private theorem reductionIso_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ) :
    integralPullbackReductionIso l E f K P e n =
      integralSystemPullbackReductionIso l E f K P e n := rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- A family of composition comparisons on the actual full constructible categories.
The type includes every composable pair of morphisms of schemes with l invertible.
Source: Stacks Tags 099N and 0D6D
(blueprint: lem-pod-integral-pullback-composition). -/
abbrev IntegralPullbackCompositionFamily :=
  ∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V),
    constructibleIntegralPullback l E (h ≫ k) ≅
      constructibleIntegralPullback l E k ⋙ constructibleIntegralPullback l E h

private theorem cancelRight_hom_app
    {C D T : Type*} [Category C] [Category D] [Category T]
    (R : D ⥤ T) [R.Full] [R.Faithful] {F G : C ⥤ D} {H : C ⥤ T}
    (a : F ⋙ R ≅ H) (b : G ⋙ R ≅ H) (K : C) :
    R.map ((Functor.fullyFaithfulCancelRight R (a ≪≫ b.symm)).hom.app K) ≫
        b.hom.app K = a.hom.app K := by
  simp [Category.assoc]

private theorem cancelRightData
    {C D T : Type*} [Category C] [Category D] [Category T]
    (R : D ⥤ T) [R.Full] [R.Faithful] {F G : C ⥤ D} {H : C ⥤ T}
    (a : F ⋙ R ≅ H) (b : G ⋙ R ≅ H) :
    ∃ c : F ≅ G, ∀ K, R.map (c.hom.app K) ≫ b.hom.app K = a.hom.app K := by
  exact ⟨Functor.fullyFaithfulCancelRight R (a ≪≫ b.symm), cancelRight_hom_app R a b⟩

private theorem liftCompositionData
    {C B D S T V : Type*}
    [Category C] [Category B] [Category D] [Category S] [Category T] [Category V]
    (R : D ⥤ S) [R.Full] [R.Faithful] (RB : B ⥤ T) (RC : C ⥤ V)
    (F : C ⥤ D) (G : C ⥤ B) (H : B ⥤ D)
    (U : T ⥤ S) (W : V ⥤ T) (J : V ⥤ S)
    (bF : F ⋙ R ≅ RC ⋙ J) (bG : G ⋙ RB ≅ RC ⋙ W)
    (bH : H ⋙ R ≅ RB ⋙ U) (a : J ≅ W ⋙ U) :
    ∃ c : F ≅ G ⋙ H, ∀ K,
      R.map (c.hom.app K) ≫ bH.hom.app (G.obj K) ≫ U.map (bG.hom.app K) =
        bF.hom.app K ≫ a.hom.app (RC.obj K) := by
  obtain ⟨c, hc⟩ := cancelRightData (C := C) (D := D) (T := S)
    (F := F) (G := G ⋙ H) (H := RC ⋙ W ⋙ U) R
    (bF ≪≫ isoWhiskerLeft RC a)
    (Functor.associator G H R ≪≫ isoWhiskerLeft G bH ≪≫
      (Functor.associator G RB U).symm ≪≫ isoWhiskerRight bG U ≪≫
        Functor.associator RC W U)
  refine ⟨c, ?_⟩
  intro K
  simpa only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using hc K

private theorem reduction_paste
    {B C D : Type*} [Category B] [Category C] [Category D]
    (H : C ⥤ D) (G : B ⥤ C) (J : B ⥤ D)
    {A₀ A₁ B₀ B₁ T₀ T₂ T₃ : D} {C₀ C₁ T₁ : C} {D₀ D₁ : B}
    (x : A₀ ⟶ B₀) (y : A₁ ⟶ B₁) (s : A₀ ≅ A₁) (t : B₀ ≅ B₁)
    (e : C₀ ≅ C₁) (d : D₀ ≅ D₁)
    (bh : B₀ ⟶ T₀) (bk : C₀ ⟶ T₁) (bj : A₀ ⟶ T₂)
    (qh : T₀ ⟶ H.obj C₀) (qk : T₁ ⟶ G.obj D₀) (qj : T₂ ⟶ J.obj D₀)
    (w : T₀ ⟶ T₃) (qt : T₃ ⟶ H.obj T₁) (a : T₂ ⟶ T₃)
    (a₀ : J.obj D₀ ⟶ H.obj (G.obj D₀)) (a₁ : J.obj D₁ ⟶ H.obj (G.obj D₁))
    (rh : B₁ ⟶ H.obj C₁) (rk : C₁ ⟶ G.obj D₁) (rj : A₁ ⟶ J.obj D₁)
    (hmap : x ≫ t.hom = s.hom ≫ y)
    (hbh : bh ≫ qh ≫ H.map e.hom = t.hom ≫ rh)
    (hbk : bk ≫ qk ≫ G.map d.hom = e.hom ≫ rk)
    (hbj : bj ≫ qj ≫ J.map d.hom = s.hom ≫ rj)
    (hw : w ≫ qt = qh ≫ H.map bk)
    (hc : x ≫ bh ≫ w = bj ≫ a)
    (hf : a ≫ qt ≫ H.map qk = qj ≫ a₀)
    (ha : a₀ ≫ H.map (G.map d.hom) = J.map d.hom ≫ a₁) :
    y ≫ rh ≫ H.map rk = rj ≫ a₁ := by
  apply (cancel_epi s.hom).1
  have hbk' := congrArg H.map hbk
  simp only [Functor.map_comp] at hbk'
  calc
    s.hom ≫ (y ≫ rh ≫ H.map rk) = x ≫ t.hom ≫ rh ≫ H.map rk := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ rh ≫ H.map rk) hmap.symm
    _ = x ≫ bh ≫ qh ≫ H.map e.hom ≫ H.map rk := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ x ≫ z ≫ H.map rk) hbh.symm
    _ = x ≫ bh ≫ qh ≫ H.map bk ≫ H.map qk ≫ H.map (G.map d.hom) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ x ≫ bh ≫ qh ≫ z) hbk'.symm
    _ = x ≫ bh ≫ w ≫ qt ≫ H.map qk ≫ H.map (G.map d.hom) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ x ≫ bh ≫ z ≫ H.map qk ≫ H.map (G.map d.hom)) hw.symm
    _ = bj ≫ a ≫ qt ≫ H.map qk ≫ H.map (G.map d.hom) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ qt ≫ H.map qk ≫ H.map (G.map d.hom)) hc
    _ = bj ≫ qj ≫ a₀ ≫ H.map (G.map d.hom) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ bj ≫ z ≫ H.map (G.map d.hom)) hf
    _ = bj ≫ qj ≫ J.map d.hom ≫ a₁ := by
      simpa only [Category.assoc] using congrArg (fun z ↦ bj ≫ qj ≫ z) ha
    _ = s.hom ≫ (rj ≫ a₁) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ a₁) hbj

private theorem comparison_naturality
    {B C D : Type*} [Category B] [Category C] [Category D]
    (H : C ⥤ D) (G : B ⥤ C) (J : B ⥤ D) (a : J ⟶ G ⋙ H)
    {X Y : B} (f : X ⟶ Y) :
    a.app X ≫ H.map (G.map f) = J.map f ≫ a.app Y :=
  (a.naturality f).symm

private theorem integralFiniteCanonicalPullbackComposition_hom
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (n : ℕ) :
    (integralFiniteCanonicalPullbackComposition l E h k n).hom =
      (proEtaleConstantRingPullbackComposition h k
        (Padic.coefficientExtensionRing l E (n + 1))).inv := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] finiteSystemDerivedPullback finiteSystemDerivedEvaluation
  integralSystemReduction integralSystemReductionEvaluation
  finiteSystemDerivedComposition finiteSystemDerivedPullbackEvaluation
  constructibleIntegralPullback integralDerivedPullback
  integralFiniteCanonicalPullbackComposition proEtaleConstantRingPullbackComposition
  integralSystemPullbackReductionIso integralPullbackReductionIso
  AlgebraicGeometry.Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted
  proEtaleConstantRingDerivedPullback scalarReductionDerivedExtension

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
-- The natural isomorphisms compare two presentations of derived coefficient systems.

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Integral pullback has natural composition isomorphisms, with their specified
finite reductions, associative composition law and whole-system normalization.

Source: Stacks Tags 099N(2),(5), 0D6D, 0941; Bhatt--Scholze, Lemmas 3.5.5 and 3.5.7
(blueprint: lem-pod-integral-pullback-composition).

Proof:
1. Use the reduction/total-limit adjunction of lem-coef-derived-system-evaluation-calculus
on strict varying-coefficient systems. Exact finite inverse image is supplied by
prop-weil-pbc-proetale-constant-exact; the simultaneous system model is
lem-coef-semilinear-derived-sections. Reductions of one flat-term K-flat resolution
remain K-flat (lem-pur-kflat-change-of-rings). Quotient tensor comparisons multiply
coefficients and obey the cocycle. Pullback preserves these comparisons by
lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The integral construction and
lem-pur-integral-operations-well-defined identify its functor with total limit after
finite inverse image and reduction. Exact countable products and the natural Roos
triangle (lem-weil-proetale-countable-products-exact and
lem-weil-pbc-ringed-strict-tower-homotopy-limit) make this an identification on maps.
2. The system-adjunction counit gives beta_f: R F_f -> U_f R. Its evaluations are
the adjoints of the actual tower projections, hence the specified rho maps.
lemma-sp-tower-adjunction-foundation--2 makes beta invertible on normalized systems.
lem-pur-integral-operations-preserve-constructible types every pullback value in
D^b_c. The triangle identity makes the adjunction unit eta invertible on these
values, giving full faithfulness of reduction on the objects used below.
3. Apply lem-weil-pbc-proetale-derived-pullback-composition on each finite quotient.
Its termwise tensor reassociation commutes with quotient maps, so it gives a coherent
system isomorphism a_hk. With B = U_h(beta_k) beta_h, set delta = B^{-1} a_hk beta_hk.
Lift delta by eta_target^{-1} L(delta) eta_source. All factors are invertible and
natural, giving c on the actual integral functors and their full subcategories.
4. Evaluate B R(c) = a_hk beta_hk at every positive exponent. This is exactly the
reduction equation below, after the canonical representative comparisons defining
integralPullbackReductionIso. No subsequence of exponents or unramifiedness is used.
5. Reduce both triple composites and identify their common target with U_j U_h U_k R.
Naturality of beta and the equation in step 4 give respectively
U_j(a_hk) a_j,hk beta_hkj and a_jh(U_k R) a_hj,k beta_hkj. Before localization both
finite composites are the same tensor reassociation: their forward maps insert
units, and their inverses multiply the three transported scalar factors. These
formulas commute with all quotient transitions. The simultaneous system model
therefore gives equality of system maps. Cancel the common invertible comparison
and use full faithfulness from step 2 to obtain the integral associativity equation.
The explicit eqToHom below only identifies the two parenthesizations of j >> h >> k.
The last clause records the whole-system normalization of c used in step 3: its
reduction composed with the system comparisons beta is the system compositor
after beta_hk, before any finite evaluation. -/
theorem integralPullbackComposition :
    ∃ c : IntegralPullbackCompositionFamily l E,
      (∀ {V W Z : Scheme.{u}}
        [∀ v : V, Invertible (l : V.residueField v)]
        [∀ w : W, Invertible (l : W.residueField w)]
        [∀ z : Z, Invertible (l : Z.residueField z)]
        (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V)
        (P : (integralOperationsGoodComplex l E V).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
        (Q : (integralOperationsGoodComplex l E W).FullSubcategory)
        (d : DerivedCategory.Q.obj Q.obj ≅ ((constructibleIntegralPullback l E k).obj K).obj)
        (n : ℕ),
        (scalarReductionDerivedExtension l E Z n).map ((c h k).hom.app K).hom ≫
            (integralPullbackReductionIso l E h
              ((constructibleIntegralPullback l E k).obj K) Q d n).hom ≫
            (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing l E (n + 1)) h).map
                (integralPullbackReductionIso l E k K P e n).hom =
          (integralPullbackReductionIso l E (h ≫ k) K P e n).hom ≫
            (integralFiniteCanonicalPullbackComposition l E h k n).hom.app
              ((scalarReductionDerivedExtension l E V n).obj K.obj)) ∧
      (∀ {V W Z Y : Scheme.{u}}
        [∀ v : V, Invertible (l : V.residueField v)]
        [∀ w : W, Invertible (l : W.residueField w)]
        [∀ z : Z, Invertible (l : Z.residueField z)]
        [∀ y : Y, Invertible (l : Y.residueField y)]
        (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V)
        (K : sfIntegralConstructibleCategory l E V),
        (c j (h ≫ k)).hom.app K ≫
            (constructibleIntegralPullback l E j).map ((c h k).hom.app K) =
          eqToHom (congrArg
            (fun f : Y ⟶ V ↦ (constructibleIntegralPullback l E f).obj K)
            (Category.assoc j h k).symm) ≫
            (c (j ≫ h) k).hom.app K ≫
              (c j h).hom.app ((constructibleIntegralPullback l E k).obj K)) ∧
      (∀ {V W Z : Scheme.{u}}
        [∀ v : V, Invertible (l : V.residueField v)]
        [∀ w : W, Invertible (l : W.residueField w)]
        [∀ z : Z, Invertible (l : Z.residueField z)]
        (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V),
        (integralSystemReduction l E Z).map ((c h k).hom.app K) ≫
            ((integralPullbackSystemComparison l E).choose h).hom.app
              ((constructibleIntegralPullback l E k).obj K) ≫
            (finiteSystemDerivedPullback (integralSystemRings l E)
              (integralSystemTransition l E) h).map
                (((integralPullbackSystemComparison l E).choose k).hom.app K) =
          ((integralPullbackSystemComparison l E).choose (h ≫ k)).hom.app K ≫
            (finiteSystemDerivedComposition (integralSystemRings l E)
              (integralSystemTransition l E) h k).hom.app
                ((integralSystemReduction l E V).obj K)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  first
  |
    classical
    let hfull (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
        ((integralSystemReduction l E) X).Full :=
      (integralSystemReduction_fullyFaithful l E X).1
    let hfaithful (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
        ((integralSystemReduction l E) X).Faithful :=
      (integralSystemReduction_fullyFaithful l E X).2
    let β : ∀ {X Y : Scheme.{u}}
        [∀ x : X, Invertible (l : X.residueField x)]
        [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y),
        constructibleIntegralPullback l E f ⋙ integralSystemReduction l E X ≅
          integralSystemReduction l E Y ⋙
            finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E) f
              :=
      (integralPullbackSystemComparison l E).choose
    have hβ := @(integralPullbackSystemComparison l E).choose_spec.1
    have hb {X Y : Scheme.{u}}
        [hX : ∀ x : X, Invertible (l : X.residueField x)]
        [hY : ∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
        (K : sfIntegralConstructibleCategory l E Y)
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (e : (DerivedCategory.Q (C := scalarReductionSource l E Y)).obj P.obj ≅ K.obj) (n : ℕ) :
        (finiteSystemDerivedEvaluation (integralSystemRings l E) (integralSystemTransition l E) X
            n).map ((β f).hom.app K) ≫
            (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
                (integralSystemTransition l E) f n).hom.app (((integralSystemReduction l E) Y).obj
                K) ≫
            (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing l E (n + 1)) f).map
              ((integralSystemReductionEvaluation l E Y n).hom.app K) =
          (integralSystemReductionEvaluation l E X n).hom.app
              ((constructibleIntegralPullback l E f).obj K) ≫
            (integralPullbackReductionIso l E f K P e n).hom := by
      exact (@hβ X Y hX hY f K P e n).trans
        (congrArg (fun i ↦ (integralSystemReductionEvaluation l E X n).hom.app
          ((constructibleIntegralPullback l E f).obj K) ≫ i.hom)
          (reductionIso_eq l E f K P e n).symm)
    have cdata {V W Z : Scheme.{u}}
        [hV : ∀ v : V, Invertible (l : V.residueField v)]
        [hW : ∀ w : W, Invertible (l : W.residueField w)]
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
        (h : Z ⟶ W) (k : W ⟶ V) :=
      letI : ((integralSystemReduction l E) Z).Full := hfull Z
      letI : ((integralSystemReduction l E) Z).Faithful := hfaithful Z
      liftCompositionData
        (C := sfIntegralConstructibleCategory l E V)
        (B := sfIntegralConstructibleCategory l E W)
        (D := sfIntegralConstructibleCategory l E Z)
        (S := finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) Z) (T :=
            finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) W)
        (V := finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) V)
            ((integralSystemReduction l E) Z) ((integralSystemReduction l E) W)
            ((integralSystemReduction l E) V)
        (constructibleIntegralPullback l E (h ≫ k))
        (constructibleIntegralPullback l E k) (constructibleIntegralPullback l E h)
        ((finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E)) h)
            ((finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E))
            k) ((finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l
            E)) (h ≫ k)) (@β Z V hZ hV (h ≫ k)) (@β W V hW hV k) (@β Z W hZ hW h)
        (finiteSystemDerivedComposition (integralSystemRings l E) (integralSystemTransition l E) h
          k)
    choose c₀ hc using @cdata
    refine ⟨c₀, ?_, ?_, hc⟩
    · intro V W Z hV hW hZ h k K P e Q d n
      let ev := finiteSystemDerivedEvaluation (integralSystemRings l E) (integralSystemTransition l
          E) Z n
      let H := proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) h
      let G := proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) k
      let J := proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) (h ≫ k)
      let x := ev.map (((integralSystemReduction l E) Z).map ((c₀ h k).hom.app K))
      let y := ((scalarReductionDerivedExtension l E Z n).map ((c₀ h k).hom.app K).hom)
      let s := ((integralSystemReductionEvaluation l E Z n).app
          ((constructibleIntegralPullback l E (h ≫ k)).obj K))
      let t := ((integralSystemReductionEvaluation l E Z n).app
          ((constructibleIntegralPullback l E h).obj ((constructibleIntegralPullback l E k).obj K)))
      let e₀ := ((integralSystemReductionEvaluation l E W n).app
          ((constructibleIntegralPullback l E k).obj K))
      let d₀ := ((integralSystemReductionEvaluation l E V n).app K)
      let bh := (ev.map ((β h).hom.app ((constructibleIntegralPullback l E k).obj K)))
      let bk := ((finiteSystemDerivedEvaluation (integralSystemRings l E) (integralSystemTransition
          l E) W n).map ((β k).hom.app K))
      let bj := (ev.map ((β (h ≫ k)).hom.app K))
      let qh := ((finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) h n).hom.app
          (((integralSystemReduction l E) W).obj ((constructibleIntegralPullback l E k).obj K)))
      let qk := ((finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) k n).hom.app (((integralSystemReduction l E) V).obj K))
      let qj := ((finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) (h ≫ k) n).hom.app (((integralSystemReduction l E) V).obj
          K))
      let w := (ev.map (((finiteSystemDerivedPullback (integralSystemRings l E)
          (integralSystemTransition l E)) h).map ((β k).hom.app K)))
      let qt := ((finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) h n).hom.app (((finiteSystemDerivedPullback
          (integralSystemRings l E) (integralSystemTransition l E)) k).obj
          (((integralSystemReduction l E) V).obj K)))
      let a₀ := (ev.map ((finiteSystemDerivedComposition (integralSystemRings l E)
          (integralSystemTransition l E) h k).hom.app (((integralSystemReduction l E) V).obj K)))
      let a₁ := ((integralFiniteCanonicalPullbackComposition l E h k n).hom.app
          ((finiteSystemDerivedEvaluation (integralSystemRings l E) (integralSystemTransition l E) V
              n).obj (((integralSystemReduction l E) V).obj K)))
      let a₂ := ((integralFiniteCanonicalPullbackComposition l E h k n).hom.app
          ((scalarReductionDerivedExtension l E V n).obj K.obj))
      let rh := (integralPullbackReductionIso l E h ((constructibleIntegralPullback l E k).obj K) Q
          d n).hom
      let rk := (integralPullbackReductionIso l E k K P e n).hom
      let rj := (integralPullbackReductionIso l E (h ≫ k) K P e n).hom
      refine reduction_paste H G J x y s t e₀ d₀ bh bk bj qh qk qj w qt a₀ a₁ a₂ rh rk rj
        ?_ (hb h ((constructibleIntegralPullback l E k).obj K) Q d n)
        (hb k K P e n) (hb (h ≫ k) K P e n) ?_ ?_ ?_ ?_
      · exact (integralSystemReductionEvaluation l E Z n).hom.naturality ((c₀ h k).hom.app K)
      · exact (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) h n).hom.naturality
          ((β k).hom.app K)
      · simpa only [Functor.map_comp] using congrArg ev.map (hc h k K)
      · have hf := (@finiteSystemPullbackCoherence.{u} (integralSystemRings l E)
            (integralSystemTransition l E) (fun n ↦ integralSystemRings_finite l E n)
            Z Z W V (𝟙 Z) h k).2.1 ((integralSystemReduction l E V).obj K) n
        exact hf.trans (congrArg
          (fun a : J ⟶ G ⋙ H ↦ qj ≫ a.app
            ((finiteSystemDerivedEvaluation (integralSystemRings l E)
              (integralSystemTransition l E) V n).obj ((integralSystemReduction l E V).obj K)))
          (integralFiniteCanonicalPullbackComposition_hom l E h k n).symm)
      · exact @comparison_naturality
          (DerivedCategory (scalarReductionTarget l E V n))
          (DerivedCategory (scalarReductionTarget l E W n))
          (DerivedCategory (scalarReductionTarget l E Z n))
          _ _ _ H G J (integralFiniteCanonicalPullbackComposition l E h k n).hom
          ((finiteSystemDerivedEvaluation (integralSystemRings l E)
            (integralSystemTransition l E) V n).obj ((integralSystemReduction l E V).obj K))
          ((scalarReductionDerivedExtension l E V n).obj K.obj) d₀.hom
    · exact integralSystemPullbackLift_associativity l E β c₀ hc

end WeilConjectures
