/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralPullbackCompositionScalar
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence

/-! # Rational scalar extension carries the rational pullback compositor

Source: Stacks Project, Tags 06YY, 07A4, 0941 and 0D6D; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-composition-scalar).

For a coefficient inclusion E to L, completed scalar extension carries the specified
integral composition comparison at E to the one at L, conjugated by the canonical
scalar/pullback comparisons. Both sides are compared after the fully faithful coherent
reduction at L: the system-level composition clause of integralPullbackComposition at
E and at L, the system scalar comparison, the pullback/scalar square of
scalarExtensionTowerCoherence, and whole-system mixed coherence.
The rationalized statement follows by localization on pure tensors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section RationalScalar

/-- The fixed-stage rational composition comparison at an arbitrary rational object: the
localized specified integral compositor between the prescribed integral objects.
Source: Stacks 099N(5) (blueprint: lem-pod-integral-pullback-composition-scalar).
Construction: conjugate the localized integral compositor by the defining object equalities. -/
def rationalPullbackCompositionIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (Q : sfRationalConstructibleCategory l E Z) :
    (rationalDerivedPullback l E (f ≫ g)).obj Q ≅
      (rationalDerivedPullback l E f).obj ((rationalDerivedPullback l E g).obj Q) :=
  eqToIso ((rationalDerivedPullback_existsUnique l E (f ≫ g)).exists.choose_spec.2.1 Q) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (((integralPullbackComposition l E).choose f g).app Q.obj) ≪≫
    (eqToIso ((congrArg (rationalDerivedPullback l E f).obj
      ((rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 Q)).trans
      ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1
        ((sfRationalConstructibleLocalization l E Y).obj
          ((constructibleIntegralPullback l E g).obj Q.obj))))).symm

/-- The rational compositor is the localized integral compositor up to object equalities.
Source: Stacks 099N(5) (blueprint: lem-pod-integral-pullback-composition-scalar).
Proof: the defining eqToHom conjugation. -/
theorem rationalPullbackCompositionIso_heq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (Q : sfRationalConstructibleCategory l E Z) :
    HEq (rationalPullbackCompositionIso l E f g Q).hom
      ((sfRationalConstructibleLocalization l E X).map
        (((integralPullbackComposition l E).choose f g).hom.app Q.obj)) :=
  (conj_eqToHom_iff_heq _ _
    ((rationalDerivedPullback_existsUnique l E (f ≫ g)).exists.choose_spec.2.1 Q)
    ((congrArg (rationalDerivedPullback l E f).obj
      ((rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 Q)).trans
      ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1
        ((sfRationalConstructibleLocalization l E Y).obj
          ((constructibleIntegralPullback l E g).obj Q.obj))))).mp rfl

private theorem map_heq_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} (eA : A = A') (eB : B = B') {a : A ⟶ B} {b : A' ⟶ B'}
    (h : HEq a b) : HEq (F.map a) (F.map b) := by
  subst eA
  subst eB
  cases h
  rfl

private theorem heq_of_obj_eq {C D : Type*} [Category D] {F G : C → D}
    (φ : ∀ c, F c ⟶ G c) {c c' : C} (e : c = c') : HEq (φ c) (φ c') := by
  subst e
  rfl

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Rational scalar extension carries the fixed-stage rational compositor at E to the one
at L, conjugated by the rational scalar/pullback comparisons.
Source: Stacks 06YY, 07A4, 099N(5)
(blueprint: lem-pod-integral-pullback-composition-scalar).
Proof: every factor is the localization of the corresponding integral map, up to the
prescribed object equalities: scalar extension and pullback act on tensors with one by the
integral maps, and the rational scalar comparisons are localized integralPullbackScalarComparison.
Apply integralPullbackComposition_scalar and compose heterogeneous equalities. -/
theorem rationalPullbackComposition_scalar {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (Q : sfRationalConstructibleCategory l E Z) :
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        (rationalPullbackCompositionIso l E f g Q).hom ≫
      (rationalPullbackScalarComparison l E L ι f).hom.app
        ((rationalDerivedPullback l E g).obj Q) ≫
      (rationalDerivedPullback l L f).map
        ((rationalPullbackScalarComparison l E L ι g).hom.app Q) =
    (rationalPullbackScalarComparison l E L ι (f ≫ g)).hom.app Q ≫
      (rationalPullbackCompositionIso l L f g
        ((sfRationalScalarExtension l E Z 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
          L ι).obj Q)).hom := by
  let SR (A : Scheme.{u}) := sfRationalScalarExtension l E A 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let SI (A : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι A
  let locL (A : Scheme.{u}) := sfRationalConstructibleLocalization l L A
  have hPE {A B : Scheme.{u}} [∀ a : A, Invertible (l : A.residueField a)]
      [∀ b : B, Invertible (l : B.residueField b)] (p : A ⟶ B)
      (K : sfRationalConstructibleCategory l E B) :
      (rationalDerivedPullback l E p).obj K =
        ⟨(constructibleIntegralPullback l E p).obj K.obj⟩ :=
    (rationalDerivedPullback_existsUnique l E p).exists.choose_spec.2.1 K
  have hPL {A B : Scheme.{u}} [∀ a : A, Invertible (l : A.residueField a)]
      [∀ b : B, Invertible (l : B.residueField b)] (p : A ⟶ B)
      (K : sfRationalConstructibleCategory l L B) :
      (rationalDerivedPullback l L p).obj K =
        ⟨(constructibleIntegralPullback l L p).obj K.obj⟩ :=
    (rationalDerivedPullback_existsUnique l L p).exists.choose_spec.2.1 K
  have mPL {A B : Scheme.{u}} [∀ a : A, Invertible (l : A.residueField a)]
      [∀ b : B, Invertible (l : B.residueField b)] (p : A ⟶ B)
      (K M : sfIntegralConstructibleCategory l L B) (a : K ⟶ M) :
      HEq ((rationalDerivedPullback l L p).map ((locL B).map a))
        ((locL A).map ((constructibleIntegralPullback l L p).map a)) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    exact (rationalDerivedPullback_existsUnique l L p).exists.choose_spec.2.2 K M a 1
  have hSR (A : Scheme.{u}) (K : sfRationalConstructibleCategory l E A) :
      (SR A).obj K = ⟨(SI A).obj K.obj⟩ :=
    (sfRationalScalarExtension_existsUnique l E A 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 K
  have mSR (A : Scheme.{u}) (K M : sfIntegralConstructibleCategory l E A) (a : K ⟶ M) :
      HEq ((SR A).map ((sfRationalConstructibleLocalization l E A).map a))
        ((locL A).map ((SI A).map a)) := by
    have h := (sfRationalScalarExtension_existsUnique l E A 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2 K M a 1
    have h1 : (sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E 1)) =
        1 := by
      simp only [map_one]
    rw [h1] at h
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    exact h
  have sρ {A B : Scheme.{u}} [∀ a : A, Invertible (l : A.residueField a)]
      [∀ b : B, Invertible (l : B.residueField b)] (p : A ⟶ B)
      (K : sfRationalConstructibleCategory l E B) :
      HEq ((rationalPullbackScalarComparison l E L ι p).hom.app K)
        ((locL A).map (integralPullbackScalarComparison l E L ι p K.obj).hom) :=
    (rationalPullbackScalarComparison_existsUnique l E L ι p).exists.choose_spec K
  let K := Q.obj
  have hI := integralPullbackComposition_scalar l E L ι f g K
  -- the five factors
  have H1 : HEq ((SR X).map (rationalPullbackCompositionIso l E f g Q).hom)
      ((locL X).map ((SI X).map (((integralPullbackComposition l E).choose f g).hom.app K))) :=
    (map_heq_of_eq (SR X) (hPE (f ≫ g) Q)
      ((congrArg (rationalDerivedPullback l E f).obj (hPE g Q)).trans
        (hPE f ⟨(constructibleIntegralPullback l E g).obj Q.obj⟩))
      (rationalPullbackCompositionIso_heq l E f g Q)).trans (mSR X _ _ _)
  have H2 : HEq ((rationalPullbackScalarComparison l E L ι f).hom.app
        ((rationalDerivedPullback l E g).obj Q))
      ((locL X).map (integralPullbackScalarComparison l E L ι f
        ((constructibleIntegralPullback l E g).obj K)).hom) :=
    (sρ f _).trans (heq_of_obj_eq
      (fun T ↦ (locL X).map (integralPullbackScalarComparison l E L ι f T).hom)
      (congrArg ScalarLocalization.obj (hPE g Q)))
  have H3 : HEq ((rationalDerivedPullback l L f).map
        ((rationalPullbackScalarComparison l E L ι g).hom.app Q))
      ((locL X).map ((constructibleIntegralPullback l L f).map
        (integralPullbackScalarComparison l E L ι g K).hom)) :=
    (map_heq_of_eq (rationalDerivedPullback l L f)
      ((congrArg (SR Y).obj (hPE g Q)).trans (hSR Y _))
      ((hPL g ((SR Z).obj Q)).trans
        (congrArg (fun T : sfRationalConstructibleCategory l L Z ↦
          (⟨(constructibleIntegralPullback l L g).obj T.obj⟩ :
            sfRationalConstructibleCategory l L Y)) (hSR Z Q)))
      (sρ g Q)).trans (mPL f _ _ _)
  have H4 : HEq ((rationalPullbackScalarComparison l E L ι (f ≫ g)).hom.app Q)
      ((locL X).map (integralPullbackScalarComparison l E L ι (f ≫ g) K).hom) :=
    sρ (f ≫ g) Q
  have H5 : HEq (rationalPullbackCompositionIso l L f g ((SR Z).obj Q)).hom
      ((locL X).map (((integralPullbackComposition l L).choose f g).hom.app ((SI Z).obj K))) :=
    (rationalPullbackCompositionIso_heq l L f g ((SR Z).obj Q)).trans (heq_of_obj_eq
      (fun T ↦ (locL X).map (((integralPullbackComposition l L).choose f g).hom.app T))
      (congrArg ScalarLocalization.obj (hSR Z Q)))
  have e1 : (SR X).obj ((rationalDerivedPullback l E (f ≫ g)).obj Q) =
      (locL X).obj ((SI X).obj ((constructibleIntegralPullback l E (f ≫ g)).obj K)) :=
    (congrArg (SR X).obj (hPE (f ≫ g) Q)).trans (hSR X _)
  have e2 : (SR X).obj ((rationalDerivedPullback l E f).obj
        ((rationalDerivedPullback l E g).obj Q)) =
      (locL X).obj ((SI X).obj ((constructibleIntegralPullback l E f).obj
        ((constructibleIntegralPullback l E g).obj K))) :=
    (congrArg (SR X).obj ((congrArg (rationalDerivedPullback l E f).obj (hPE g Q)).trans
      (hPE f ⟨(constructibleIntegralPullback l E g).obj Q.obj⟩))).trans (hSR X _)
  have e3 : (rationalDerivedPullback l L f).obj ((rationalDerivedPullback l L g).obj
        ((SR Z).obj Q)) =
      (locL X).obj ((constructibleIntegralPullback l L f).obj
        ((constructibleIntegralPullback l L g).obj ((SI Z).obj K))) :=
    (congrArg (rationalDerivedPullback l L f).obj ((hPL g ((SR Z).obj Q)).trans
      (congrArg (fun T : sfRationalConstructibleCategory l L Z ↦
        (⟨(constructibleIntegralPullback l L g).obj T.obj⟩ :
          sfRationalConstructibleCategory l L Y)) (hSR Z Q)))).trans
      (hPL f ⟨(constructibleIntegralPullback l L g).obj ((SI Z).obj K)⟩)
  have e4 : (rationalDerivedPullback l L f).obj ((SR Y).obj
        ((rationalDerivedPullback l E g).obj Q)) =
      (locL X).obj ((constructibleIntegralPullback l L f).obj
        ((SI Y).obj ((constructibleIntegralPullback l E g).obj K))) :=
    (congrArg (rationalDerivedPullback l L f).obj
      ((congrArg (SR Y).obj (hPE g Q)).trans (hSR Y _))).trans
      (hPL f ⟨(SI Y).obj ((constructibleIntegralPullback l E g).obj K)⟩)
  have e5 : (rationalDerivedPullback l L (f ≫ g)).obj ((SR Z).obj Q) =
      (locL X).obj ((constructibleIntegralPullback l L (f ≫ g)).obj ((SI Z).obj K)) :=
    (hPL (f ≫ g) ((SR Z).obj Q)).trans
      (congrArg (fun T : sfRationalConstructibleCategory l L Z ↦
        (⟨(constructibleIntegralPullback l L (f ≫ g)).obj T.obj⟩ :
          sfRationalConstructibleCategory l L X)) (hSR Z Q))
  have hL := heq_comp e1 e2 e3 H1 (heq_comp e2 e4 e3 H2 H3)
  have hR := heq_comp e1 e5 e3 H4 H5
  have hM : (locL X).map ((SI X).map (((integralPullbackComposition l E).choose f g).hom.app K)) ≫
        (locL X).map (integralPullbackScalarComparison l E L ι f
          ((constructibleIntegralPullback l E g).obj K)).hom ≫
        (locL X).map ((constructibleIntegralPullback l L f).map
          (integralPullbackScalarComparison l E L ι g K).hom) =
      (locL X).map (integralPullbackScalarComparison l E L ι (f ≫ g) K).hom ≫
        (locL X).map (((integralPullbackComposition l L).choose f g).hom.app ((SI Z).obj K)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (locL X).map hI
  exact eq_of_heq (hL.trans ((heq_of_eq hM).trans hR.symm))

/-- Generic form of the transport of a compositor square through functors equal to the
scalar extensions. Source: elementary category theory. -/
private theorem compositor_transport
    {AX AY AZ BX BY BZ : Type*} [Category AX] [Category AY] [Category AZ]
    [Category BX] [Category BY] [Category BZ]
    (pEg : AZ ⥤ AY) (pEf : AY ⥤ AX) (pEfg : AZ ⥤ AX)
    (pLg : BZ ⥤ BY) (pLf : BY ⥤ BX) (pLfg : BZ ⥤ BX)
    (SX : AX ⥤ BX) (SY : AY ⥤ BY) (SZ : AZ ⥤ BZ)
    (TX : AX ⥤ BX) (TY : AY ⥤ BY) (TZ : AZ ⥤ BZ)
    (eX : TX = SX) (eY : TY = SY) (eZ : TZ = SZ)
    (ρf : pEf ⋙ SX ≅ SY ⋙ pLf) (ρg : pEg ⋙ SY ≅ SZ ⋙ pLg) (ρfg : pEfg ⋙ SX ≅ SZ ⋙ pLfg)
    (Q : AZ) (wE : pEfg.obj Q ≅ pEf.obj (pEg.obj Q))
    (wL : ∀ Q' : BZ, pLfg.obj Q' ≅ pLf.obj (pLg.obj Q'))
    (R : SX.map wE.hom ≫ ρf.hom.app (pEg.obj Q) ≫ pLf.map (ρg.hom.app Q) =
      ρfg.hom.app Q ≫ (wL (SZ.obj Q)).hom) :
    TX.map wE.hom =
      ((eqToIso eX).app (pEfg.obj Q) ≪≫ ρfg.app Q ≪≫
          pLfg.mapIso ((eqToIso eZ).app Q).symm).hom ≫
        (wL (TZ.obj Q)).hom ≫
        pLf.map ((eqToIso eY).app (pEg.obj Q) ≪≫ ρg.app Q ≪≫
            pLg.mapIso ((eqToIso eZ).app Q).symm).inv ≫
        ((eqToIso eX).app (pEf.obj (pEg.obj Q)) ≪≫ ρf.app (pEg.obj Q) ≪≫
          pLf.mapIso ((eqToIso eY).app (pEg.obj Q)).symm).inv := by
  subst eX eY eZ
  simp only [eqToIso_refl, Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Iso.refl_hom, Iso.refl_inv, Iso.symm_hom, Iso.symm_inv, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.mapIso_inv, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [Category.id_comp]
  rw [← reassoc_of% R]
  erw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]

/-- The rational compositor statement transported through arbitrary functors equal to the
rational scalar extensions, conjugated by the comparisons built from those equalities.
This is the form used for the recorded common-stage transitions.
Source: Stacks 06YY, 099N(5) (blueprint: lem-pod-integral-pullback-composition-scalar).
Proof: substitute the three equalities and rearrange rationalPullbackComposition_scalar. -/
theorem rationalPullbackComposition_scalar_transport {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (TX : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l L X)
    (TY : sfRationalConstructibleCategory l E Y ⥤ sfRationalConstructibleCategory l L Y)
    (TZ : sfRationalConstructibleCategory l E Z ⥤ sfRationalConstructibleCategory l L Z)
    (eX : TX = sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
    (eY : TY = sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
    (eZ : TZ = sfRationalScalarExtension l E Z 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
    (Q : sfRationalConstructibleCategory l E Z) :
    TX.map (rationalPullbackCompositionIso l E f g Q).hom =
      ((eqToIso eX).app ((rationalDerivedPullback l E (f ≫ g)).obj Q) ≪≫
          (rationalPullbackScalarComparison l E L ι (f ≫ g)).app Q ≪≫
          (rationalDerivedPullback l L (f ≫ g)).mapIso ((eqToIso eZ).app Q).symm).hom ≫
        (rationalPullbackCompositionIso l L f g (TZ.obj Q)).hom ≫
        (rationalDerivedPullback l L f).map
          ((eqToIso eY).app ((rationalDerivedPullback l E g).obj Q) ≪≫
            (rationalPullbackScalarComparison l E L ι g).app Q ≪≫
            (rationalDerivedPullback l L g).mapIso ((eqToIso eZ).app Q).symm).inv ≫
        ((eqToIso eX).app ((rationalDerivedPullback l E f).obj
            ((rationalDerivedPullback l E g).obj Q)) ≪≫
          (rationalPullbackScalarComparison l E L ι f).app
            ((rationalDerivedPullback l E g).obj Q) ≪≫
          (rationalDerivedPullback l L f).mapIso
            ((eqToIso eY).app ((rationalDerivedPullback l E g).obj Q)).symm).inv :=
  compositor_transport _ _ _ _ _ _ _ _ _ TX TY TZ eX eY eZ _ _ _ Q _
    (fun Q' ↦ rationalPullbackCompositionIso l L f g Q')
    (rationalPullbackComposition_scalar l E L ι f g Q)

end RationalScalar


end WeilConjectures
