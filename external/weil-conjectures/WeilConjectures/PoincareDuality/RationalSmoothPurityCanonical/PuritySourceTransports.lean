/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationNormalization
import WeilConjectures.SixFunctors.GeneratorReduction.FiniteTorOrdinaryTensorComplete
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Shift.Localization
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Canonical source transports for smooth purity

Source: main-20261015, prop-weil-operations.proof.md, sentences 3--4;
proposition-sp-rational, Steps 1--2, and thm-pur-adic-reconstruction
(blueprint: def-pur-canonical-purity-source-transports).

The source functors retain the actual localization, coefficient and shift
comparisons. Completed-to-ordinary tensor is fixed on strict Roos representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local irreducible] CategoryTheory.Functor.mapIso
  CategoryTheory.Iso.trans CategoryTheory.Iso.prod
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
  CategoryTheory.Functor.leftAdjoint
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
  Algebra.toModule CategoryTheory.HasSheafify.isRightAdjoint
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme MonoidalCategory
namespace WeilConjectures

namespace RationalSmoothPurityCanonical
attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  commonStageDerivedPullback commonStageDerivedTensor
  integralCompletedTensor integralCompletedTensorComparison sfRationalScalarExtension
/-- The actual rational twisted-pullback functor. The even shift is on the line;
canonical symmetry and shift constraints identify this with Lf*(-)(d)[2d].
Source: rational purity statement
(blueprint: def-pur-canonical-purity-source-transports). -/
def rationalSource (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :=
  ((Functor.const (sfRationalConstructibleCategory l E Y)).obj
      ((sfRationalTwistingCoefficient l E X (d : ℤ))⟦2 * (d : ℤ)⟧)).prod'
        (rationalDerivedPullback l E f) ⋙ rationalDerivedTensor l E X

private theorem integerShift_ext_one
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} (s t : F.CommShift ℤ)
    (h : Functor.commShiftIso F (self := s) (1 : ℤ) =
      Functor.commShiftIso F (self := t) (1 : ℤ)) : s = t := by
  have hinj {i j k : ℤ} (e : i + j = k)
      (b : shiftFunctor C j ⋙ F ≅ F ⋙ shiftFunctor D j)
      {a a' : shiftFunctor C i ⋙ F ≅ F ⋙ shiftFunctor D i}
      (ha : Functor.CommShift.isoAdd' e a b = Functor.CommShift.isoAdd' e a' b) :
      a = a' := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply (shiftFunctor D j).map_injective
    apply (cancel_mono ((shiftFunctorAdd' D i j k e).inv.app (F.obj X))).1
    apply (cancel_epi (b.hom.app ((shiftFunctor C i).obj X))).1
    apply (cancel_epi (F.map ((shiftFunctorAdd' C i j k e).hom.app X))).1
    simpa only [Functor.CommShift.isoAdd'_hom_app, Category.assoc] using
      congrArg (fun z ↦ z.hom.app X) ha
  have hn (n : ℤ) : Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n := by
    induction n using Int.inductionOn' (b := 0) with
    | zero => rw [Functor.commShiftIso_zero, Functor.commShiftIso_zero]
    | succ n _ ih =>
      rw [Functor.commShiftIso_add, Functor.commShiftIso_add, ih, h]
    | pred n _ ih =>
      apply hinj (show n - 1 + 1 = n by omega)
        (Functor.commShiftIso F (self := s) (1 : ℤ))
      rw [h, ← Functor.commShiftIso_add', ← h, ← Functor.commShiftIso_add']
      exact ih
  cases s
  cases t
  congr
  funext n
  exact hn n

private theorem identity_heq_of_eq
    {C : Type*} [Category C] {A B : C} (h : A = B) : HEq (𝟙 A) (𝟙 B) := by
  subst B
  rfl

private theorem identity_chain_heq
    {C : Type*} [Category C] {A B C' D E F : C}
    (a : A ⟶ B) (b : B ⟶ C') (f : C' ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (hA : A = C') (hB : B = C') (hE : E = D) (hF : F = D)
    (ha : HEq a (𝟙 C')) (hb : HEq b (𝟙 C'))
    (hc : HEq c (𝟙 D)) (hd : HEq d (𝟙 D)) : HEq (a ≫ b ≫ f ≫ c ≫ d) f := by
  subst A
  subst B
  subst E
  subst F
  apply heq_of_eq
  rw [eq_of_heq ha, eq_of_heq hb, eq_of_heq hc, eq_of_heq hd]
  simp only [Category.id_comp, Category.comp_id]

attribute [local irreducible] Functor.commShiftOfLocalization

private theorem localizedShift_heq
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (Q : C ⥤ C') (P : D ⥤ D') (F : C ⥤ D) (J : C' ⥤ D')
    (W : MorphismProperty C) [Q.IsLocalization W]
    [Q.CommShift ℤ] [P.CommShift ℤ] [F.CommShift ℤ]
    (fac : Q ⋙ J = F ⋙ P) (K : C)
    (hsrc : (shiftFunctor _ (1 : ℤ)).obj (Q.obj K) = Q.obj (K⟦(1 : ℤ)⟧))
    (htgt : (shiftFunctor _ (1 : ℤ)).obj (P.obj (F.obj K)) =
      P.obj ((F.obj K)⟦(1 : ℤ)⟧))
    (hQ : HEq ((Q.commShiftIso (1 : ℤ)).hom.app K) (𝟙 (Q.obj (K⟦(1 : ℤ)⟧))))
    (hP : HEq ((P.commShiftIso (1 : ℤ)).hom.app (F.obj K))
      (𝟙 (P.obj ((F.obj K)⟦(1 : ℤ)⟧)))) :
    letI : Localization.Lifting Q W (F ⋙ P) J := ⟨eqToIso fac⟩
    HEq ((Functor.commShiftIso J
      (self := Functor.commShiftOfLocalization Q W ℤ (F ⋙ P) J) (1 : ℤ)).hom.app (Q.obj K))
      (P.map ((F.commShiftIso (1 : ℤ)).hom.app K)) := by
  let : Localization.Lifting Q W (F ⋙ P) J := ⟨eqToIso fac⟩
  rw [Functor.commShiftOfLocalization_iso_hom_app Q W (F ⋙ P) J]
  rw [Functor.commShiftIso_comp_hom_app]
  have hobj (V : C) :
    J.obj (Q.obj V) = P.obj (F.obj V) := Functor.congr_obj fac V
  have heh (V : C) :
    HEq ((Localization.Lifting.iso Q W (F ⋙ P) J).hom.app V)
      (𝟙 (P.obj (F.obj V))) := by
    change HEq ((eqToHom fac).app V) _
    rw [eqToHom_app]
    exact eqToHom_heq_id_cod _ _ _
  have hei (V : C) :
    HEq ((Localization.Lifting.iso Q W (F ⋙ P) J).inv.app V)
      (𝟙 (P.obj (F.obj V))) := by
    change HEq ((eqToHom fac.symm).app V) _
    rw [eqToHom_app]
    exact eqToHom_heq_id_dom _ _ _
  have hi := ScalarLocalization.iso_inv_heq_id
    ((Q.commShiftIso (1 : ℤ)).app K) hsrc hQ
  have hmi := (ScalarLocalization.hom_map_heq J hsrc rfl hi).trans
    (heq_of_eq (J.map_id _))
  have hleft : HEq (J.map ((Q.commShiftIso (1 : ℤ)).inv.app K))
    (𝟙 (P.obj (F.obj (K⟦(1 : ℤ)⟧)))) := by
    exact hmi.trans (identity_heq_of_eq (hobj _))
  have hright := (ScalarLocalization.hom_map_heq (shiftFunctor _ (1 : ℤ))
    rfl (hobj K) (hei K)).trans
    (heq_of_eq ((shiftFunctor _ (1 : ℤ)).map_id _))
  have hright' : HEq
    ((shiftFunctor _ (1 : ℤ)).map
      ((Localization.Lifting.iso Q W (F ⋙ P) J).inv.app K))
    (𝟙 (P.obj ((F.obj K)⟦(1 : ℤ)⟧))) :=
    hright.trans (identity_heq_of_eq htgt)
  simp only [Category.assoc]
  change HEq (_ ≫ _ ≫ P.map ((F.commShiftIso (1 : ℤ)).hom.app K) ≫ _ ≫ _)
    (P.map ((F.commShiftIso (1 : ℤ)).hom.app K))
  exact identity_chain_heq
    (J.map ((Q.commShiftIso (1 : ℤ)).inv.app K))
    ((Localization.Lifting.iso Q W (F ⋙ P) J).hom.app (K⟦(1 : ℤ)⟧))
    (P.map ((F.commShiftIso (1 : ℤ)).hom.app K))
    ((P.commShiftIso (1 : ℤ)).hom.app (F.obj K))
    ((shiftFunctor _ (1 : ℤ)).map
    ((Localization.Lifting.iso Q W (F ⋙ P) J).inv.app K))
    ((congrArg J.obj hsrc).trans (hobj _)) (hobj _)
    htgt ((congrArg (shiftFunctor _ (1 : ℤ)).obj (hobj K)).trans htgt)
    hleft (heh _) hP hright'

private theorem rationalLocalizationShift_hom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (K : sfIntegralConstructibleCategory l E T) :
    HEq (((sfRationalConstructibleLocalization l E T).commShiftIso (1 : ℤ)).hom.app K)
      (𝟙 ((sfRationalConstructibleLocalization l E T).obj (K⟦(1 : ℤ)⟧))) := by
  exact (sfRationalTriangulationDatum l E T).choose_spec.choose_spec.2
    |>.choose_spec.choose_spec.1 K

section CoefficientTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (a : E →ₐ[Padic l] L)

/-- The integral scalar shift inherited from the normalized ordinary comparison.
Source: rational purity proof Step 2, scalar compatibility
(blueprint: def-pur-canonical-purity-source-transports). -/
def integralScalarShift (T : Scheme.{u}) (n : ℤ) :=
  letI := (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
    l E L a T).exists.choose
  (sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero E L a T).commShiftIso n

/-- The rational scalar shift is uniquely determined by its integral degree-one components.
Source: rational purity proof Step 2, scalar compatibility
(blueprint: def-pur-canonical-purity-source-transports).
Proof: localize integralScalarShift and its inverse. Naturality on integral arrows
extends to all fractions. The integral zero and addition identities localize too.
The shift and localization are pinned at one. Coherence determines every integer
comparison, and the degree-one component formula gives uniqueness. -/
theorem scalarShift_existsUnique (T : Scheme.{u}) :
    ∃! c : (sfRationalScalarExtension l E T 0 (Fact.out : l.Prime).ne_zero L a).CommShift ℤ,
      (fun [h : (sfRationalScalarExtension l E T 0
          (Fact.out : l.Prime).ne_zero L a).CommShift ℤ] ↦
        ∀ K : sfRationalConstructibleCategory l E T,
          HEq (((sfRationalScalarExtension l E T 0
            (Fact.out : l.Prime).ne_zero L a).commShiftIso (1 : ℤ)).hom.app K)
            ((sfRationalConstructibleLocalization l L T).map
              ((integralScalarShift l E L a T (1 : ℤ)).hom.app K.obj))) (h := c) := by
  unfold sfRationalScalarExtension
  let F := sfConstructibleIntegralScalarExtension 0 l
    (Fact.out : l.Prime).ne_zero E L a T
  let J := (sfRationalScalarExtension_existsUnique l E T 0
    (Fact.out : l.Prime).ne_zero L a).exists.choose
  let Q := sfRationalConstructibleLocalization l E T
  let P := sfRationalConstructibleLocalization l L T
  let : F.CommShift ℤ :=
    (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
      l E L a T).exists.choose
  let W := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (sfIntegralConstructibleCategory l E T)
  have : Q.IsLocalization W :=
    ScalarLocalization.semilinear_localization_isLocalization
      (Padic.coefficientExtensionIntegers l E)
      (sfIntegralConstructibleCategory l E T)
      (Padic.coefficientExtensionUniformizer l E)
  have spec := (sfRationalScalarExtension_existsUnique l E T 0
    (Fact.out : l.Prime).ne_zero L a).exists.choose_spec
  have fac : Q ⋙ J = F ⋙ P := by
    apply Functor.hext (fun K ↦ spec.2.1 ⟨K⟩)
    intro K M f
    have hf := spec.2.2 K M f 1
    change HEq (J.map (Q.map f)) (P.map (F.map f))
    dsimp only [J, F, Q, P, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] at hf ⊢
    simp only [map_one] at hf
    refine hf.trans ?_
    rfl
  let : Localization.Lifting Q W (F ⋙ P) J := ⟨eqToIso fac⟩
  let c : J.CommShift ℤ := Functor.commShiftOfLocalization Q W ℤ (F ⋙ P) J
  have hc (K : sfRationalConstructibleCategory l E T) :
      HEq ((Functor.commShiftIso J (self := c) (1 : ℤ)).hom.app K)
        (P.map ((integralScalarShift l E L a T (1 : ℤ)).hom.app K.obj)) := by
    let K₀ := K.obj
    change HEq ((Functor.commShiftIso J (self := c) (1 : ℤ)).hom.app (Q.obj K₀))
      (P.map ((Functor.commShiftIso F (1 : ℤ)).hom.app K₀))
    have hQ := rationalLocalizationShift_hom l E T K₀
    have hP := rationalLocalizationShift_hom l L T (F.obj K₀)
    have hsrc : (shiftFunctor _ (1 : ℤ)).obj (Q.obj K₀) = Q.obj (K₀⟦(1 : ℤ)⟧) :=
      Functor.congr_obj (sfRationalTriangulationDatum l E T).choose_spec.choose_spec.1
        (Q.obj K₀)
    have htgt : (shiftFunctor _ (1 : ℤ)).obj (P.obj (F.obj K₀)) =
        P.obj ((F.obj K₀)⟦(1 : ℤ)⟧) :=
      Functor.congr_obj (sfRationalTriangulationDatum l L T).choose_spec.choose_spec.1
        (P.obj (F.obj K₀))
    refine localizedShift_heq
      (C := sfIntegralConstructibleCategory l E T)
      (D := sfIntegralConstructibleCategory l L T)
      (C' := sfRationalConstructibleCategory l E T)
      (D' := sfRationalConstructibleCategory l L T)
      Q P F J W fac K₀ hsrc htgt ?_ ?_
    · exact hQ
    · exact hP
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply integerShift_ext_one
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply eq_of_heq
  exact (hc' K).trans (hc K).symm

/-- The scalar shift fixed by localization of the ordinary integral comparison.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
@[instance_reducible]
def scalarShift (T : Scheme.{u}) :
    (sfRationalScalarExtension l E T 0 (Fact.out : l.Prime).ne_zero L a).CommShift ℤ :=
  (scalarShift_existsUnique l E L a T).exists.choose

/-- Scalar transport of the degree-zero line in ambient derived coordinates.
Every factor is fixed by completion, single-complex descent, and the signed root-line
scalar comparison; it is not a new line trivialization.
Source: rational purity proof Step 2, finite coefficient extension
(blueprint: def-pur-canonical-purity-source-transports). -/
def lineScalarAmbient (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)]
    (m : ℤ) :=
  (scalarCompletionIso l E L a T (sfIntegralTwistingObject l E T m)
    (sfIntegralTwistingObject_mem l E T m).1).symm ≪≫
    ((integralOrdinaryScalar l E L a T).mapDerivedCategorySingleFunctor 0).app
      (integralTwistLine l E T m) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (twistLineScalarIso l E T L a m)

/-- The line scalar comparison in intrinsic integral representatives retains that map.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports).
Proof: the rational scalar functor's object clause is the literal completed integral
scalar extension. The preceding ambient comparison therefore has these underlying
objects. Lift it through the full subcategory inclusion. Faithfulness and the displayed
underlying hom condition give uniqueness. -/
theorem lineScalarIntegral_existsUnique (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (m : ℤ) :
    ∃! e : ((sfRationalScalarExtension l E T 0 (Fact.out : l.Prime).ne_zero L a).obj
        (sfRationalTwistingCoefficient l E T m)).obj ≅ sfIntegralTwistingCoefficient l L T m,
      HEq e.hom.hom (lineScalarAmbient l E L a T m).hom := by
  have hobj : ((sfRationalScalarExtension l E T 0
      (Fact.out : l.Prime).ne_zero L a).obj
        (sfRationalTwistingCoefficient l E T m)).obj =
      (sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
        E L a T).obj (sfIntegralTwistingCoefficient l E T m) := by
    unfold sfRationalScalarExtension
    exact congrArg (fun K : sfRationalConstructibleCategory l L T ↦ K.obj)
      ((sfRationalScalarExtension_existsUnique l E T 0
        (Fact.out : l.Prime).ne_zero L a).exists.choose_spec.2.1
          (sfRationalTwistingCoefficient l E T m))
  rw [hobj]
  refine ⟨ObjectProperty.isoMk _ (lineScalarAmbient l E L a T m), HEq.rfl, ?_⟩
  intro e he
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact eq_of_heq he

/-- The rational scalar comparison on the coefficient line.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
def lineScalar (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)] (m : ℤ) :
    (sfRationalScalarExtension l E T 0 (Fact.out : l.Prime).ne_zero L a).obj
      (sfRationalTwistingCoefficient l E T m) ≅ sfRationalTwistingCoefficient l L T m :=
  (sfRationalConstructibleLocalization l L T).mapIso
    (lineScalarIntegral_existsUnique l E L a T m).exists.choose

/-- The canonical pullback/tensor/line/shift comparison for finite scalar extension.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
def sourceScalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l E X 0 (Fact.out : l.Prime).ne_zero L a).obj
        ((rationalSource l E f d).obj K) ≅
      (rationalSource l L f d).obj
        ((sfRationalScalarExtension l E Y 0 (Fact.out : l.Prime).ne_zero L a).obj K) :=
  (rationalTensorScalarComparison l E L a X).app
      ((sfRationalTwistingCoefficient l E X (d : ℤ))⟦2*(d : ℤ)⟧,
        (rationalDerivedPullback l E f).obj K) ≪≫
    (rationalDerivedTensor l L X).mapIso
      (Iso.prod
        ((Functor.commShiftIso
          (sfRationalScalarExtension l E X 0 (Fact.out : l.Prime).ne_zero L a)
          (self := scalarShift l E L a X) (2*(d : ℤ))).app _ ≪≫
          (shiftFunctor _ (2*(d : ℤ))).mapIso (lineScalar l E L a X (d : ℤ)))
        ((rationalPullbackScalarComparison l E L a f).app K))

end CoefficientTransport

section CommonSource
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

-- Match the transported field and module structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The shifted coefficient line as a literal pair at the least finite stage.
This is the canonical stage presentation of the existing Qbar Tate line and its shift.
Source: rational purity proof Step 2, common-stage presentation
(blueprint: def-pur-canonical-purity-source-transports). -/
def commonShiftedLine (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (d : ℕ) : generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  ⟨Padic.finiteCoefficientBase l Ω,
    (sfRationalTwistingCoefficient l (Coefficient.{u} l Ω
      (Padic.finiteCoefficientBase l Ω)) X (d : ℤ))⟦2*(d : ℤ)⟧⟩

/-- The actual common-stage tensor and pullback with that shifted coefficient line.
Source: rational purity statement, Qbar source
(blueprint: def-pur-canonical-purity-source-transports). -/
def commonSource {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :=
  ((Functor.const (generalAlgebraicallyClosedConstructibleCategory l Ω Y)).obj
    (commonShiftedLine l Ω X d)).prod' (commonStageDerivedPullback l Ω f) ⋙
      commonStageDerivedTensor l Ω X

set_option linter.unusedSectionVars false in
/-- The least coefficient stage is contained in every finite stage.
Source: rational purity proof Step 2, the coefficient directed set
(blueprint: def-pur-canonical-purity-source-transports).
Proof: the underlying field of finiteCoefficientBase is bottom, so the inclusion
is bottom_le. The subtype order is the underlying intermediate-field order. -/
theorem base_le (L : Index l Ω) : Padic.finiteCoefficientBase l Ω ≤ L := by
  exact (bot_le : (⊥ : IntermediateField (Padic l) Ω) ≤ L.val)

/-- The normalized self-transition unitor in the actual stage-system presentation.
Source: rational purity proof Step 2, common-stage identity normalization
(blueprint: def-pur-canonical-purity-source-transports). -/
def selfStageUnit (X : Scheme.{u}) (L : Index l Ω) :
    (stageSystem l Ω X).T (le_rfl : L ≤ L) ≅ 𝟭 (Stage l Ω X L) :=
  operationStageTransitionIso l Ω X L L le_rfl ≪≫ unitor l Ω X L

/-- Scalar transport of the shifted root line to a finite stage.
Source: rational purity proof Step 2, canonical line comparisons
(blueprint: def-pur-canonical-purity-source-transports). -/
def shiftedLineToStage (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (d : ℕ) (L : Index l Ω) :
    (commonShiftedLine l Ω X d).toStage (base_le l Ω L) ≅
      (sfRationalTwistingCoefficient l (Coefficient.{u} l Ω L) X (d : ℤ))⟦2*(d : ℤ)⟧ :=
  (operationStageTransitionIso l Ω X (Padic.finiteCoefficientBase l Ω) L
    (base_le l Ω L)).app _ ≪≫
    (Functor.commShiftIso
      (GeneralAlgebraicallyClosedCoefficients.transition l Ω X
        (Padic.finiteCoefficientBase l Ω) L (base_le l Ω L))
      (self := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X
        (Padic.finiteCoefficientBase l Ω) L
        (base_le l Ω L)) (2*(d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2*(d : ℤ))).mapIso
      (lineScalar l (Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω))
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L (base_le l Ω L)) X (d : ℤ))

/-- The literal tensor-stage object of the common source.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
def commonSourceObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  commonStageTensorObject l Ω X (commonShiftedLine l Ω X d)
    (commonStagePullbackObject l Ω f K)

/-- Both selected operation functors retain their specified literal object formulas.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports).
Proof: use the object clauses of commonStageDerivedPullback_existsUnique and
commonStageDerivedTensor_existsUnique. Substitution gives precisely commonSourceObject. -/
theorem commonSource_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonSource l Ω f d).obj K = commonSourceObject l Ω f d K := by
  change (commonStageDerivedTensor l Ω X).obj
    (commonShiftedLine l Ω X d, (commonStageDerivedPullback l Ω f).obj K) = _
  have hobj : (commonStageDerivedPullback l Ω f).obj K =
      commonStagePullbackObject l Ω f K := by
    unfold commonStageDerivedPullback
    with_reducible_and_instances exact
      (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 K
  rw [hobj]
  unfold commonStageDerivedTensor commonSourceObject
  with_reducible_and_instances exact
    ((commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1
      (commonShiftedLine l Ω X d) (commonStagePullbackObject l Ω f K))

/-- The compositum with the least coefficient field is contained in K's own stage.
Source: rational purity proof Step 2, one-stage presentation
(blueprint: def-pur-canonical-purity-source-transports).
Proof: the two tensor inputs have stages bottom and K.stage, respectively.
Their compositum is the supremum. Apply sup_le with bottom_le and le_rfl. -/
theorem commonSource_stage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonSourceObject l Ω f d K).stage ≤ K.stage := by
  change (⊥ : IntermediateField (Padic l) Ω) ⊔ K.stage.val ≤ K.stage.val
  exact sup_le bot_le le_rfl

/-- The source represented over the object's own finite field, with all scalar
associators, root-line comparisons, and self-transition unitors retained.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
def commonSourceStageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonSourceObject l Ω f d K).toStage (commonSource_stage l Ω f d K) ≅
      (rationalSource l (Coefficient.{u} l Ω K.stage) f d).obj K.obj :=
  commonStageTensorComparison l Ω X (commonShiftedLine l Ω X d)
    (commonStagePullbackObject l Ω f K) K.stage (commonSource_stage l Ω f d K) ≪≫
    (rationalDerivedTensor l (Coefficient.{u} l Ω K.stage) X).mapIso
      (Iso.prod (shiftedLineToStage l Ω X d K.stage)
        ((selfStageUnit l Ω X K.stage).app _))

/-- Canonical identification of common-source objects with their rational stage.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
def commonSourceComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonSource l Ω f d).obj K ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).obj
        ((rationalSource l (Coefficient.{u} l Ω K.stage) f d).obj K.obj) :=
  eqToIso (commonSource_obj l Ω f d K) ≪≫
    (stageSystem l Ω X).isoToStage (commonSourceObject l Ω f d K)
      (commonSource_stage l Ω f d K) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso
      (commonSourceStageComparison l Ω f d K)

end CommonSource

end RationalSmoothPurityCanonical

namespace RationalSmoothPurityCanonical

/-- The ordinary K-flat total tensor, before completion.
Source: rational purity proof, integral representatives
(blueprint: def-pur-canonical-purity-source-transports). -/
def ordinaryTotal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    CochainComplex (integralTowerModules l E T) ℤ ×
      CochainComplex (integralTowerModules l E T) ℤ ⥤
        CochainComplex (integralTowerModules l E T) ℤ :=
  coefficientTotalTensor.{u, u + 1, u} (ProEt.topology T)
    (completedIntegralCommRingSheafUnrestricted l E T)

/-- The two strict Roos coordinates specifying the tensor augmentation.
Source: rational purity proof Step 1, completed tensor convention
(blueprint: def-pur-canonical-purity-source-transports). -/
def TensorAugmentationNormalized (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (eta : ordinaryTotal l E T ⟶ integralOperationsTensorComplexFunctor l E T) : Prop :=
      (∀ (P Q : CochainComplex (integralTowerModules l E T) ℤ)
        (p q : ℤ) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (((eta.app (P,Q)).f (p + q) ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
                (P,Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor l E T).obj (P,Q))))).f (p + q) ≫
          (Pi.π (fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
            (P,Q)).obj (op j)) n).f (p + q)).val.app U)
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology T)
              (completedIntegralCommRingSheafUnrestricted l E T) P Q p q (p+q) rfl U x y) =
          integralOperationsTotalTensorSection l E T n P Q p q U
            (unrestrictedIntegralTensorSection l E T n (P.X p) U 1 x)
            (unrestrictedIntegralTensorSection l E T n (Q.X q) U 1 y)) ∧
      ∀ (P Q : CochainComplex (integralTowerModules l E T) ℤ) (i : ℤ),
        (eta.app (P,Q)).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
                (P,Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor l E T).obj (P,Q))))).v
                  i (i - 1) (by omega) = 0

attribute [local irreducible] TensorAugmentationNormalized

section TensorAugmentationProof
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence
  coefficientTensorGenerator StrictTensorAugmentation.map integralOperationsTotalTensorSection
  unrestrictedIntegralTensorSection
attribute [local implicit_reducible] coefficientTotalTensor
attribute [local implicit_reducible] ordinaryTotal integralOperationsTensorComplexFunctor
  integralOperationsRoos integralOperationsRoosFunctor

/-- The ordinary-to-completed tensor map is the strict quotient augmentation.
Its product component is fixed on all pure total tensors, and its second cone
component is zero. This specifies the full Roos map before localization.
Source: rational purity proof Step 1, completed tensor convention
(blueprint: def-pur-canonical-purity-source-transports).
Proof: send x tensor y to the tensor of their images in each positive quotient.
Balanced tensors and total-summand injections extend this to a chain map to the
product tower. Compatibility with quotient transitions annihilates 1-s.
The mapping-cocone lift with second component zero exists and is unique.
The generator equations and zero second component prove naturality and uniqueness. -/
theorem tensorAugmentation_existsUnique (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    ∃! eta : ordinaryTotal l E T ⟶ integralOperationsTensorComplexFunctor l E T,
      TensorAugmentationNormalized l E T eta := by
  unfold TensorAugmentationNormalized
  exact StrictTensorAugmentation.existsUnique_normalized l E T

end TensorAugmentationProof

/-- The fixed tensor augmentation, including both strict cone components.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-purity-source-transports). -/
def tensorAugmentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    ordinaryTotal l E T ⟶ integralOperationsTensorComplexFunctor l E T :=
  (tensorAugmentation_existsUnique l E T).exists.choose

attribute [local irreducible] tensorAugmentation

private theorem ordinary_model_from_comparison (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (A : DerivedCategory.{u + 2} (proEtaleRingModules T R) ×
      DerivedCategory.{u + 2} (proEtaleRingModules T R) ⥤
        DerivedCategory.{u + 2} (proEtaleRingModules T R))
    (c : (((coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology T) R).prod
      (coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology T) R)) ⋙
        coefficientTotalTensor.{u, u + 1, u} (ProEt.topology T) R ⋙ DerivedCategory.Q ≅
      ((coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology T) R ⋙ DerivedCategory.Q).prod
        (coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology T) R ⋙ DerivedCategory.Q)) ⋙ A)) :
    ∃! a : ProEtaleTensorModel T R,
      a.tensor = A ∧
      ∀ (P Q : (proEtaleFlatRepresentatives T R).FullSubcategory)
        (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          T.ProEt _ (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (ProEt.topology T) R P.obj)
        (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          T.ProEt _ (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (ProEt.topology T) R Q.obj),
        HEq (a.representative.app (P, Q))
          (c.app (⟨P.obj, hP⟩, ⟨Q.obj, hQ⟩)) := by
  let ι : (proEtaleFlatRepresentatives T R).FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology T) (R := R)) := {
    obj := fun P ↦ ⟨P.obj,
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
    map := fun f ↦ ObjectProperty.homMk f.hom }
  let a : ProEtaleTensorModel T R := {
    tensor := A
    representative := NatIso.ofComponents
      (fun PQ ↦ c.app (ι.obj PQ.1, ι.obj PQ.2))
      (fun f ↦ c.hom.naturality ((ι.prod ι).map f)) }
  refine ⟨a, ⟨rfl, fun P Q hP hQ ↦ HEq.rfl⟩, ?_⟩
  rintro ⟨b, e⟩ ⟨hb, he⟩
  dsimp only at hb
  subst b
  congr 1
  apply Iso.ext
  apply NatTrans.ext
  funext ⟨P, Q⟩
  exact congrArg Iso.hom (eq_of_heq (he P Q
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q.obj).2 Q.property.1)))

/-- The ordinary tensor model belonging to the recorded coherent coefficient calculus.
Its representative is fixed by that calculus's ordinary total-tensor comparison.
Source: rational purity proof, projection-formula transpose
(blueprint: def-pur-canonical-purity-source-transports).
Proof: restrict the calculus's K-flat comparison to flat-term K-flat complexes.
The ordinary totals in the two interfaces are the same signed direct-sum total;
transport across that definitional presentation equality. This produces a natural
isomorphism and fixes it uniquely at every pair of representatives. -/
theorem ordinaryModel_existsUnique (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    ∃! a : ProEtaleTensorModel T (completedIntegralCommRingSheafUnrestricted l E T),
      a.tensor = (@RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} l E T none)).tensor ∧
      ∀ (P Q : (proEtaleFlatRepresentatives T
        (completedIntegralCommRingSheafUnrestricted l E T)).FullSubcategory),
        ∀ (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          T.ProEt _ (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (ProEt.topology T)
          (completedIntegralCommRingSheafUnrestricted l E T) P.obj)
          (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          T.ProEt _ (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (ProEt.topology T)
          (completedIntegralCommRingSheafUnrestricted l E T) Q.obj),
        HEq (a.representative.app (P,Q))
          (@CoefficientTensorModels.iso.{u, u + 1, u, u + 2} _ _ _
            (IntegralOnSlice.abSheafify.{u, u} T none)
            (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _ _
            (@RingedSiteDualityModel.models.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} l E T none)) P.obj Q.obj hP hQ) := by
  let R : Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
    completedIntegralCommRingSheafUnrestricted l E T
  let S := @RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
    _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
    (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
    (IntegralOnSlice.duality.{u, u} l E T none)
  let M := @RingedSiteDualityModel.models.{u + 1, u, u, u + 2}
    _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
    (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
    (IntegralOnSlice.duality.{u, u} l E T none)
  exact ordinary_model_from_comparison T R S.tensor
    (CoefficientTensorModels.comparison.{u, u + 1, u, u + 2} M)

/-- The ordinary derived tensor with its fixed representative data.
Source: rational purity proof, tensor transpose
(blueprint: def-pur-canonical-purity-source-transports). -/
def ordinaryModel (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    ProEtaleTensorModel T (completedIntegralCommRingSheafUnrestricted l E T) :=
  (ordinaryModel_existsUnique l E T).exists.choose

attribute [local irreducible] ordinaryModel

/-- The two existing K-flat encodings agree for the fixed ordinary module tensor.
Source: rational purity proof, K-flat representatives
(blueprint: def-pur-canonical-purity-source-transports).
Proof: unfold both K-flat predicates. Their test functors are the same signed total
tensor with the same sheaf monoidal structure; the flat-term conjunct is identical. -/
theorem goodOrdinary (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (hP : integralOperationsGoodComplex l E T P) :
    proEtaleFlatRepresentatives T
      (completedIntegralCommRingSheafUnrestricted l E T) P := by
  exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP.1, hP.2⟩

section TensorAugmentationIsoProof
attribute [local irreducible] StrictTensorAugmentation.map
  IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralReductionExistence coefficientTensorGenerator
  integralOperationsTotalTensorSection unrestrictedIntegralTensorSection
attribute [local implicit_reducible] ordinaryTotal IntegralAmbient.tensorTower
attribute [local irreducible] coefficientTotalTensor

private theorem strict_tensor_normalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :
    TensorAugmentationNormalized l E T (StrictTensorAugmentation.map l E T) := by
  unfold TensorAugmentationNormalized
  exact StrictTensorAugmentation.map_normalized l E T

private theorem tensorAugmentation_eq_strict (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) : tensorAugmentation l E T = StrictTensorAugmentation.map l E T := by
  unfold tensorAugmentation
  exact (tensorAugmentation_existsUnique l E T).unique
    (tensorAugmentation_existsUnique l E T).exists.choose_spec (strict_tensor_normalized l E T)

private theorem isIso_map_comp_map_iso
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F : B ⥤ D) (G : A ⥤ B) {W : B} {X Y : A}
    (f : W ⟶ G.obj X) (e : X ≅ Y) (hf : IsIso (F.map f)) :
    IsIso (F.map (f ≫ G.map e.hom)) := by
  let := hf
  rw [F.map_comp]
  infer_instance

-- `flatConstantModulesAbelian` (universes `max u v`) leaves a universe metavariable unsolved.
attribute [-instance] CategoryTheory.flatConstantModulesAbelian in
/-- On the constructible finite-Tor domain the ordinary tensor is already complete.
The map asserted invertible is the fixed strict quotient augmentation.
Source: rational purity proof, completed tensor on integral representatives
(blueprint: def-pur-canonical-purity-source-transports).
Proof: choose bounded flat models on a finite constructible stratification. Tensor
with each bounded finite-projective term preserves derived completeness and the
common Tor bounds. Glue the strata by the localization triangles. The strict Roos
augmentation is the completion unit, hence a quasi-isomorphism. -/
theorem tensorAugmentation_isIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E T) ℤ)
    (hP : integralOperationsGoodComplex l E T P)
    (hQ : integralOperationsGoodComplex l E T Q)
    (hM : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj P))
    (hN : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj Q)) :
    IsIso (DerivedCategory.Q.map ((tensorAugmentation l E T).app (P,Q))) := by
  let C := IntegralSystemRealization.calculus l E T
  let V := (ordinaryTotal l E T).obj (P, Q)
  let e : DerivedCategory.Q.obj V ≅
      C.integralClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
    C.integralTensorModel.iso (ProEt.topology T)
      (completedIntegralCommRingSheafUnrestricted l E T) C.integralClosed P Q hP.1 hQ.1
  have hc := GeneratorReduction.finiteTorOrdinaryTensorComplete l E T
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) hM hN
  have ht : IsIso ((IntegralOnSlice.completionUnit l E T none).app
      (C.integralClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))) :=
    (IntegralOnSlice.canonicalCompletionUnitCriterion l E T _).mpr hc
  have hu : IsIso ((IntegralOnSlice.completionUnit l E T none).app
      (DerivedCategory.Q.obj V)) :=
    (NatTrans.isIso_app_iff_of_iso (IntegralOnSlice.completionUnit l E T none) e).mpr ht
  have hV : IntegralOnSlice.Good l E T none V :=
    IntegralAmbient.tensor_good l E T P Q hP hQ
  have hunit := (IntegralOnSlice.completionUnit_existsUnique l E T none).exists.choose_spec
    ⟨V, hV⟩
  have hi : IsIso (DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none V)) := by
    exact (congrArg IsIso hunit).mp
      (IsIso.comp_isIso' hu
        ((IntegralOnSlice.completionComparison l E T none).app ⟨V, hV⟩).isIso_hom)
  rw [tensorAugmentation_eq_strict, StrictTensorAugmentation.map_app]
  unfold IntegralAmbient.tensorOperationUnit
  exact isIso_map_comp_map_iso DerivedCategory.Q integralOperationsRoosFunctor
    (IntegralOnSlice.roosUnit l E T none V)
    ((IntegralAmbient.tensorTowerIso l E T).app (P, Q)) hi

end TensorAugmentationIsoProof

/-- The completion comparison on good finite-Tor representatives.
Source: rational purity proof, projection transpose
(blueprint: def-pur-canonical-purity-source-transports). -/
def tensorToOrdinaryOnGood (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E T) ℤ)
    (hP : integralOperationsGoodComplex l E T P)
    (hQ : integralOperationsGoodComplex l E T Q)
    (hM : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj P))
    (hN : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj Q)) :
    (integralCompletedTensor l E T).obj (DerivedCategory.Q.obj P,
      DerivedCategory.Q.obj Q) ≅
    (ordinaryModel l E T).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  (integralCompletedTensorComparison l E T).app (⟨P,hP⟩,⟨Q,hQ⟩) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((tensorAugmentation l E T).app (P,Q)))
      (tensorAugmentation_isIso l E T P Q hP hQ hM hN)).symm ≪≫
    (ordinaryModel l E T).representative.app
      (⟨P,goodOrdinary l E T P hP⟩,⟨Q,goodOrdinary l E T Q hQ⟩)

attribute [local irreducible] tensorToOrdinaryOnGood
attribute [local implicit_reducible] integralOperationsGoodLocalization

private theorem inverse_comparison
    {C : Type*} [Category C] {X Y Z W : C}
    (e : X ≅ Y) (f : Z ⟶ Y) (h : IsIso f) (a : Z ≅ W) :
    (e ≪≫ (@asIso _ _ _ _ f h).symm ≪≫ a).inv = a.inv ≫ f ≫ e.inv := by
  simp only [Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc]

private theorem product_symm
    {C D : Type*} [Category C] [Category D] {X Y : C} {U V : D}
    (e : X ≅ Y) (f : U ≅ V) : Iso.prod e.symm f.symm = (Iso.prod e f).symm := by
  apply Iso.ext
  simp only [Iso.prod_hom, Iso.symm_hom, Iso.prod_inv]

private theorem transport_inverse
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (τ : F ⟶ G) {X Y : C} (e : X ≅ Y) (a : G.obj X ≅ F.obj X)
    (ha : τ.app X = a.inv) :
    (G.mapIso e.symm ≪≫ a ≪≫ F.mapIso e).inv = τ.app Y := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc]
  rw [← ha, ← τ.naturality e.hom, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id,
    Category.id_comp]

private theorem normalized_descent_comparison
    {C D H : Type*} [Category C] [Category D] [Category H]
    (L : C ⥤ D) (V : MorphismProperty C) [L.IsLocalization V]
    {A B : D ⥤ H} {R S : C ⥤ H}
    (r : R ≅ L ⋙ A) (d : L ⋙ B ≅ S) (α : R ⟶ S)
    (M : D) (P : ObjectProperty C)
    (hP : ∀ X : C, (L.obj X ≅ M) → P X)
    (c : ∀ (X : C), P X → (B.obj (L.obj X) ≅ A.obj (L.obj X)))
    (hc : ∀ (X : C) (hX : P X),
      (c X hX).inv = (r.app X).inv ≫ α.app X ≫ (d.app X).inv) :
    ∃! e : B.obj M ≅ A.obj M,
      ∀ (X : C) (hX : P X) (eX : L.obj X ≅ M),
        e = B.mapIso eX.symm ≪≫ c X hX ≪≫ A.mapIso eX := by
  let : L.EssSurj := Localization.essSurj L V
  let ff := Localization.fullyFaithfulWhiskeringLeft L V H
  let η : L ⋙ A ⟶ L ⋙ B := r.inv ≫ α ≫ d.inv
  let τ : A ⟶ B := ff.preimage η
  have hτ (X : C) :
      τ.app (L.obj X) = (r.app X).inv ≫ α.app X ≫ (d.app X).inv := by
    have h := congrArg (fun t ↦ t.app X) (ff.map_preimage η)
    change τ.app (L.obj X) = η.app X at h
    simpa only [η, NatTrans.comp_app, Iso.app_inv] using h
  have hc_inv (X : C) (hX : P X) : τ.app (L.obj X) = (c X hX).inv := by
    exact (hτ X).trans (hc X hX).symm
  have hn (X : C) (hX : P X) (eX : L.obj X ≅ M) :
      (B.mapIso eX.symm ≪≫ c X hX ≪≫ A.mapIso eX).inv = τ.app M :=
    transport_inverse τ eX (c X hX) (hc_inv X hX)
  let X := L.objPreimage M
  let eX := L.objObjPreimageIso M
  let hX := hP X eX
  let e := B.mapIso eX.symm ≪≫ c X hX ≪≫ A.mapIso eX
  refine ⟨e, ?_, ?_⟩
  · intro Y hY eY
    apply Iso.ext_inv
    exact (hn X hX eX).trans (hn Y hY eY).symm
  · intro e' he'
    exact he' X hX eX

private theorem product_normalization
    {C D H : Type*} [Category C] [Category D] [Category H]
    (G : ObjectProperty C) (L : G.FullSubcategory ⥤ D)
    {A B : D × D ⥤ H} (M N : D) (P : ObjectProperty D)
    (c : ∀ (Z : G.FullSubcategory × G.FullSubcategory),
      (P (L.obj Z.1) ∧ P (L.obj Z.2)) →
        (B.obj (L.obj Z.1, L.obj Z.2) ≅ A.obj (L.obj Z.1, L.obj Z.2)))
    (h : ∃! e : B.obj (M, N) ≅ A.obj (M, N),
      ∀ (Z : G.FullSubcategory × G.FullSubcategory)
        (hZ : P (L.obj Z.1) ∧ P (L.obj Z.2)) (eZ : (L.prod L).obj Z ≅ (M, N)),
        e = B.mapIso eZ.symm ≪≫ c Z hZ ≪≫ A.mapIso eZ) :
    ∃! e : B.obj (M, N) ≅ A.obj (M, N),
      ∀ (X Y : C) (hX : G X) (hY : G Y)
        (pX : P (L.obj ⟨X, hX⟩)) (pY : P (L.obj ⟨Y, hY⟩))
        (eX : L.obj ⟨X, hX⟩ ≅ M) (eY : L.obj ⟨Y, hY⟩ ≅ N),
        e = B.mapIso (Iso.prod eX.symm eY.symm) ≪≫
          c (⟨X, hX⟩, ⟨Y, hY⟩) ⟨pX, pY⟩ ≪≫ A.mapIso (Iso.prod eX eY) := by
  obtain ⟨e, he, hu⟩ := h
  refine ⟨e, ?_, ?_⟩
  · intro X Y hX hY pX pY eX eY
    rw [product_symm eX eY]
    exact he (⟨X, hX⟩, ⟨Y, hY⟩) ⟨pX, pY⟩ (Iso.prod eX eY)
  · intro e' he'
    apply hu e'
    intro ⟨X, Y⟩ hZ eZ
    let eX := (CategoryTheory.Prod.fst _ _).mapIso eZ
    let eY := (CategoryTheory.Prod.snd _ _).mapIso eZ
    have hprod : Iso.prod eX eY = eZ := by
      apply Iso.ext
      simp only [eX, eY, Iso.prod_hom, Functor.mapIso_hom]
      rfl
    rw [← hprod, ← product_symm eX eY]
    exact he' X.obj Y.obj X.property Y.property hZ.1 hZ.2 eX eY

private theorem tensor_comparison_from_augmentation
    {C D : Type*} [Category C] [Category D]
    (G H : ObjectProperty C) (hGH : ∀ X, G X → H X)
    (q : C ⥤ D) (V : MorphismProperty G.FullSubcategory) [V.ContainsIdentities]
    [(G.ι ⋙ q).IsLocalization V]
    (A B : D × D ⥤ D) (F K : C × C ⥤ C)
    (rH : (H.ι.prod H.ι) ⋙ F ⋙ q ≅ ((H.ι ⋙ q).prod (H.ι ⋙ q)) ⋙ A)
    (d : ((G.ι ⋙ q).prod (G.ι ⋙ q)) ⋙ B ≅ (G.ι.prod G.ι) ⋙ K ⋙ q)
    (α : F ⟶ K) (P : ObjectProperty D)
    (hP : ∀ {X Y : D}, (X ≅ Y) → P X → P Y)
    (hi : ∀ (X Y : C) (hX : G X) (hY : G Y)
      (pX : P (q.obj X)) (pY : P (q.obj Y)), IsIso (q.map (α.app (X, Y))))
    (M N : D) (pM : P M) (pN : P N) :
    ∃! e : B.obj (M, N) ≅ A.obj (M, N),
      ∀ (X Y : C) (hX : G X) (hY : G Y)
        (pX : P (q.obj X)) (pY : P (q.obj Y))
        (eX : q.obj X ≅ M) (eY : q.obj Y ≅ N),
        e = B.mapIso (Iso.prod eX.symm eY.symm) ≪≫
          (d.app (⟨X, hX⟩, ⟨Y, hY⟩) ≪≫
            (@asIso _ _ _ _ (q.map (α.app (X, Y))) (hi X Y hX hY pX pY)).symm ≪≫
            rH.app (⟨X, hGH X hX⟩, ⟨Y, hGH Y hY⟩)) ≪≫
          A.mapIso (Iso.prod eX eY) := by
  let L := G.ι ⋙ q
  have : L.IsLocalization V := inferInstanceAs ((G.ι ⋙ q).IsLocalization V)
  let ι : G.FullSubcategory ⥤ H.FullSubcategory := {
    obj := fun X ↦ ⟨X.obj, hGH X.obj X.property⟩
    map := fun f ↦ ObjectProperty.homMk f.hom }
  let r : (G.ι.prod G.ι) ⋙ F ⋙ q ≅ (L.prod L) ⋙ A :=
    NatIso.ofComponents (fun Z ↦ rH.app (ι.obj Z.1, ι.obj Z.2))
      (fun f ↦ rH.hom.naturality ((ι.prod ι).map f))
  let β : (G.ι.prod G.ι) ⋙ F ⋙ q ⟶ (G.ι.prod G.ι) ⋙ K ⋙ q :=
    Functor.whiskerLeft (G.ι.prod G.ι) (Functor.whiskerRight α q)
  let P' : ObjectProperty (G.FullSubcategory × G.FullSubcategory) :=
    fun Z ↦ P (L.obj Z.1) ∧ P (L.obj Z.2)
  have hp (Z : G.FullSubcategory × G.FullSubcategory)
      (eZ : (L.prod L).obj Z ≅ (M, N)) : P' Z :=
    ⟨hP ((CategoryTheory.Prod.fst _ _).mapIso eZ).symm pM,
      hP ((CategoryTheory.Prod.snd _ _).mapIso eZ).symm pN⟩
  let c (Z : G.FullSubcategory × G.FullSubcategory) (hZ : P' Z) :
      B.obj (L.obj Z.1, L.obj Z.2) ≅ A.obj (L.obj Z.1, L.obj Z.2) :=
    d.app Z ≪≫ (@asIso _ _ _ _ (q.map (α.app (Z.1.obj, Z.2.obj)))
      (hi Z.1.obj Z.2.obj Z.1.property Z.2.property hZ.1 hZ.2)).symm ≪≫
      rH.app (ι.obj Z.1, ι.obj Z.2)
  have hc (Z : G.FullSubcategory × G.FullSubcategory) (hZ : P' Z) :
      (c Z hZ).inv = (r.app Z).inv ≫ β.app Z ≫ (d.app Z).inv := by
    exact inverse_comparison _ _ _ _
  exact product_normalization G L M N P c
    (normalized_descent_comparison (L.prod L) (V.prod V) r d β (M, N) P' hp c hc)

private theorem finiteTor_of_iso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    {M N : DerivedCategory (integralTowerModules l E T)} (e : M ≅ N)
    (hM : finiteTorConstructibleIntegral l E T M) :
    finiteTorConstructibleIntegral l E T N := by
  refine ⟨(sfIntegralConstructible l E T).prop_of_iso e hM.1, ?_⟩
  obtain ⟨a, b, hab, h⟩ := hM.2
  refine ⟨a, b, hab, fun n ↦ ⟨(h n).1, ?_⟩⟩
  intro L P hL f hf hP A i hi
  exact (h n).2 L P
    (hL.map (fun j ↦ j ≪≫ ((scalarReductionDerivedExtension l E T n).mapIso e).symm))
    f hf hP A i hi

/-- Completion-to-ordinary tensor is fixed on every pair of good representatives.
Source: rational purity proof, tensor transpose
(blueprint: def-pur-canonical-purity-source-transports).
Proof: use flat K-flat resolutions of M and N and the preceding strict augmentation.
Naturality of that augmentation and the representative comparisons makes the result
independent of both resolutions and their isomorphisms. Every pair admits such
resolutions. This proves existence and uniqueness with the displayed normalization. -/
theorem tensorToOrdinary_existsUnique (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (M N : finiteTorConstructibleIntegralCategory l E T) :
    ∃! e : (integralCompletedTensor l E T).obj (M.obj,N.obj) ≅
        (ordinaryModel l E T).tensor.obj (M.obj,N.obj),
      ∀ (P Q : CochainComplex (integralTowerModules l E T) ℤ)
        (hP : integralOperationsGoodComplex l E T P)
        (hQ : integralOperationsGoodComplex l E T Q)
        (hM : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj P))
        (hN : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj Q))
        (eP : DerivedCategory.Q.obj P ≅ M.obj) (eQ : DerivedCategory.Q.obj Q ≅ N.obj),
        e = (integralCompletedTensor l E T).mapIso (Iso.prod eP.symm eQ.symm) ≪≫
          tensorToOrdinaryOnGood l E T P Q hP hQ hM hN ≪≫
          (ordinaryModel l E T).tensor.mapIso (Iso.prod eP eQ) := by
  unfold tensorToOrdinaryOnGood
  let G := integralOperationsGoodComplex l E T
  let H := proEtaleFlatRepresentatives T
    (completedIntegralCommRingSheafUnrestricted l E T)
  let q : CochainComplex (integralTowerModules l E T) ℤ ⥤
      DerivedCategory (integralTowerModules l E T) := DerivedCategory.Q
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E T) (.up ℤ)).inverseImage
    G.ι
  have : (G.ι ⋙ q).IsLocalization V :=
    integralOperationsGoodLocalization_isLocalization l E T
  exact tensor_comparison_from_augmentation G H (goodOrdinary l E T) q V
    (ordinaryModel l E T).tensor (integralCompletedTensor l E T)
    (ordinaryTotal l E T) (integralOperationsTensorComplexFunctor l E T)
    (ordinaryModel l E T).representative (integralCompletedTensorComparison l E T)
    (tensorAugmentation l E T) (finiteTorConstructibleIntegral l E T)
    (fun e h ↦ finiteTor_of_iso l E T e h) (tensorAugmentation_isIso l E T)
    M.obj N.obj M.property N.property

/-- The uniquely normalized comparison from completed to ordinary tensor.
Source: rational purity proof, tensor transpose
(blueprint: def-pur-canonical-purity-source-transports). -/
def tensorToOrdinary (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (M N : finiteTorConstructibleIntegralCategory l E T) :=
  (tensorToOrdinary_existsUnique l E T M N).exists.choose

end RationalSmoothPurityCanonical
end WeilConjectures
