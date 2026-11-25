/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Pur.PurSequenceOrdinaryFactorization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSequenceDirectEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitDerivedAdjunctionComparison

/-! # Coherent reduction and strict pullback tower core

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: def-pur-completed-pullback-tower-core).

## Main definitions

* `pullbackTensorOrdinaryReduction` and its adjunction fix coherent reduction.
* `pullbackTensorRoosModel` fixes the total-limit/Roos normalization.
* `pullbackTensorPullbackTower` fixes the strict finite-pullback tower comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

/-- Select the uniquely normalized object without repeating its predicate.
Source: classical unique choice (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorUniqueChoice {A : Sort*} {P : A → Prop} (h : ∃! x, P x) : A :=
  h.exists.choose

section RoosSign
open CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b w g
variable {B : Type a} [Category.{b} B] [Abelian B] [HasCountableProducts B]

private def pullbackCoconeFunctor : Arrow (CochainComplex B ℤ) ⥤ CochainComplex B ℤ where
  obj f := CochainComplex.mappingCocone f.hom
  map f := (shiftFunctor _ (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
      (fun j : ℤ ↦ ⟨j - 1, by change j - 1 + 1 = j; omega⟩) f)
  map_id f := by
    erw [HomologicalComplex.homotopyCofiber.mapArrowHom_id]
    exact (shiftFunctor _ (-1 : ℤ)).map_id _
  map_comp f g := by
    rw [HomologicalComplex.homotopyCofiber.mapArrowHom_comp, Functor.map_comp]

private def pullbackRoosArrow (negative : Bool) :
    CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ Arrow (CochainComplex B ℤ) where
  obj X := Arrow.mk (if negative then -ExactProductsRoos.difference.app X
    else ExactProductsRoos.difference.app X)
  map f := Arrow.homMk (ExactProductsRoos.product.map f) (ExactProductsRoos.product.map f)
    (by
      cases negative
      · exact ExactProductsRoos.difference.naturality f
      · change ExactProductsRoos.product.map f ≫ (-ExactProductsRoos.difference.app _) =
          (-ExactProductsRoos.difference.app _) ≫ ExactProductsRoos.product.map f
        rw [Preadditive.comp_neg, Preadditive.neg_comp]
        exact congrArg Neg.neg (ExactProductsRoos.difference.naturality f))
  map_id X := by apply Arrow.hom_ext <;> exact ExactProductsRoos.product.map_id X
  map_comp f g := by apply Arrow.hom_ext <;> exact ExactProductsRoos.product.map_comp f g

private def pullbackRoosSign : pullbackRoosArrow (B := B) false ≅ pullbackRoosArrow true :=
  NatIso.ofComponents (fun X ↦
    { hom := Arrow.homMk (𝟙 _) (-𝟙 _) (by simp [pullbackRoosArrow])
      inv := Arrow.homMk (𝟙 _) (-𝟙 _) (by simp [pullbackRoosArrow])
      hom_inv_id := by apply Arrow.hom_ext <;> simp
      inv_hom_id := by apply Arrow.hom_ext <;> simp }) (by
    intro X Y f
    apply Arrow.hom_ext <;> simp [pullbackRoosArrow])

private def pullbackRoosSignIso :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor (A := B) ≅ ExactProductsRoos.fibre :=
  Functor.isoWhiskerRight pullbackRoosSign pullbackCoconeFunctor

variable [HasLimitsOfShape ℕᵒᵖ B]
private def pullbackPositiveCondition (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain
          (ExactProductsRoos.ordinary.obj X) (ExactProductsRoos.product.obj X) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (ExactProductsRoos.inclusion.app X ≫ ExactProductsRoos.difference.app X) = 0 := by
  rw [ExactProductsRoos.inclusion_difference]
  simp

private def pullbackPositiveComparison (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :=
  CochainComplex.mappingCocone.lift (ExactProductsRoos.difference.app X)
    (ExactProductsRoos.inclusion.app X) 0 (pullbackPositiveCondition X)

private theorem pullbackZeroLift_f {M K L : CochainComplex B ℤ} (φ : K ⟶ L)
    (α : M ⟶ K)
    (h : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain M L (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ φ) = 0) (p : ℤ) :
    (CochainComplex.mappingCocone.lift φ α 0 h).f p = α.f p ≫
      HomologicalComplex.homotopyCofiber.inlX φ p (p + (-1))
        (by change p + (-1) + 1 = p; omega) := by
  simp only [CochainComplex.mappingCocone.lift,
    CochainComplex.mappingCocone.liftCocycle, CochainComplex.mappingCocone.liftCochain,
    CochainComplex.mappingCone.liftCochain,
    CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.inr, CochainComplex.HomComplex.Cochain.zero_comp,
    add_zero, CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
      _ _ _ _ p _ _ (p + (-1)) (by omega),
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.assoc]
  erw [Category.comp_id]

private theorem pullbackPositiveComparison_sign (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    pullbackPositiveComparison X ≫ pullbackRoosSignIso.hom.app X =
      ExactProductsRoos.comparison.app X := by
  ext p : 1
  dsimp only [HomologicalComplex.comp_f, pullbackPositiveComparison]
  rw [pullbackZeroLift_f, ExactProductsRoos.comparisonApp_f]
  dsimp only [pullbackRoosSignIso, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, pullbackCoconeFunctor, pullbackRoosSign,
    NatIso.ofComponents_hom_app, Functor.comp_map]
  rw [CochainComplex.shiftFunctor_map_f']
  dsimp only [pullbackRoosArrow]
  erw [Category.assoc, HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.inlX_desc_f]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
    Pi.zero_apply, zero_add, add_zero]
  erw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
  simp
  all_goals change p + -1 + 1 = p; omega

variable [HasExactLimitsOfShape (Discrete ℕ) B] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]

private theorem pullbackRoosComparison_exists :
    ∃ e : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective],
        e.hom.app I =
          (Functor.rightDerivedFunctorObjQIso (lim : (ℕᵒᵖ ⥤ B) ⥤ B) I).hom ≫
            DerivedCategory.Q.map (pullbackPositiveComparison I) := by
  let L : (ℕᵒᵖ ⥤ B) ⥤ B := lim
  let η : ExactProductsRoos.ordinary ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L.rightDerivedFunctor :=
    { app := L.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ L.rightDerivedFunctorUnitQ_naturality f }
  obtain ⟨e, he⟩ := ExactProductsRoos.comparisonIso L.rightDerivedFunctor η (by
    intro I hI
    letI := hI
    change IsIso (L.rightDerivedFunctorUnitQ I)
    rw [L.rightDerivedFunctorUnitQ_eq]
    infer_instance)
  let d := Functor.isoWhiskerRight pullbackRoosSignIso DerivedCategory.Q ≪≫ e
  refine ⟨d.symm, ?_⟩
  intro I hI
  have hn : DerivedCategory.Q.map (pullbackPositiveComparison I) ≫ d.hom.app I =
      η.app I := by
    change DerivedCategory.Q.map (pullbackPositiveComparison I) ≫
      DerivedCategory.Q.map (pullbackRoosSignIso.hom.app I) ≫ e.hom.app I = _
    rw [← DerivedCategory.Q.map_comp_assoc, pullbackPositiveComparison_sign]
    exact congrArg (fun z ↦ z.app I) he
  have hη : η.app I = (L.rightDerivedFunctorObjQIso I).inv :=
    L.rightDerivedFunctorUnitQ_eq I
  apply (cancel_mono (d.hom.app I)).1
  dsimp only [Iso.symm_hom]
  rw [Iso.inv_hom_id_app, Category.assoc, hn, hη, Iso.hom_inv_id]

private theorem pullbackRoosComparison_unique
    (e e' : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
    (h : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective],
      e.hom.app I = e'.hom.app I) : e = e' := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective X
  letI := hI
  letI := hq
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance
  have : IsIso ((DerivedCategory.Q ⋙
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor).map q) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have : IsIso ((HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q).map q) :=
    (NatIso.isIso_map_iff e q).1 inferInstance
  apply (cancel_mono ((HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q).map q)).1
  rw [← e.hom.naturality q, ← e'.hom.naturality q, h I]

end RoosSign

section CoherentSystems

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The sequence site's actual object and morphism universes are u+1 and u.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
instance (priority := 3000) pullbackTensorSequenceSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × W.ProEt) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The recorded coefficient reduction/limit adjunction and tensor models.
Source: Stacks 0941 and 07A6 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorCalculus (W : Scheme.{u}) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose

/-- Base change on the actual ringed sequence site.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorSequenceBase {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ℕ × Y.ProEt ⥤ ℕ × X.ProEt :=
  (𝟭 ℕ).prod (proEtaleBaseChange f)

/-- Base change preserves the vertical covering condition.
Source: Stacks 0941, 098K (blueprint: def-pur-completed-pullback-tower-core).
Proof: a vertical slice of a pulled-back sieve is the base change of its
vertical slice; pro-etale covers are stable under scheme base change. -/
@[instance] theorem pullbackTensorSequenceBase_continuous {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (pullbackTensorSequenceBase f).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) := by
  exact integralComparisonSequenceBaseChange_continuous f

/-- The sequence-ring map is fixed at every level by the constant-section map.
Source: Stacks 0941 and 0H7J (blueprint: def-pur-completed-pullback-tower-core).
Proof: take the existing constant-section morphism at every positive quotient.
Its naturality in quotient ring maps proves naturality also in the sequence
direction. These components define the ring-sheaf morphism; componentwise
extensionality proves uniqueness. -/
theorem pullbackTensorSequenceRing_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! ρ : coefficientSequenceCommRingSheaf l E Y ⟶
      ((pullbackTensorSequenceBase f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X),
      ∀ (n : ℕ) (U : Y.ProEt),
        HEq (ρ.hom.app (op (n,U)))
          ((coefficientProEtaleDirectRingMap.{u, u} f
            (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).hom.app
              (op U)) := by
  refine ⟨integralComparisonSequenceRingMap l E f, ?_, ?_⟩
  · intro n U
    rfl
  · intro ρ hρ
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact eq_of_heq (hρ V.unop.1 V.unop.2)

/-- The explicit levelwise constant-section components of the sequence ring map.
It is exported as irreducible at the end of this file, so that importers see
`pullbackTensorSequenceRing` as opaque as the former unique choice.
Source: Stacks 0941 and 0H7J (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorSequenceRingMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientSequenceCommRingSheaf l E Y ⟶
      ((pullbackTensorSequenceBase f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X) where
  hom :=
    { app := fun A ↦
        (coefficientProEtaleDirectRingMap.{u, u} f
          (CommRingCat.of (ULift.{u + 1}
            (finiteCoefficientRing l E (A.unop.1 + 1))))).hom.app (op A.unop.2)
      naturality := by
        intro A B g
        let ρ := (pullbackTensorSequenceRing_existsUnique l E f).exists.choose
        have hρ := (pullbackTensorSequenceRing_existsUnique l E f).exists.choose_spec
        have hA := eq_of_heq (hρ A.unop.1 A.unop.2)
        have hB := eq_of_heq (hρ B.unop.1 B.unop.2)
        change ρ.hom.app A = _ at hA
        change ρ.hom.app B = _ at hB
        exact (congrArg ((coefficientSequenceCommRingPresheaf l E Y).map g ≫ ·) hB).symm.trans
          ((ρ.hom.naturality g).trans (congrArg (· ≫ _) hA)) }

/-- The actual levelwise constant-section map on sequence rings.
Source: Stacks 0941 and 0H7J (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorSequenceRing {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientSequenceCommRingSheaf l E Y ⟶
      ((pullbackTensorSequenceBase f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X) :=
  pullbackTensorSequenceRingMap l E f

/-- Module direct image on the ringed sequence site, with the actual coefficient action.
Source: Stacks 03D1 and 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorSequenceDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.pushforward.{u + 1} (F := pullbackTensorSequenceBase f)
    (J := coefficientSequenceTopology (ProEt.topology Y))
    (K := coefficientSequenceTopology (ProEt.topology X))
    (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E Y))
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E X))
    ⟨Functor.whiskerRight (pullbackTensorSequenceRing l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Module Kan extension followed by sheafification is left adjoint to this direct image.
Source: Stacks 03D2 and 0941 (blueprint: def-pur-completed-pullback-tower-core).
Proof: pass to a small model in coefficient universe u + 1. The free module
presheaf presentation constructs inverse image with extension of scalars;
module sheafification gives its adjunction. Transport back to the stated
sequence sites. The right adjoint and its coefficient map are the displayed ones. -/
@[instance] theorem pullbackTensorSequenceDirect_rightAdjoint {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (pullbackTensorSequenceDirect l E f).IsRightAdjoint := by
  change (integralComparisonSequenceDirectImage l E f).IsRightAdjoint
  exact integralComparisonSequenceDirectImage_isRightAdjoint l E f

/-- Canonical module inverse image on coefficient systems, retaining its adjunction.
Source: Stacks 03D2 and 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorSequenceInverse {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorSequenceDirect l E f).leftAdjoint

/-- The defining sequence-module adjunction, including its unit.
Source: Stacks 03D2 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorSequenceAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceInverse l E f ⊣ pullbackTensorSequenceDirect l E f :=
  Adjunction.ofIsRightAdjoint _

/-- Sequence inverse image is additive and exact, without a boundedness restriction.
Source: Stacks 03D2, 0941 (blueprint: def-pur-completed-pullback-tower-core).
Proof: on every vertical slice the ring map is the constant-ring comparison,
so inverse image is the exact ordinary constant-coefficient inverse image.
Kernels and cokernels of sequence modules are levelwise, giving exactness.
The additive adjunction criterion gives additivity. -/
theorem pullbackTensorSequenceInverse_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceInverse l E f).Additive ∧
      PreservesFiniteLimits (pullbackTensorSequenceInverse l E f) ∧
      PreservesFiniteColimits (pullbackTensorSequenceInverse l E f) := by
  have heq : pullbackTensorSequenceInverse l E f =
      integralComparisonSequencePullback l E f := by
    rfl
  rw [heq]
  exact integralComparisonSequencePullback_exact l E f

/-- The additive structure of sequence inverse image.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
instance pullbackTensorSequenceInverse_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceInverse l E f).Additive :=
  (pullbackTensorSequenceInverse_exact l E f).1

/-- Finite-limit preservation of sequence inverse image.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
instance pullbackTensorSequenceInverse_limits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (pullbackTensorSequenceInverse l E f) :=
  (pullbackTensorSequenceInverse_exact l E f).2.1

/-- Finite-colimit preservation of sequence inverse image.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
instance pullbackTensorSequenceInverse_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pullbackTensorSequenceInverse l E f) :=
  (pullbackTensorSequenceInverse_exact l E f).2.2

/-- The unbounded derived inverse image on the coherent sequence category itself.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorSequenceDerived {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientSequenceDerived l E Y ⥤ coefficientSequenceDerived l E X :=
  (pullbackTensorSequenceInverse l E f).mapDerivedCategory

/-- The ordinary inverse limit of a coefficient system with its completed scalar action.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorOrdinaryLimit (W : Scheme.{u}) :
    coefficientSequenceModules l E W ⥤ integralTowerModules l E W :=
  coefficientSequenceRestriction l E W ⋙ lim

/-- Ordinary coherent reduction is left adjoint to the specified ordinary limit.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core).
Proof: send a completed module P to the system of its actual quotients
B_n tensor P. The quotient units form a map P to the limit after scalar
restriction. A system map from these quotients is equivalent, by the ordinary
scalar-extension adjunctions and their compatibility, to a map P to that limit.
This is the required natural Hom bijection. -/
@[instance] theorem pullbackTensorOrdinaryLimit_rightAdjoint (W : Scheme.{u}) :
    (pullbackTensorOrdinaryLimit l E W).IsRightAdjoint := by
  have : IsGrothendieckAbelian.{u + 1} (coefficientSequenceModules l E W) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _
  have hev (n : ℕ) : PreservesLimitsOfSize.{u + 1, u + 1}
      (coefficientSequenceEvaluation l E W n) := by
    unfold coefficientSequenceEvaluation
    have := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u + 1}
      (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm)
    infer_instance
  have hres (n : ℕ) : (scalarReductionRestriction l E W n).IsRightAdjoint :=
    (scalarReductionExtension_adjunction l E W n).choose.isRightAdjoint
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (coefficientSequenceRestriction l E W) := by
    apply preservesLimits_of_evaluation
    intro n
    rw [coefficientSequenceRestriction_evaluation]
    have := hev n.unop
    have := hres n.unop
    infer_instance
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (pullbackTensorOrdinaryLimit l E W) := by
    unfold pullbackTensorOrdinaryLimit
    infer_instance
  exact isRightAdjoint_of_preservesLimits_of_isCoseparating
    (isCoseparator_coseparator (coefficientSequenceModules l E W)) _

/-- Ordinary coherent reduction, fixed by its adjunction to the ordinary limit.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorOrdinaryReduction (W : Scheme.{u}) :=
  (pullbackTensorOrdinaryLimit l E W).leftAdjoint

/-- The ordinary reduction/limit adjunction and its canonical quotient units.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorOrdinaryAdjunction (W : Scheme.{u}) :
    pullbackTensorOrdinaryReduction l E W ⊣ pullbackTensorOrdinaryLimit l E W :=
  Adjunction.ofIsRightAdjoint _

/-- Additivity of ordinary coherent reduction and ordinary limit.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core).
Proof: restriction, limits and the scalar quotient functors are additive.
Alternatively use the additive-adjunction criterion for the displayed adjunction. -/
theorem pullbackTensorOrdinary_additive (W : Scheme.{u}) :
    (pullbackTensorOrdinaryReduction l E W).Additive ∧
      (pullbackTensorOrdinaryLimit l E W).Additive := by
  have : (pullbackTensorOrdinaryLimit l E W).Additive := by
    have := coefficientConstantTowerLimitAdditive l E W
    change (coefficientSequenceRestriction l E W ⋙ lim).Additive
    infer_instance
  exact ⟨(pullbackTensorOrdinaryAdjunction l E W).left_adjoint_additive, inferInstance⟩

/-- The additive structure on ordinary coherent reduction.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
instance pullbackTensorOrdinaryReduction_additive (W : Scheme.{u}) :
    (pullbackTensorOrdinaryReduction l E W).Additive :=
  (pullbackTensorOrdinary_additive l E W).1

/-- The additive structure on the ordinary limit with completed coefficients.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
instance pullbackTensorOrdinaryLimit_additive (W : Scheme.{u}) :
    (pullbackTensorOrdinaryLimit l E W).Additive :=
  (pullbackTensorOrdinary_additive l E W).2

/-- The ordinary limit with its completed-module source recorded explicitly.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorConstantLimit (W : Scheme.{u}) :
    (ℕᵒᵖ ⥤ integralTowerModules l E W) ⥤ integralTowerModules l E W := lim

/-- The additive structure of the explicitly typed constant-tower limit.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tower-core). -/
instance pullbackTensorConstantLimit_additive (W : Scheme.{u}) :
    (pullbackTensorConstantLimit l E W).Additive :=
  coefficientConstantTowerLimitAdditive l E W

/-- The standard derived localization instance for the completed-module tower category.
Source: Stacks 05RU (blueprint: def-pur-completed-pullback-tower-core). -/
instance pullbackTensorTowerHasDerived (W : Scheme.{u}) :
    HasDerivedCategory (ℕᵒᵖ ⥤ integralTowerModules l E W) := HasDerivedCategory.standard _

/-- The additive finite inverse-image functor with both size parameters fixed.
Source: Stacks 03D2 (blueprint: def-pur-completed-pullback-tower-core). -/
instance pullbackTensorLevelAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (integralOperationsLevelPullback l E f n).Additive :=
  integralOperationsLevelPullback_additive l E f n

/-- K-injective resolutions in the explicitly sized tower category.
Source: Stacks 079P and 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
instance pullbackTensorTowerKInjectives (W : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ integralTowerModules l E W) :=
  coefficientConstantTowersKInjectives l E W

/-- The standard localization functor for completed-coefficient towers.
Source: Stacks 05RU (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorTowerQ (W : Scheme.{u}) :=
  @DerivedCategory.Q (ℕᵒᵖ ⥤ integralTowerModules l E W) _ _ (HasDerivedCategory.standard _)

/-- The canonical comparison from ordinary limit to the already specified total limit.
Source: Stacks 0941 and 08TC (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorLimitUnit (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    DerivedCategory.Q.obj
        (((pullbackTensorOrdinaryLimit l E W).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj C) :=
  letI := pullbackTensorConstantLimit_additive l E W
  DerivedCategory.Q.map
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (coefficientSequenceRestriction l E W ⋙
        (pullbackTensorConstantLimit l E W)))
      (.up ℤ)).inv.app C) ≫
  (pullbackTensorConstantLimit l E W).rightDerivedFunctorUnitQ
      (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C) ≫
  (coefficientConstantTowerLimit l E W).map
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C)

private theorem pullbackSequenceRing_map_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceRing l E f = integralComparisonSequenceRingMap l E f := by
  rfl

/-- The ordinary scalar-extension adjunction of the actual finite reduction.
Source: Stacks 06YY (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorFiniteAdjunction (W : Scheme.{u}) (n : ℕ) :
    unrestrictedIntegralReductionFunctor l E W n ⊣ scalarReductionRestriction l E W n :=
  (scalarReductionExtension_adjunction l E W n).choose

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf in
private theorem pullbackTensorReductionEvaluation_normalization (W : Scheme.{u})
    (O : PurSequenceOrdinaryAdjoints l E W) (n : ℕ) (M : integralTowerModules l E W) :
    (pullbackTensorFiniteAdjunction l E W n).homEquiv M _
        (((O.tensor n).symm ≪≫ Functor.isoWhiskerRight
          ((O.adjunction.ofNatIsoRight O.limit).leftAdjointUniq
            (pullbackTensorOrdinaryAdjunction l E W))
          (coefficientSequenceEvaluation l E W n)).hom.app M) =
      (pullbackTensorOrdinaryAdjunction l E W).unit.app M ≫
        limit.π ((coefficientSequenceRestriction l E W).obj
          ((pullbackTensorOrdinaryReduction l E W).obj M)) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
          ((pullbackTensorOrdinaryReduction l E W).obj M) := by
  let adj := O.adjunction.ofNatIsoRight O.limit
  let a := adj.leftAdjointUniq (pullbackTensorOrdinaryAdjunction l E W)
  have h := O.transpose M ((pullbackTensorOrdinaryReduction l E W).obj M)
    (O.adjunction.homEquiv _ _ (a.hom.app M)) n
  rw [Equiv.symm_apply_apply] at h
  have ha := Adjunction.homEquiv_leftAdjointUniq_hom_app
    adj (pullbackTensorOrdinaryAdjunction l E W) M
  change adj.homEquiv _ _ (a.hom.app M) = _ at ha
  dsimp only [adj] at ha
  erw [Adjunction.homEquiv_ofNatIsoRight_apply] at ha
  rw [O.projection_limit] at h
  refine h.trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k ↦ k ≫
      (limit.π ((coefficientSequenceRestriction l E W).obj
        ((pullbackTensorOrdinaryReduction l E W).obj M)) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
          ((pullbackTensorOrdinaryReduction l E W).obj M))) ha)

/-- Evaluation of ordinary coherent reduction is the actual quotient extension,
with its adjunction unit rather than a chosen component map.
Source: Stacks 0941 and 06YY (blueprint: def-pur-completed-pullback-tower-core).
Proof: take the adjoint of the ordinary reduction/limit unit followed by its
nth limit projection. The scalar-extension adjunction identifies this map with
B_n tensor P to the nth coherent quotient. The section formula sends 1 tensor x
to 1 tensor x, giving an isomorphism. Naturality follows from the two adjunctions;
the displayed transpose determines all components uniquely. -/
theorem pullbackTensorReductionEvaluation_existsUnique (W : Scheme.{u}) (n : ℕ) :
    ∃! e : unrestrictedIntegralReductionFunctor l E W n ≅
      pullbackTensorOrdinaryReduction l E W ⋙ coefficientSequenceEvaluation l E W n,
      ∀ M : integralTowerModules l E W,
        (pullbackTensorFiniteAdjunction l E W n).homEquiv M _ (e.hom.app M) =
          (pullbackTensorOrdinaryAdjunction l E W).unit.app M ≫
            limit.π ((coefficientSequenceRestriction l E W).obj
              ((pullbackTensorOrdinaryReduction l E W).obj M)) (op n) ≫
            (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
              ((pullbackTensorOrdinaryReduction l E W).obj M) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨O, _⟩ := purSequenceOrdinaryFactorization l E W
    let adj := O.adjunction.ofNatIsoRight O.limit
    let a := adj.leftAdjointUniq (pullbackTensorOrdinaryAdjunction l E W)
    let e := (O.tensor n).symm ≪≫
      Functor.isoWhiskerRight a (coefficientSequenceEvaluation l E W n)
    have he (M : integralTowerModules l E W) :
        (pullbackTensorFiniteAdjunction l E W n).homEquiv M _ (e.hom.app M) =
          (pullbackTensorOrdinaryAdjunction l E W).unit.app M ≫
            limit.π ((coefficientSequenceRestriction l E W).obj
              ((pullbackTensorOrdinaryReduction l E W).obj M)) (op n) ≫
            (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
              ((pullbackTensorOrdinaryReduction l E W).obj M) :=
      pullbackTensorReductionEvaluation_normalization l E W O n M

    refine ⟨e, he, ?_⟩
    intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ((pullbackTensorFiniteAdjunction l E W n).homEquiv M _).injective
    exact (he' M).trans (he M).symm

/-- The unit-normalized quotient evaluation isomorphism.
Source: Stacks 0941 and 06YY (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorReductionEvaluation (W : Scheme.{u}) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorReductionEvaluation_existsUnique l E W n)

attribute [local implicit_reducible] pullbackTensorSequenceBase
  integralComparisonSequenceBaseChange integralComparisonSequenceDirectImage in
/-- Direct image on sequences commutes with evaluation by the identity on sections.
Source: Stacks 03D1 and 0941 (blueprint: def-pur-completed-pullback-tower-core).
Proof: both functors evaluate M at (n, f-basechange U) with scalar action through
the same constant-section coefficient map. The identity section maps give the
natural isomorphism. Sectionwise extensionality proves uniqueness. -/
theorem pullbackTensorSequenceDirectEvaluation_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! e : pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        coefficientProEtaleModuleDirectImage.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))),
      ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
        (x : ((coefficientSequenceEvaluation l E Y n).obj
          ((pullbackTensorSequenceDirect l E f).obj M)).val.obj (op U)),
        HEq ((e.hom.app M).val.app (op U) x) x := by
  unfold pullbackTensorSequenceDirect
  rw [pullbackSequenceRing_map_eq]
  exact integralComparisonSequenceDirectEvaluation_existsUnique l E f n

/-- The sectionwise direct-image/evaluation comparison.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorSequenceDirectEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n)

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceBase pullbackTensorSequenceDirect pullbackTensorSequenceInverse
  pullbackTensorSequenceAdjunction coefficientSequenceEvaluation integralOperationsLevelPullback in
/-- The inverse-image/evaluation comparison is the adjunction mate of the
sectionwise direct-image comparison.
Source: Stacks 03D2 and 0941 (blueprint: def-pur-completed-pullback-tower-core).
Proof: transpose the displayed map under the finite module adjunction. The two
inverse-image functors are computed levelwise, so the resulting natural map is
invertible. The adjunction Hom bijection fixes its components and proves uniqueness. -/
theorem pullbackTensorSequenceInverseEvaluation_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! e : coefficientSequenceEvaluation l E Y n ⋙
        integralOperationsLevelPullback l E f n ≅
      pullbackTensorSequenceInverse l E f ⋙ coefficientSequenceEvaluation l E X n,
      ∀ M : coefficientSequenceModules l E Y,
        (coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).homEquiv
            ((coefficientSequenceEvaluation l E Y n).obj M) _ (e.hom.app M) =
          (coefficientSequenceEvaluation l E Y n).map
            ((pullbackTensorSequenceAdjunction l E f).unit.app M) ≫
          (pullbackTensorSequenceDirectEvaluation l E f n).hom.app
            ((pullbackTensorSequenceInverse l E f).obj M) := by
  let adj := pullbackTensorSequenceAdjunction l E f
  let adjn := coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
  let d := pullbackTensorSequenceDirectEvaluation l E f n
  have : ((𝟭 ℕ).prod (proEtaleBaseChange f)).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) :=
    pullbackTensorSequenceBase_continuous f
  have : IsIso ((mateEquiv adj adjn).symm d.hom).natTrans :=
    SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E Y))
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E X)) n
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (pullbackTensorSequenceRing l E f))
      (integralCoefficientSheaf l E Y n) (integralCoefficientSheaf l E X n)
      (coefficientSequenceEvaluationRing_eq l E Y n)
      (coefficientSequenceEvaluationRing_eq l E X n)
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (coefficientProEtaleDirectRingMap.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))))
      (pullbackTensorSequenceInverse l E f) (integralOperationsLevelPullback l E f n)
      adj adjn d
  let e := asIso ((mateEquiv adj adjn).symm d.hom).natTrans
  have he (M : coefficientSequenceModules l E Y) :
      adjn.homEquiv _ _ (e.hom.app M) =
        (coefficientSequenceEvaluation l E Y n).map (adj.unit.app M) ≫
          d.hom.app ((pullbackTensorSequenceInverse l E f).obj M) := by
    rw [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm adj adjn d.hom M).symm
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (adjn.homEquiv _ _).injective
  exact (he' M).trans (he M).symm

/-- The canonical mate comparing sequence inverse image with finite inverse image.
Source: Stacks 03D2 and 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorSequenceInverseEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n)

/-- Reordering a restricted sequence complex into a tower preserves its finite slices.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorRestrictedLevel (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
      (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)).obj
        (op n)) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceRestriction l E W ⋙
      (evaluation ℕᵒᵖ (integralTowerModules l E W)).obj (op n))) (.up ℤ)).app C ≪≫
  (NatIso.mapHomologicalComplex
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) (.up ℤ)).app C ≪≫
  ((Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceEvaluation l E W n ⋙
      scalarReductionRestriction l E W n)) (.up ℤ)).app C).symm

/-- The actual complex-to-tower reordering after completed scalar restriction.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorRestrictedTower (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)

/-- The canonical augmentation of the ordinary inverse limit into its strict Roos model.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorRoosAugmentation (W : Scheme.{u})
    (P : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    ((pullbackTensorConstantLimit l E W).mapHomologicalComplex (.up ℤ)).obj P ⟶
        ∏ᶜ (fun n : ℕ ↦
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n)) :=
  Pi.lift (fun n ↦ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app P)

/-- The strict limit projections give a zero homotopy for the Roos augmentation.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tower-core).
Proof: after every product projection the composite with 1-s is the difference
of consecutive compatible limit projections. It vanishes. The zero cochain has
zero differential, which is the displayed mapping-cocone lifting condition. -/
theorem pullbackTensorRoosAugmentation_condition (W : Scheme.{u})
    (P : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain
        (((pullbackTensorConstantLimit l E W).mapHomologicalComplex (.up ℤ)).obj P)
        (∏ᶜ fun n : ℕ ↦
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (pullbackTensorRoosAugmentation l E W P ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦
              (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n))
            (integralOperationsTowerStep
              (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P))) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hz : pullbackTensorRoosAugmentation l E W P ≫
        towerTransitionEndomorphism
          (K := fun n : ℕ ↦
            (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n))
          (integralOperationsTowerStep
            (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P)) = 0 := by
      apply Pi.hom_ext
      intro n
      simp only [towerTransitionEndomorphism, Preadditive.comp_sub, Preadditive.sub_comp,
        Category.comp_id,
        towerProductShift, Category.assoc, Pi.lift_comp_π_assoc, pullbackTensorRoosAugmentation,
        Pi.lift_comp_π, zero_comp]
      apply sub_eq_zero.mpr
      apply HomologicalComplex.hom_ext
      intro k
      exact (limit.w (P.X k) (homOfLE (Nat.le_succ n)).op).symm
    rw [hz]
    simp only [CochainComplex.HomComplex.δ_zero, zero_add,
      CochainComplex.HomComplex.Cochain.ofHom_zero]

/-- The specified (limit-projections, zero) chain map into Cone(1-s)[-1].
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorRoosUnit (W : Scheme.{u})
    (P : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    ((pullbackTensorConstantLimit l E W).mapHomologicalComplex (.up ℤ)).obj P ⟶
      integralOperationsRoos
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P) :=
  letI : Abelian (integralTowerModules l E W) := inferInstance
  letI : HasCountableProducts (integralTowerModules l E W) := inferInstance
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n))
      (integralOperationsTowerStep
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P)))
    (pullbackTensorRoosAugmentation l E W P) 0
    (pullbackTensorRoosAugmentation_condition l E W P)

/-- The canonical total-limit/Roos isomorphism is fixed on K-injectives by the
actual right-derived comparison and the specified zero-homotopy augmentation.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tower-core).
Proof: exact products identify the Roos construction with the total derived
limit. For a K-injective tower the ordinary limit computes that derived limit;
the displayed formula fixes the comparison there. Resolve any tower complex
by a K-injective one. Naturality and invertibility on quasi-isomorphisms extend
this formula uniquely, giving the natural isomorphism on all tower complexes. -/
theorem pullbackTensorRoosModel_existsUnique (W : Scheme.{u}) :
    ∃! e : pullbackTensorTowerQ l E W ⋙ coefficientConstantTowerLimit l E W ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) [I.IsKInjective],
        e.hom.app I =
          (Functor.rightDerivedFunctorObjQIso
            (pullbackTensorConstantLimit l E W) I).hom ≫
          DerivedCategory.Q.map (pullbackTensorRoosUnit l E W I) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let A := integralTowerModules l E W
    letI : IsGrothendieckAbelian.{u + 1} A :=
      SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _
    letI : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) := by
      have := diagrams_isGrothendieckAbelian A (AsSmall.{u + 1} ℕᵒᵖ)
      exact IsGrothendieckAbelian.of_equivalence
        (Equivalence.congrLeft (AsSmall.equiv (C := ℕᵒᵖ)).symm)
    letI : HasExactLimitsOfShape (Discrete ℕ) A :=
      integralOperationsExactProducts l E W
    obtain ⟨e, he⟩ := pullbackRoosComparison_exists (B := A)
    refine ⟨e, he, ?_⟩
    intro e' he'
    apply pullbackRoosComparison_unique (B := A) e' e
    intro I hI
    exact (he' I).trans (he I).symm

/-- The uniquely normalized total-limit/Roos model, including both cone coordinates.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorRoosModel (W : Scheme.{u}) :=
  pullbackTensorUniqueChoice (pullbackTensorRoosModel_existsUnique l E W)

attribute [reducible] pullbackTensorUniqueChoice

private theorem pullbackTensorSequenceRing_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceRing l E f = integralComparisonSequenceRingMap l E f := by
  rfl

/-- The ordinary quotient evaluation comparison on cochain complexes.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorReductionEvaluationComplex (W : Scheme.{u}) (n : ℕ) :
    unrestrictedIntegralFiniteComplex l E W n ≅
      (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ) ⋙
        (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (pullbackTensorReductionEvaluation l E W n) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pullbackTensorOrdinaryReduction l E W ⋙
        coefficientSequenceEvaluation l E W n)) (.up ℤ)).symm

/-- The unit-normalized inverse-image evaluation comparison on cochain complexes.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorInverseEvaluationComplex {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI := integralOperationsLevelPullback_additive l E f n
    (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ) ⋙
      (integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ) ≅
    (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    exact letI := integralOperationsLevelPullback_additive l E f n
      letI := pullbackTensorSequenceInverse_additive l E f
      letI := coefficientSequenceEvaluation_additive l E X n
      letI := coefficientSequenceEvaluation_additive l E Y n
      Functor.mapHomologicalComplexCompIso
        (Iso.refl (coefficientSequenceEvaluation l E Y n ⋙
          integralOperationsLevelPullback l E f n)) (.up ℤ) ≪≫
      NatIso.mapHomologicalComplex (pullbackTensorSequenceInverseEvaluation l E f n) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (pullbackTensorSequenceInverse l E f ⋙
          coefficientSequenceEvaluation l E X n)) (.up ℤ)).symm

/-- Each slice of the coherent pullback model is the recorded strict finite pullback.
Source: Stacks 0941 and 099N (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorPullbackTowerLevel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    (pullbackTensorRestrictedTower l E X
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
        (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P))).obj
          (op n) ≅
      ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n) :=
  pullbackTensorRestrictedLevel l E X _ n ≪≫
  ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).mapIso
    ((pullbackTensorInverseEvaluationComplex l E f n).app
      (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
  ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).mapIso
    (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).mapIso
      ((pullbackTensorReductionEvaluationComplex l E Y n).app P).symm)

section TowerComparisonProof
attribute [local irreducible] pullbackTensorReductionEvaluationComplex
  pullbackTensorInverseEvaluationComplex pullbackTensorPullbackTowerLevel
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf

private theorem pullbackTensor_identityFactors
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : B ⥤ A) (G : C ⥤ B) {U : A} {V : B} {W Z : C}
    (a : U ⟶ F.obj V) (b : V ⟶ G.obj W) (c : W ⟶ Z) :
    a ≫ F.map b ≫ F.map (G.map c) =
      𝟙 _ ≫ a ≫ 𝟙 _ ≫ F.map (𝟙 V) ≫ F.map b ≫ F.map (𝟙 (G.obj W)) ≫
        F.map (G.map (𝟙 W)) ≫ F.map (G.map c) := by
  simp

private theorem pullbackTensorReductionEvaluation_eq (W : Scheme.{u})
    (O : PurSequenceOrdinaryAdjoints l E W) (n : ℕ) :
    pullbackTensorReductionEvaluation l E W n = (O.tensor n).symm ≪≫
      Functor.isoWhiskerRight
        ((O.adjunction.ofNatIsoRight O.limit).leftAdjointUniq
          (pullbackTensorOrdinaryAdjunction l E W))
        (coefficientSequenceEvaluation l E W n) := by
  apply (pullbackTensorReductionEvaluation_existsUnique l E W n).unique
  · exact (pullbackTensorReductionEvaluation_existsUnique l E W n).exists.choose_spec
  · exact pullbackTensorReductionEvaluation_normalization l E W O n

private theorem pullbackTensorOrdinaryModel_transition (W : Scheme.{u})
    (O : PurSequenceOrdinaryAdjoints l E W) (M : scalarReductionSource l E W)
    {m n : ℕ} (h : n ≤ m) :
    (coefficientSequenceTransition l E W h).app
        ((pullbackTensorOrdinaryReduction l E W).obj M) ≫
      (normalizedDVRModuleRes l E W h).map
        ((pullbackTensorReductionEvaluation l E W n).inv.app M) =
      (pullbackTensorReductionEvaluation l E W m).inv.app M ≫
        (coefficientOrdinaryQuotient l E W h).app M := by
  rw [pullbackTensorReductionEvaluation_eq l E W O n,
    pullbackTensorReductionEvaluation_eq l E W O m]
  let a := (O.adjunction.ofNatIsoRight O.limit).leftAdjointUniq
    (pullbackTensorOrdinaryAdjunction l E W)
  change (coefficientSequenceTransition l E W h).app _ ≫
    (normalizedDVRModuleRes l E W h).map
      ((coefficientSequenceEvaluation l E W n).map (a.inv.app M) ≫
        (O.tensor n).hom.app M) =
    ((coefficientSequenceEvaluation l E W m).map (a.inv.app M) ≫
      (O.tensor m).hom.app M) ≫ (coefficientOrdinaryQuotient l E W h).app M
  rw [Functor.map_comp, ← Category.assoc]
  have hn := (coefficientSequenceTransition l E W h).naturality (a.inv.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc] using
    congrArg ((coefficientSequenceEvaluation l E W m).map (a.inv.app M) ≫ ·)
      (O.tensor_transition M m n h)

private theorem pullbackTensorOrdinaryModel_unit_tensor (W : Scheme.{u})
    (M : scalarReductionSource l E W) (n : ℕ) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    (((pullbackTensorOrdinaryAdjunction l E W).unit.app M ≫
      limit.π ((coefficientSequenceRestriction l E W).obj
        ((pullbackTensorOrdinaryReduction l E W).obj M)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        ((pullbackTensorOrdinaryReduction l E W).obj M) ≫
      (scalarReductionRestriction l E W n).map
        ((pullbackTensorReductionEvaluation l E W n).inv.app M)).val.app V) x =
      unrestrictedIntegralTensorSection l E W n M V 1 x := by
  have h := (pullbackTensorReductionEvaluation_existsUnique l E W n).exists.choose_spec M
  change (pullbackTensorFiniteAdjunction l E W n).homEquiv M _
    ((pullbackTensorReductionEvaluation l E W n).hom.app M) = _ at h
  have hu : (pullbackTensorOrdinaryAdjunction l E W).unit.app M ≫
      limit.π ((coefficientSequenceRestriction l E W).obj
        ((pullbackTensorOrdinaryReduction l E W).obj M)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app _ ≫
      (scalarReductionRestriction l E W n).map
        ((pullbackTensorReductionEvaluation l E W n).inv.app M) =
      (pullbackTensorFiniteAdjunction l E W n).unit.app M := by
    have hh := congrArg (fun z ↦ z ≫ (scalarReductionRestriction l E W n).map
      ((pullbackTensorReductionEvaluation l E W n).inv.app M)) h
    rw [Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id] at hh
    erw [← Category.assoc, ← Category.assoc]
    exact hh.symm.trans
      (Category.comp_id ((pullbackTensorFiniteAdjunction l E W n).unit.app M))
  exact (congrArg (fun z ↦ z.val.app V x) hu).trans
    (CompletionUnit.finite_unit_tensor l E W M n V x)

private def pullbackTensorOrdinaryModel (W : Scheme.{u})
    (O : PurSequenceOrdinaryAdjoints l E W) : CompletionUnit.OrdinaryModel l E W where
  tensor := pullbackTensorOrdinaryReduction l E W
  evaluation n := (pullbackTensorReductionEvaluation l E W n).symm
  transition M {_ _} h := pullbackTensorOrdinaryModel_transition l E W O M h
  adjunction := pullbackTensorOrdinaryAdjunction l E W
  unit_tensor := pullbackTensorOrdinaryModel_unit_tensor l E W
  limitComparison := Functor.isoWhiskerLeft (CompletionUnit.tower l E W)
    (CompletionUnit.termwiseLimitComparison l E W)
  limitComparison_projection I n p :=
    CompletionUnit.termwiseLimitComparison_projection l E W
      ((CompletionUnit.tower l E W).obj I) n p

attribute [local implicit_reducible] pullbackTensorOrdinaryModel pullbackTensorOrdinaryLimit
  pullbackTensorConstantLimit
  coefficientConstantTowerLimit coefficientSequenceLimit pullbackTensorOrdinaryReduction
  pullbackTensorOrdinaryAdjunction integralOperationsGoodLocalization
  HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex

attribute [local irreducible] pullbackTensorCalculus

/-- On flat K-flat complexes the adjunction mate of the ordinary quotient unit
is the canonical comparison with coherent derived reduction. The formula takes
place in the system derived category, before evaluation.
Source: Stacks 0941, 07A6 and 09T5 (blueprint: def-pur-completed-pullback-tower-core).
Proof: use the ordinary quotient model with the selected reduction functor and
its adjunction. Transport the canonical right-derived limit unit through the
termwise limit comparison. Cancelling that comparison with its inverse gives
exactly pullbackTensorLimitUnit. The existing fixed-calculus derived comparison
is invertible on flat-term K-flat complexes. Its Hom equation at the identity
gives the displayed transpose. Injectivity of that Hom equivalence and natural-
transformation extensionality prove uniqueness. -/
theorem pullbackTensorReductionModel_existsUnique (W : Scheme.{u}) :
    ∃! e : integralOperationsGoodLocalization l E W ⋙
        (pullbackTensorCalculus l E W).reduction ≅
      (integralOperationsGoodComplex l E W).ι ⋙
        (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q,
      ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        ((pullbackTensorCalculus l E W).adjunction.homEquiv
          (DerivedCategory.Q.obj P.obj)
          (DerivedCategory.Q.obj
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
              P.obj))) (e.hom.app P) =
        DerivedCategory.Q.map
          (((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).unit.app
            P.obj) ≫
          pullbackTensorLimitUnit l E W
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
              P.obj) := by
  obtain ⟨O, _⟩ := purSequenceOrdinaryFactorization l E W
  let M := pullbackTensorOrdinaryModel l E W O
  let F := pullbackTensorConstantLimit l E W
  let c := CompletionUnit.termwiseLimitComparison l E W
  let ν : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W :=
    { app I := F.rightDerivedFunctorUnitQ I
      naturality {I J} a := F.rightDerivedFunctorUnitQ_naturality a }
  let η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W :=
    (Functor.isoWhiskerRight c.symm DerivedCategory.Q).hom ≫ ν
  have hη (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [I.IsKInjective] : η.app I ≫ (F.rightDerivedFunctorObjQIso I).hom =
      DerivedCategory.Q.map (c.inv.app I) := by
    dsimp only [η, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Iso.symm_hom, Functor.whiskerRight_app, ν]
    rw [Functor.rightDerivedFunctorUnitQ_eq, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hu (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
      (CompletionUnit.systemLimitUnit l E W M η).app C =
        pullbackTensorLimitUnit l E W C := by
    change DerivedCategory.Q.map
        (c.hom.app ((CompletionUnit.tower l E W).obj C)) ≫
      η.app ((CompletionUnit.tower l E W).obj C) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C) = _
    dsimp only [η, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Iso.symm_hom, Functor.whiskerRight_app, ν]
    rw [Category.assoc, ← DerivedCategory.Q.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    have hcomp : (Functor.mapHomologicalComplexCompIso
        (Iso.refl (coefficientSequenceRestriction l E W ⋙
          pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app C = 𝟙 _ := rfl
    simp only [pullbackTensorLimitUnit, hcomp]
    erw [CategoryTheory.Functor.map_id, Category.id_comp] <;> rfl
  obtain ⟨_, ε, _, hε, _, hhom⟩ :=
    CompletionUnit.fixedDerivedComparison l E W (pullbackTensorCalculus l E W) M c
      (CompletionUnit.termwiseLimitComparison_projection l E W) η hη
  let e : integralOperationsGoodLocalization l E W ⋙
      (pullbackTensorCalculus l E W).reduction ≅
      (integralOperationsGoodComplex l E W).ι ⋙
        (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦
      @asIso _ _ _ _ (ε.app P.obj) (hε P.obj P.property.1 P.property.2))
      (fun {_ _} f ↦ ε.naturality f.hom)
  have he (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      ((pullbackTensorCalculus l E W).adjunction.homEquiv _ _) (e.hom.app P) =
        DerivedCategory.Q.map
          (((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).unit.app
            P.obj) ≫
          pullbackTensorLimitUnit l E W
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
              P.obj) := by
    have hh := hhom P.obj ((M.quotient l E W).obj P.obj) (𝟙 _)
    simp only [CategoryTheory.Functor.map_id, Adjunction.homEquiv_id] at hh
    rw [hu] at hh
    erw [Category.comp_id] at hh
    exact hh
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply ((pullbackTensorCalculus l E W).adjunction.homEquiv _ _).injective
  exact (he' P).trans (he P).symm

/-- The uniquely adjunction-normalized coherent reduction model.
Source: Stacks 0941 and 09T5 (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorReductionModel (W : Scheme.{u}) :=
  pullbackTensorUniqueChoice (pullbackTensorReductionModel_existsUnique l E W)

private theorem pullbackTensorInverseEvaluationComplex_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorInverseEvaluationComplex l E f n =
      (letI := integralOperationsLevelPullback_additive l E f n
       letI := pullbackTensorSequenceInverse_additive l E f
       letI := coefficientSequenceEvaluation_additive l E X n
       letI := coefficientSequenceEvaluation_additive l E Y n
       Functor.mapHomologicalComplexCompIso
         (Iso.refl (coefficientSequenceEvaluation l E Y n ⋙
           integralOperationsLevelPullback l E f n)) (.up ℤ) ≪≫
       NatIso.mapHomologicalComplex
         (pullbackTensorSequenceInverseEvaluation l E f n) (.up ℤ) ≪≫
       (Functor.mapHomologicalComplexCompIso
         (Iso.refl (pullbackTensorSequenceInverse l E f ⋙
           coefficientSequenceEvaluation l E X n)) (.up ℤ)).symm) := by
  unfold pullbackTensorInverseEvaluationComplex
  rfl

private theorem pullbackTensorDirectEvaluation_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) : pullbackTensorSequenceDirectEvaluation l E f n =
      OrdinaryTowerProof.directEvaluation l E f n := by
  apply (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).unique
  · exact (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose_spec
  · exact OrdinaryTowerProof.directEvaluation_sections l E f n

private theorem pullbackTensorInverseEvaluation_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) : pullbackTensorSequenceInverseEvaluation l E f n =
      OrdinaryTowerProof.inverseEvaluation l E f n := by
  apply (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).unique
  · exact (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose_spec
  · intro M
    rw [pullbackTensorDirectEvaluation_eq]
    erw [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
      (coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))))
      (OrdinaryTowerProof.directEvaluation l E f n).hom M).symm

attribute [local irreducible] pullbackTensorOrdinaryReduction pullbackTensorOrdinaryAdjunction
  pullbackTensorReductionEvaluation pullbackTensorSequenceDirectEvaluation
  pullbackTensorSequenceInverseEvaluation

attribute [local implicit_reducible] pullbackTensorSequenceBase pullbackTensorSequenceDirect
  pullbackTensorSequenceInverse
  pullbackTensorSequenceAdjunction coefficientSequenceEvaluation integralOperationsLevelPullback
  integralComparisonSequencePullback integralComparisonSequenceDirectImage
  integralComparisonSequenceBaseChange
  unrestrictedIntegralReductionFunctor pullbackTensorRestrictedTower
  integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence

private theorem pullbackTensor_components_unique {D : Type*} [Category D]
    (F G : ℕᵒᵖ ⥤ D) (c : ∀ n : ℕ, F.obj (op n) ≅ G.obj (op n))
    (hc : ∀ {i j : ℕᵒᵖ} (g : i ⟶ j),
      F.map g ≫ (c j.unop).hom = (c i.unop).hom ≫ G.map g) :
    ∃! e : F ≅ G, ∀ n : ℕ, e.app (op n) = c n := by
  let e : F ≅ G := NatIso.ofComponents (fun n ↦ c n.unop) hc
  have he (n : ℕ) : e.app (op n) = c n := NatIso.ofComponents.app _ _ _
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext n
  exact congrArg Iso.hom ((he' n.unop).trans (he n.unop).symm)

attribute [local irreducible] OrdinaryTowerProof.moduleLevel OrdinaryTowerProof.inverseEvaluation

private theorem pullbackTensor_comparison_degree {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) (i : ℤ) :
    (((OrdinaryTowerProof.comparison l E f M).hom.app P).app (op n)).f i =
      (OrdinaryTowerProof.moduleLevel l E f M n).hom.app (P.X i) := by
  exact OrdinaryTowerProof.comparison_hom_app_f l E f M P n i

attribute [local irreducible] OrdinaryTowerProof.comparison

private theorem pullbackTensorPullbackTower_degree {X Y : Scheme.{u}}
    (f : X ⟶ Y) (O : PurSequenceOrdinaryAdjoints l E Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ) :
    (OrdinaryTowerProof.moduleLevel l E f
      (pullbackTensorOrdinaryModel l E Y O) n).hom.app (P.X i) =
        (pullbackTensorPullbackTowerLevel l E f P n).hom.f i := by
  let M := pullbackTensorOrdinaryModel l E Y O
  change (OrdinaryTowerProof.moduleLevel l E f M n).hom.app (P.X i) = _
  have ht : M.tensor = pullbackTensorOrdinaryReduction l E Y := rfl
  have heval : M.evaluation n = (pullbackTensorReductionEvaluation l E Y n).symm := rfl
  simp only [OrdinaryTowerProof.moduleLevel, pullbackTensorPullbackTowerLevel,
    pullbackTensorRestrictedLevel, pullbackTensorInverseEvaluationComplex_eq,
    pullbackTensorReductionEvaluationComplex, pullbackTensorInverseEvaluation_eq]
  simp only [ht, heval, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    NatIso.mapHomologicalComplex_hom_app_f,
    NatIso.mapHomologicalComplex_inv_app_f,
    Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.comp_f, Iso.refl_hom, Iso.refl_inv,
    Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_comp, Category.assoc] <;>
    exact pullbackTensor_identityFactors
      (scalarReductionRestriction l E X n) (integralOperationsLevelPullback l E f n)
      ((eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app
        ((pullbackTensorSequenceInverse l E f).obj
          ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i))))
      ((OrdinaryTowerProof.inverseEvaluation l E f n).inv.app
        ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i)))
      ((pullbackTensorReductionEvaluation l E Y n).inv.app (P.X i))

private theorem pullbackTensorPullbackTower_component {X Y : Scheme.{u}}
    (f : X ⟶ Y) (O : PurSequenceOrdinaryAdjoints l E Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    (((OrdinaryTowerProof.comparison l E f
      (pullbackTensorOrdinaryModel l E Y O)).hom.app P).app (op n)) =
        (pullbackTensorPullbackTowerLevel l E f P n).hom := by
  apply HomologicalComplex.hom_ext
  intro i
  exact (pullbackTensor_comparison_degree l E f
    (pullbackTensorOrdinaryModel l E Y O) P n i).trans
      (pullbackTensorPullbackTower_degree l E f O P n i)

/-- The slice comparisons form one strict tower isomorphism, fixed at every level.
Source: Stacks 0941 and 099N (blueprint: def-pur-completed-pullback-tower-core).
Proof: the quotient maps and inverse-image maps were fixed by their ordinary
adjunction units. Apply the two adjunction Hom bijections: both composites
across a quotient transition become the same quotient unit. Thus the level
comparisons commute strictly with transitions. They form a tower isomorphism;
its prescribed components give uniqueness by natural-transformation extensionality. -/
theorem pullbackTensorPullbackTower_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ∃! e : pullbackTensorRestrictedTower l E X
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
        (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P,
      ∀ n : ℕ, e.app (op n) = pullbackTensorPullbackTowerLevel l E f P n := by
  obtain ⟨O, _⟩ := purSequenceOrdinaryFactorization l E Y
  let M := pullbackTensorOrdinaryModel l E Y O
  refine pullbackTensor_components_unique _ _
    (fun n ↦ pullbackTensorPullbackTowerLevel l E f P n) ?_
  intro i j g
  have h := ((OrdinaryTowerProof.comparison l E f M).hom.app P).naturality g
  change _ ≫ (((OrdinaryTowerProof.comparison l E f M).hom.app P).app j) =
    (((OrdinaryTowerProof.comparison l E f M).hom.app P).app i) ≫ _ at h
  rw [pullbackTensorPullbackTower_component l E f O P j.unop,
    pullbackTensorPullbackTower_component l E f O P i.unop] at h
  exact h

end TowerComparisonProof

attribute [local irreducible] pullbackTensorCalculus pullbackTensorOrdinaryModel

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward false in
set_option synthInstance.maxSize 768 in
/-- The unit-normalized strict pullback tower comparison.
Source: Stacks 0941 and 099N (blueprint: def-pur-completed-pullback-tower-core). -/
def pullbackTensorPullbackTower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  pullbackTensorUniqueChoice (pullbackTensorPullbackTower_existsUnique l E f P)

end CoherentSystems

-- Consumers normalize this map by its section equation before comparing adjoints;
-- `pullbackTensorSequenceRing` itself stays semireducible, so their local hints remain valid.
attribute [irreducible] pullbackTensorSequenceRingMap

end WeilConjectures
