/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage

import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.HomCongr
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-! # Internal Hom and evaluation under coefficient-site isomorphisms

Source: Stacks Project, Modules on Sites, Tag 0GMX; the derived and completed
normalization is the enhancement in the node's sixteen proof steps, supplying
main-20261015 theorem-poincare-duality-frobenius--2 Steps 1, 2, 4 and 5.
(blueprint: lem-pod-derived-automorphism-hom-evaluation).

Finite inputs are unbounded. Integral inputs have exactly the recorded
Hom-constructibility condition. Completed inverse image is constructed from
all coefficient projections; its comparison with tower pullback uses the
actual completion unit and a resolution-normalized total-limit comparison.
System maps and their identities are stated before evaluation or realization.
Rational maps are localized; algebraically closed maps use every common stage.

## Main definitions

* `podFiniteHomComparison`: transpose of pullback of finite evaluation.
* `podPartialHomComparison`: the same construction on permitted Hom pairs.
* `podCompletedRingMap`: completed coefficient transport from all projections.
* `podCompletedToTower`: the completion-unit comparison with tower pullback.

## Main statements

* `derivedAutomorphismHomEvaluation`: the four evaluation-defined natural isomorphisms.
* The `*_laws`, `*_shift`, `*_comp` declarations give all coherent identities.
* `podHomReductionSquare`: the actual system-level reduction square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard

/-- Partial closed data on precisely the pairs for which internal Hom is permitted.
Source: Stacks 08J9 and the integral qualification in the node
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
structure PodPartialClosed {C : Type a} [Category.{b} C] [Preadditive C]
    (T : C × C ⥤ C) (J : ObjectProperty (Cᵒᵖ × C)) (H : J.FullSubcategory ⥤ C) where
  /-- Tensor-Hom transposition on every permitted pair. -/
  transpose : ∀ (L : C) (P : J.FullSubcategory),
    (T.obj (L, P.obj.1.unop) ⟶ P.obj.2) ≃+ (L ⟶ H.obj P)
  /-- Naturality in the tensor parameter. -/
  parameter_naturality : ∀ (L L' : C) (P : J.FullSubcategory) (f : L' ⟶ L)
    (h : T.obj (L, P.obj.1.unop) ⟶ P.obj.2),
    transpose L' P (T.map (Prod.mkHom f (𝟙 _)) ≫ h) = f ≫ transpose L P h

/-- Evaluation is the inverse transpose of the identity, with Hom first.
The node's argument-first convention is obtained by the canonical Koszul symmetry.
Source: Stacks 08J9 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def PodPartialClosed.evaluation {C : Type a} [Category.{b} C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (P : J.FullSubcategory) :
    T.obj (H.obj P, P.obj.1.unop) ⟶ P.obj.2 :=
  (S.transpose _ P).symm (𝟙 _)

/-- The genuine functor on permitted Hom pairs induced by pullback.
Source: Stacks 0GMX (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podPairPullback {C : Type a} {D : Type c} [Category.{b} C] [Category.{d} D]
    (F : C ⥤ D) (J : ObjectProperty (Cᵒᵖ × C)) (K : ObjectProperty (Dᵒᵖ × D))
    (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj)) :
    J.FullSubcategory ⥤ K.FullSubcategory :=
  K.lift (J.ι ⋙ F.op.prod F) h

/-- The evaluation-defined comparison, using the specified tensor comparison.
Its data are a closed transpose, never an arbitrary chosen isomorphism.
Source: Stacks 0GMX (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podPartialHomComparison {C : Type a} {D : Type c}
    [Category.{b} C] [Category.{d} D] [Preadditive C] [Preadditive D]
    {TC : C × C ⥤ C} {TD : D × D ⥤ D}
    {J : ObjectProperty (Cᵒᵖ × C)} {K : ObjectProperty (Dᵒᵖ × D)}
    {HC : J.FullSubcategory ⥤ C} {HD : K.FullSubcategory ⥤ D}
    (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
    (F : C ⥤ D) (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj))
    (μ : ∀ L M : C, F.obj (TC.obj (L, M)) ≅ TD.obj (F.obj L, F.obj M))
    (P : J.FullSubcategory) :
    F.obj (HC.obj P) ⟶ HD.obj ((podPairPullback F J K h).obj P) :=
  SD.transpose _ _ ((μ (HC.obj P) P.obj.1.unop).inv ≫ F.map (SC.evaluation P))

/-- The displayed naturality, evaluation, and transposition identities, together
with invertibility of the evaluation-defined map. All arrows are in the stated
category itself, including when that category is a derived system category.
Source: Stacks 0GMX, node proof steps 3--5
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
structure PodPartialHomCompatibility {C : Type a} {D : Type c}
    [Category.{b} C] [Category.{d} D] [Preadditive C] [Preadditive D]
    {TC : C × C ⥤ C} {TD : D × D ⥤ D}
    {J : ObjectProperty (Cᵒᵖ × C)} {K : ObjectProperty (Dᵒᵖ × D)}
    {HC : J.FullSubcategory ⥤ C} {HD : K.FullSubcategory ⥤ D}
    (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
    (F : C ⥤ D) (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj))
    (μ : ∀ L M : C, F.obj (TC.obj (L, M)) ≅ TD.obj (F.obj L, F.obj M)) : Prop where
  /-- The canonical comparison is invertible on exactly the permitted pairs. -/
  isIso : ∀ P, IsIso (podPartialHomComparison SC SD F h μ P)
  /-- Naturality includes arbitrary arrows of the actual input category. -/
  naturality : ∀ (P Q : J.FullSubcategory) (f : P ⟶ Q),
    F.map (HC.map f) ≫ podPartialHomComparison SC SD F h μ Q =
      podPartialHomComparison SC SD F h μ P ≫ HD.map ((podPairPullback F J K h).map f)
  /-- The evaluation square, written with Hom first in the tensor. -/
  evaluation : ∀ P : J.FullSubcategory,
    (μ (HC.obj P) P.obj.1.unop).hom ≫
      TD.map (Prod.mkHom (podPartialHomComparison SC SD F h μ P) (𝟙 _)) ≫
        SD.evaluation ((podPairPullback F J K h).obj P) = F.map (SC.evaluation P)
  /-- Preservation of every transpose, with the inverse tensor comparison. -/
  transpose : ∀ (L : C) (P : J.FullSubcategory)
    (f : TC.obj (L, P.obj.1.unop) ⟶ P.obj.2),
    SD.transpose _ _ ((μ L P.obj.1.unop).inv ≫ F.map f) =
      F.map (SC.transpose L P f) ≫ podPartialHomComparison SC SD F h μ P

-- Closed-adjunction calculations are independent of sites and coefficient models.
section ClosedComparisonCalculus
universe w z
variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
  {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
  (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
  (F : C ⥤ D) (μ : SC.tensor ⋙ F ≅ F.prod F ⋙ SD.tensor)

private theorem uncurry_eq (L M N : C) (f : L ⟶ HC.obj (op M, N)) :
    (SC.transpose L M N).symm f =
      SC.tensor.map (Prod.mkHom f (𝟙 M)) ≫ SC.evaluation M N := by
  let := SC.monoidal
  simpa only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensorRight,
    MonoidalCategory.tensorLeft, MonoidalCategory.curriedTensor, Functor.flip,
    Functor.comp_map, Functor.id_map, Prod.sectR, MonoidalCategory.tensor_obj, Functor.comp_obj,
    MonoidalCategory.tensor_map,
    MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
    (SC.adjunction M).homEquiv_symm_apply L N f

private theorem eval_map (M M' N N' : C) (a : M' ⟶ M) (b : N ⟶ N') :
    SC.tensor.map (Prod.mkHom (HC.map (Prod.mkHom a.op b)) (𝟙 M')) ≫
      SC.evaluation M' N' =
    SC.tensor.map (Prod.mkHom (𝟙 _) a) ≫ SC.evaluation M N ≫ b := by
  let := SC.monoidal
  have hb := (SC.adjunction M').counit.naturality b
  have hb' : SC.tensor.map (Prod.mkHom (HC.map (Prod.mkHom (𝟙 (op M')) b))
      (𝟙 M')) ≫ SC.evaluation M' N' = SC.evaluation M' N ≫ b := by
    simpa only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
      CoefficientClosedStructure.tensor, MonoidalCategory.tensorRight,
      MonoidalCategory.tensorLeft, MonoidalCategory.curriedTensor, Functor.flip,
      Functor.comp_map, Functor.id_map, Prod.sectR, MonoidalCategory.tensor_obj, Functor.comp_obj,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using
      hb
  have ha := SC.evaluation_naturality M M' N a
  have ha' : SC.tensor.map (Prod.mkHom (HC.map (Prod.mkHom a.op (𝟙 N))) (𝟙 M')) ≫
      SC.evaluation M' N = SC.tensor.map (Prod.mkHom (𝟙 _) a) ≫
        SC.evaluation M N := by
    simpa only [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
      MonoidalCategory.tensorRight, MonoidalCategory.tensorLeft,
      MonoidalCategory.curriedTensor, Functor.flip, MonoidalCategory.tensor_obj, Functor.comp_obj,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using
      ha
  have hp : Prod.mkHom a.op b =
      Prod.mkHom a.op (𝟙 N) ≫ Prod.mkHom (𝟙 (op M')) b := by simp
  rw [hp, HC.map_comp]
  have ht : Prod.mkHom
      (HC.map (Prod.mkHom a.op (𝟙 N)) ≫ HC.map (Prod.mkHom (𝟙 (op M')) b))
      (𝟙 M') = Prod.mkHom (HC.map (Prod.mkHom a.op (𝟙 N))) (𝟙 M') ≫
        Prod.mkHom (HC.map (Prod.mkHom (𝟙 (op M')) b)) (𝟙 M') := by simp
  rw [ht, SC.tensor.map_comp, Category.assoc, hb', ← Category.assoc, ha', Category.assoc]

private theorem transpose_transport (L M N : C)
    (b : SC.tensor.obj (L, M) ⟶ N) :
    SD.transpose _ _ _ (μ.inv.app (L, M) ≫ F.map b) =
      F.map (SC.transpose L M N b) ≫
        SD.transpose _ _ _ (μ.inv.app (HC.obj (op M, N), M) ≫
          F.map (SC.evaluation M N)) := by
  let := SD.monoidal
  let t := SC.transpose L M N b
  have ht : SC.tensor.map (Prod.mkHom t (𝟙 M)) ≫ SC.evaluation M N = b := by
    rw [← uncurry_eq]
    exact (SC.transpose L M N).symm_apply_apply b
  have hn := μ.inv.naturality (Prod.mkHom t (𝟙 M))
  change SD.tensor.map (Prod.mkHom (F.map t) (F.map (𝟙 M))) ≫
      μ.inv.app (HC.obj (op M, N), M) =
    μ.inv.app (L, M) ≫ F.map (SC.tensor.map (Prod.mkHom t (𝟙 M))) at hn
  rw [F.map_id] at hn
  have h := (SD.adjunction (F.obj M)).homEquiv_naturality_left (F.map t)
    (μ.inv.app (HC.obj (op M, N), M) ≫ F.map (SC.evaluation M N))
  have h' : SD.transpose _ _ _
      (SD.tensor.map (Prod.mkHom (F.map t) (𝟙 (F.obj M))) ≫
        (μ.inv.app (HC.obj (op M, N), M) ≫ F.map (SC.evaluation M N))) =
      F.map t ≫ SD.transpose _ _ _
        (μ.inv.app (HC.obj (op M, N), M) ≫ F.map (SC.evaluation M N)) := by
    simpa only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
      CoefficientClosedStructure.tensor, MonoidalCategory.tensorRight,
      MonoidalCategory.tensorLeft, MonoidalCategory.curriedTensor, Functor.flip,
      Functor.comp_map, Functor.id_map, Prod.sectR, MonoidalCategory.tensor_obj, Functor.comp_obj,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using
      h
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, ht] at h'
  exact h'

private theorem uncurry_comp (L L' M N : C) (f : L' ⟶ L)
    (h : L ⟶ HC.obj (op M, N)) :
    (SC.transpose L' M N).symm (f ≫ h) =
      SC.tensor.map (Prod.mkHom f (𝟙 M)) ≫ (SC.transpose L M N).symm h := by
  rw [uncurry_eq, uncurry_eq]
  have hp : Prod.mkHom (f ≫ h) (𝟙 M) =
      Prod.mkHom f (𝟙 M) ≫ Prod.mkHom h (𝟙 M) := by simp
  rw [hp, SC.tensor.map_comp, Category.assoc]

private theorem uncurry_hom_map (L M M' N N' : C)
    (h : L ⟶ HC.obj (op M, N)) (a : M' ⟶ M) (b : N ⟶ N') :
    (SC.transpose L M' N').symm (h ≫ HC.map (Prod.mkHom a.op b)) =
      SC.tensor.map (Prod.mkHom (𝟙 L) a) ≫ (SC.transpose L M N).symm h ≫ b := by
  rw [uncurry_comp, uncurry_eq, eval_map, uncurry_eq]
  simp only [← Category.assoc, ← SC.tensor.map_comp]
  congr 2
  congr 1
  apply Prod.hom_ext <;> simp

private def closedComparison (M N : C) :
    F.obj (HC.obj (op M, N)) ⟶ HD.obj (op (F.obj M), F.obj N) :=
  SD.transpose _ _ _ (μ.inv.app (HC.obj (op M, N), M) ≫ F.map (SC.evaluation M N))

private theorem comparison_naturality (M M' N N' : C) (a : M' ⟶ M) (b : N ⟶ N') :
    F.map (HC.map (Prod.mkHom a.op b)) ≫ closedComparison SC SD F μ M' N' =
      closedComparison SC SD F μ M N ≫ HD.map (Prod.mkHom (F.map a).op (F.map b)) := by
  apply (SD.transpose _ (F.obj M') (F.obj N')).symm.injective
  rw [uncurry_comp, uncurry_hom_map]
  simp only [closedComparison, Equiv.symm_apply_apply]
  have hn₁ := μ.inv.naturality
    (Prod.mkHom (HC.map (Prod.mkHom a.op b)) (𝟙 M'))
  have hn₂ := μ.inv.naturality (Prod.mkHom (𝟙 (HC.obj (op M, N))) a)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn₁ hn₂
  rw [F.map_id] at hn₁ hn₂
  rw [← Category.assoc, hn₁, Category.assoc, ← F.map_comp, eval_map,
    F.map_comp, F.map_comp, ← Category.assoc, ← Category.assoc, ← hn₂]
  simp only [Category.assoc]

private theorem comparison_evaluation (M N : C) :
    μ.hom.app (HC.obj (op M, N), M) ≫
      SD.tensor.map (Prod.mkHom (closedComparison SC SD F μ M N) (𝟙 (F.obj M))) ≫
        SD.evaluation (F.obj M) (F.obj N) = F.map (SC.evaluation M N) := by
  rw [← uncurry_eq]
  simp only [closedComparison, Equiv.symm_apply_apply, Iso.hom_inv_id_app_assoc]

private theorem comparison_isIso [F.IsEquivalence] (M N : C) :
    IsIso (closedComparison SC SD F μ M N) := by
  -- On objects in the essential image, postcomposition is the closed Hom bijection.
  have hL (L : C) : Function.Bijective
      (fun x : F.obj L ⟶ F.obj (HC.obj (op M, N)) ↦
        x ≫ closedComparison SC SD F μ M N) := by
    let e : (L ⟶ HC.obj (op M, N)) ≃
        (F.obj L ⟶ HD.obj (op (F.obj M), F.obj N)) :=
      (SC.transpose L M N).symm.trans
        ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
          ((Iso.homCongr (μ.app (L, M)) (Iso.refl (F.obj N))).trans
            (SD.transpose _ _ _)))
    have he (x : L ⟶ HC.obj (op M, N)) :
        e x = F.map x ≫ closedComparison SC SD F μ M N := by
      dsimp only [e, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk,
        Functor.FullyFaithful.homEquiv, Iso.refl_hom]
      rw [Category.comp_id]
      change SD.transpose _ _ _ (μ.inv.app (L, M) ≫
        F.map ((SC.transpose L M N).symm x)) = _
      rw [transpose_transport, Equiv.apply_symm_apply]
      rfl
    have hbij : Function.Bijective
        (fun x : L ⟶ HC.obj (op M, N) ↦
          F.map x ≫ closedComparison SC SD F μ M N) := by
      simpa only [← he] using e.bijective
    constructor
    · intro x y hxy
      obtain ⟨x₀, rfl⟩ := F.map_surjective x
      obtain ⟨y₀, rfl⟩ := F.map_surjective y
      exact congrArg F.map (hbij.1 hxy)
    · intro y
      obtain ⟨x, hx⟩ := hbij.2 y
      exact ⟨F.map x, hx⟩
  -- Transfer the bijection to arbitrary test objects using essential surjectivity.
  apply isIso_of_yoneda_map_bijective
  intro T
  let e := F.objObjPreimageIso T
  constructor
  · intro x y hxy
    apply (cancel_epi e.hom).mp
    apply (hL (F.objPreimage T)).1
    simpa only [Category.assoc] using congrArg (fun z ↦ e.hom ≫ z) hxy
  · intro y
    obtain ⟨x, hx⟩ := (hL (F.objPreimage T)).2 (e.hom ≫ y)
    refine ⟨e.inv ≫ x, ?_⟩
    change (e.inv ≫ x) ≫ closedComparison SC SD F μ M N = y
    change x ≫ closedComparison SC SD F μ M N = e.hom ≫ y at hx
    rw [Category.assoc, hx, Iso.inv_hom_id_assoc]

end ClosedComparisonCalculus

section Finite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The finite unbounded comparison: transpose of pullback of ordinary evaluation.
Source: Stacks 0GMX, node proof steps 3--5
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteHomComparison (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finiteDerivedPullback l E n g).obj
        ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) ⟶
      (finiteIntrinsicDerivedInternalHom l E X n).obj
        (op ((finiteDerivedPullback l E n g).obj M),
          (finiteDerivedPullback l E n g).obj N) :=
  (finiteIntrinsicTranspose l E X n) _ _ _
    ((canonicalFinitePullbackTensor l E g n
      ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) M).inv ≫
      (finiteDerivedPullback l E n g).map (finiteIntrinsicEvaluation l E Y n M N))

private def finiteComparisonTensor (n : ℕ) :
    finiteIntrinsicDerivedTensor l E Y n ⋙ finiteDerivedPullback l E n g ≅
      (finiteDerivedPullback l E n g).prod (finiteDerivedPullback l E n g) ⋙
        finiteIntrinsicDerivedTensor l E X n :=
  finitePullbackTensorConstructionIso l E g n

omit [IsIso g] in
private theorem finiteComparison_eq (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    closedComparison (finiteIntrinsicClosed l E Y n) (finiteIntrinsicClosed l E X n)
      (finiteDerivedPullback l E n g) (finiteComparisonTensor l E g n) M N =
        podFiniteHomComparison l E g n M N := by
  rfl

-- Preserve the published isomorphism-instance binder, although naturality needs no equivalence.
set_option linter.unusedSectionVars false in
/-- Naturality of the finite comparison in both inputs: the naturality clause of
`podFiniteHomComparison_laws`.
Source: Stacks 0GMX; node lem-pod-derived-automorphism-hom-evaluation, steps 1--2.
Proof: both sides are maps into an internal Hom of the target; compare their
transposes. Parameter naturality of the transposition turns the left side into
the transpose of `T(F H(a,b), 1)` followed by `μ⁻¹` and `F(ev)`; naturality of
`μ` and dinaturality of evaluation, `T(H(a,b),1) ≫ ev = T(1,a) ≫ ev ≫ b`, make it
`T(1, F a) ≫ μ⁻¹ ≫ F(ev) ≫ F b`. The right side transposes to
`T(1, F a) ≫ T(c,1) ≫ ev ≫ F b`, and `T(c,1) ≫ ev = μ⁻¹ ≫ F(ev)` is the counit
identity of the transpose defining `c`. The transposes agree, so the maps agree.
(blueprint: stage3-pod-finite-hom-comparison-naturality). -/
theorem podFiniteHomComparison_naturality (n : ℕ)
    (M N M' N' : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)))
    (a : M' ⟶ M) (b : N ⟶ N') :
    (finiteDerivedPullback l E n g).map
        ((finiteIntrinsicDerivedInternalHom l E Y n).map (Prod.mkHom a.op b)) ≫
      podFiniteHomComparison l E g n M' N' =
    podFiniteHomComparison l E g n M N ≫
      (finiteIntrinsicDerivedInternalHom l E X n).map
        (Prod.mkHom ((finiteDerivedPullback l E n g).map a).op
          ((finiteDerivedPullback l E n g).map b)) := by
  simpa only [finiteComparison_eq] using
    comparison_naturality (finiteIntrinsicClosed l E Y n) (finiteIntrinsicClosed l E X n)
      (finiteDerivedPullback l E n g) (finiteComparisonTensor l E g n) M M' N N' a b

/-- The finite comparison's invertibility, evaluation equation and transpose
equation: the clauses of `podFiniteHomComparison_laws` other than naturality.
Source: Stacks 0GMX; node lem-pod-derived-automorphism-hom-evaluation, steps 1--2.
Proof: finite pullback is an equivalence: transport the fixed-coefficient
inverse-image equivalence through the intrinsic module realizations and then
pass to the ordinary unbounded derived category. For any test object in its
essential image, closed transposition, full faithfulness, and the canonical
tensor comparison identify postcomposition with `c` with a composite of Hom
bijections. Essential surjectivity gives this for every test object, so Yoneda
makes `c` invertible. No resolution comparison or boundedness is needed.
The evaluation equation is the counit identity of the transpose defining `c`,
precomposed with `μ`. For the transpose equation, transpose both sides: by
parameter naturality and naturality of `μ` the right side becomes
`μ⁻¹ ≫ F(T(b♯,1) ≫ ev) = μ⁻¹ ≫ F b`, which is the left side.
(blueprint: stage3-pod-finite-hom-comparison-remaining). -/
theorem podFiniteHomComparison_laws_remaining (n : ℕ) :
    (∀ M N, IsIso (podFiniteHomComparison l E g n M N)) ∧
    (∀ M N,
      (canonicalFinitePullbackTensor l E g n
        ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) M).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (podFiniteHomComparison l E g n M N) (𝟙 _)) ≫
      finiteIntrinsicEvaluation l E X n
        ((finiteDerivedPullback l E n g).obj M) ((finiteDerivedPullback l E n g).obj N) =
      (finiteDerivedPullback l E n g).map (finiteIntrinsicEvaluation l E Y n M N)) ∧
    (∀ L M N (b : (finiteIntrinsicDerivedTensor l E Y n).obj (L, M) ⟶ N),
      finiteIntrinsicTranspose l E X n _ _ _
        ((canonicalFinitePullbackTensor l E g n L M).inv ≫
          (finiteDerivedPullback l E n g).map b) =
      (finiteDerivedPullback l E n g).map (finiteIntrinsicTranspose l E Y n L M N b) ≫
        podFiniteHomComparison l E g n M N) := by
  have : (finiteDerivedPullback l E n g).IsEquivalence := by
    let A := finiteCoefficientRing l E (n + 1)
    let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    change (sfIntrinsicPullback A g).mapDerivedCategory.IsEquivalence
    have : (sfIntrinsicPullback A g).IsEquivalence := by
      unfold sfIntrinsicPullback sfIntrinsicTransport
      infer_instance
    infer_instance
  refine ⟨?_, ?_, ?_⟩
  · intro M N
    rw [← finiteComparison_eq]
    exact comparison_isIso (finiteIntrinsicClosed l E Y n) (finiteIntrinsicClosed l E X n)
      (finiteDerivedPullback l E n g) (finiteComparisonTensor l E g n) M N
  · intro M N
    exact comparison_evaluation (finiteIntrinsicClosed l E Y n) (finiteIntrinsicClosed l E X n)
      (finiteDerivedPullback l E n g) (finiteComparisonTensor l E g n) M N
  · intro L M N b
    exact transpose_transport (finiteIntrinsicClosed l E Y n) (finiteIntrinsicClosed l E X n)
      (finiteDerivedPullback l E n g) (finiteComparisonTensor l E g n) L M N b

/-- Finite unbounded internal Hom is preserved, naturally and with its actual evaluation
and transposition. Source: Stacks 0GMX, node proof steps 1--5.
Proof: the naturality clause is `podFiniteHomComparison_naturality`; the
invertibility, evaluation and transposition clauses are
`podFiniteHomComparison_laws_remaining`.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podFiniteHomComparison_laws (n : ℕ) :
    (∀ M N, IsIso (podFiniteHomComparison l E g n M N)) ∧
    (∀ M N M' N' (a : M' ⟶ M) (b : N ⟶ N'),
      (finiteDerivedPullback l E n g).map
          ((finiteIntrinsicDerivedInternalHom l E Y n).map (Prod.mkHom a.op b)) ≫
        podFiniteHomComparison l E g n M' N' =
      podFiniteHomComparison l E g n M N ≫
        (finiteIntrinsicDerivedInternalHom l E X n).map
          (Prod.mkHom ((finiteDerivedPullback l E n g).map a).op
            ((finiteDerivedPullback l E n g).map b))) ∧
    (∀ M N,
      (canonicalFinitePullbackTensor l E g n
        ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) M).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (podFiniteHomComparison l E g n M N) (𝟙 _)) ≫
        finiteIntrinsicEvaluation l E X n
          ((finiteDerivedPullback l E n g).obj M) ((finiteDerivedPullback l E n g).obj N) =
      (finiteDerivedPullback l E n g).map (finiteIntrinsicEvaluation l E Y n M N)) ∧
    (∀ L M N (b : (finiteIntrinsicDerivedTensor l E Y n).obj (L, M) ⟶ N),
      finiteIntrinsicTranspose l E X n _ _ _
        ((canonicalFinitePullbackTensor l E g n L M).inv ≫
          (finiteDerivedPullback l E n g).map b) =
      (finiteDerivedPullback l E n g).map (finiteIntrinsicTranspose l E Y n L M N b) ≫
        podFiniteHomComparison l E g n M N) := by
  have hr := podFiniteHomComparison_laws_remaining l E g n
  refine ⟨hr.1, ?_, hr.2.1, hr.2.2⟩
  intro M N M' N' a b
  exact podFiniteHomComparison_naturality l E g n M N M' N' a b
end Finite

end WeilConjectures
