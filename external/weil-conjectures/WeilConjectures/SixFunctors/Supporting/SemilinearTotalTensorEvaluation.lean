/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
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
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Total tensor evaluation on the ringed sequence site

Source: Stacks Project, Tags 03EK, 07A4 and 0941.
(blueprint: lem-coef-semilinear-total-tensor-evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe t u c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace WeilConjectures
open SemilinearSections
attribute [local irreducible] SemilinearSections.evaluation SheafOfModules.monoidalCategory
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive
private theorem totalIso_summand
    {A : Type t} [Category.{u} A] [Abelian A] [MonoidalCategory A]
    {D : Type t} [Category.{u} D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive A] [MonoidalPreadditive D]
    [HasCoproducts.{0} A] [HasCoproducts.{0} D]
    (L : A ⥤ D) [L.Additive]
    (μ : ∀ M N : A, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
    (hn : ∀ {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g))
    (V : D ⥤ A) (adj : L ⊣ V) (P Q : CochainComplex A ℤ)
    (p q k : ℤ) (h : p + q = k) :
    HomologicalComplex.ιMapBifunctor
        ((L.mapHomologicalComplex (.up ℤ)).obj P)
        ((L.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) p q k h ≫
      ((exactTensorTotalIso L μ hn V adj).hom.app (P, Q)).f k =
    (μ (P.X p) (Q.X q)).inv ≫
      L.map (HomologicalComplex.ιMapBifunctor P Q (curriedTensor A) (.up ℤ) p q k h) := by
  rw [exactTensorTotalIso_hom_app]
  exact HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := (L.mapHomologicalComplex (.up ℤ)).obj P)
    (K₂ := (L.mapHomologicalComplex (.up ℤ)).obj Q)
    (F := curriedTensor D) (c := .up ℤ) (j := k)
    (fun a b hab ↦ (μ (P.X a) (Q.X b)).inv ≫
      L.map (HomologicalComplex.ιMapBifunctor P Q (curriedTensor A) (.up ℤ) a b k hab))
    p q h

section Generic
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

@[irreducible] private def evaluationTotalIso (n : ℕ)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    ((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj
      ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ)).obj (P, Q)) ≅
    (totalTensor.{c, v, r} J (B n)).obj
      (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj P,
       ((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj Q) := by
  let F := SemilinearSections.evaluation J B τ n
  let G := WeilConjectures.SequenceModuleEvaluation.coFor J
    (ring (coefficientSequenceTopology J) (systemRing J B τ)) n (ring J (B n))
    (evaluation_ring J B τ n)
  let adj : F ⊣ G := by
    dsimp only [F]
    unfold SemilinearSections.evaluation
    exact WeilConjectures.SequenceModuleEvaluation.coForAdj J
      (ring (coefficientSequenceTopology J) (systemRing J B τ)) n (ring J (B n))
      (evaluation_ring J B τ n)
  let := SheafOfModules.monoidalCategory (systemRing J B τ)
  let := SheafOfModules.monoidalCategory (B n)
  let := SheafOfModules.isMonoidal_W_independentCoefficients (systemRing J B τ)
  let := SheafOfModules.isMonoidal_W_independentCoefficients (B n)
  let := SheafOfModules.cochainModulesPreadditive (systemRing J B τ)
  let := SheafOfModules.cochainModulesPreadditive (B n)
  let μ : ∀ M N : Systems.{c, v, max c v r} J B τ,
      F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N :=
    ordinaryEvaluationTensor.{c, v, r} J B τ n
  have hn : ∀ {M M' N N' : Systems.{c, v, max c v r} J B τ}
      (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (F.map f ⊗ₘ F.map g) := by
    intro M M' N N' f g
    exact evaluation_tensor_natural.{c, v, r} J B τ n f g
  let e := exactTensorTotalIso F μ hn G adj
  exact (e.app (P, Q)).symm

private theorem evaluationTotalIso_summand (n : ℕ)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (p q k : ℤ) (h : p + q = k) :
    tensorSummand.{c, v, r} J (B n)
        (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj P)
        (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj Q)
        p q k h ≫ ((evaluationTotalIso.{c, v, r} J B τ n P Q).inv.f k) =
      (ordinaryEvaluationTensor.{c, v, r} J B τ n (P.X p) (Q.X q)).inv ≫
        (SemilinearSections.evaluation J B τ n).map
          (tensorSummand.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ)
            P Q p q k h) := by
  unfold evaluationTotalIso
  exact totalIso_summand _ _ _ _ _ P Q p q k h

private theorem evaluationTotalIso_inv_generator (n : ℕ)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj (op (n, U.unop)))
    (y : (Q.X q).val.obj (op (n, U.unop))) :
    (((evaluationTotalIso.{c, v, r} J B τ n P Q).inv).f k).val.app U
      (coefficientTensorGenerator.{r, c, v} J (B n)
        (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj P)
        (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj Q)
        p q k h U (evalSection.{c, v, r} J B τ n (P.X p) U x)
        (evalSection.{c, v, r} J B τ n (Q.X q) U y)) =
      evalSection.{c, v, r} J B τ n _ U
        (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J)
          (systemRing J B τ) P Q p q k h (op (n, U.unop)) x y) := by
  have hs := evaluationTotalIso_summand.{c, v, r} J B τ n P Q p q k h
  have hh := congrArg (fun f ↦ f.val.app U
    (tensorSection.{c, v, r} J (B n)
      ((SemilinearSections.evaluation J B τ n).obj (P.X p))
      ((SemilinearSections.evaluation J B τ n).obj (Q.X q)) U
      (evalSection.{c, v, r} J B τ n (P.X p) U x)
      (evalSection.{c, v, r} J B τ n (Q.X q) U y))) hs
  change _ = ((SemilinearSections.evaluation J B τ n).map
      (tensorSummand.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ)
        P Q p q k h)).val.app U
      ((ordinaryEvaluationTensor.{c, v, r} J B τ n (P.X p) (Q.X q)).inv.val.app U
        (tensorSection.{c, v, r} J (B n) _ _ U
          (evalSection.{c, v, r} J B τ n (P.X p) U x)
          (evalSection.{c, v, r} J B τ n (Q.X q) U y))) at hh
  rw [evaluation_inv_pure_cast, evaluation_map_section] at hh
  exact hh

attribute [local irreducible] coefficientTensorGenerator coefficientTotalTensor

/-- Evaluation commutes with the unbounded total tensor, uniquely on its pure generators.
Source: Stacks 03EK, 07A4 and 0941
(blueprint: lem-coef-semilinear-total-tensor-evaluation).
Proof: use the identity-on-pure-sections ordinary evaluation tensor comparison.
Evaluation is a left adjoint, so it preserves the coproducts defining each total degree.
The inverse ordinary comparisons therefore give an invertible total chain comparison;
naturality handles both differentials and their signs. Its summand equation gives
its value on every pure generator. For uniqueness, precompose with its inverse,
then test maps out of the total tensor on every summand and every pure tensor.
No flatness, boundedness, or positivity beyond n being a natural number is used. -/
theorem semilinearTotalTensorEvaluation_existsUnique (n : ℕ)
    (F : Systems.{c, v, max c v r} J B τ ⥤ SemilinearSections.Mod.{c, v, max c v r} J (B n))
    [hF0 : F.PreservesZeroMorphisms] (hF : F = SemilinearSections.evaluation J B τ n)
    (σ : ∀ (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ),
      M.val.obj (op (n, U.unop)) →
        (F.obj M).val.obj U)
    (hσ : ∀ M U x, HEq (σ M U x) x)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    ∃! e : (F.mapHomologicalComplex (.up ℤ)).obj
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ)).obj (P, Q)) ≅
      (totalTensor.{c, v, r} J (B n)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P,
         (F.mapHomologicalComplex (.up ℤ)).obj Q),
      ∀ (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj (op (n, U.unop)))
        (y : (Q.X q).val.obj (op (n, U.unop))),
        (e.hom.f k).val.app U
          (σ _ U (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J)
            (systemRing J B τ) P Q p q k h (op (n, U.unop)) x y)) =
          coefficientTensorGenerator.{r, c, v} J (B n)
            ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q)
            p q k h U (σ (P.X p) U x) (σ (Q.X q) U y) := by
  subst F
  have hσ' (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
      (x : M.val.obj (op (n, U.unop))) :
      σ M U x = evalSection.{c, v, r} J B τ n M U x := by
    exact eq_of_heq ((hσ M U x).trans (evalSection_heq.{c, v, r} J B τ n M U x).symm)
  simp_rw [hσ']
  let e := evaluationTotalIso.{c, v, r} J B τ n P Q
  have he (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
      (x : (P.X p).val.obj (op (n, U.unop)))
      (y : (Q.X q).val.obj (op (n, U.unop))) :
      (e.hom.f k).val.app U
        (evalSection.{c, v, r} J B τ n _ U
          (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J)
            (systemRing J B τ) P Q p q k h (op (n, U.unop)) x y)) =
        coefficientTensorGenerator.{r, c, v} J (B n)
          (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj P)
          (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h U (evalSection.{c, v, r} J B τ n (P.X p) U x)
          (evalSection.{c, v, r} J B τ n (Q.X q) U y) := by
    have hh := congrArg (fun f ↦ (f.f k).val.app U
      (coefficientTensorGenerator.{r, c, v} J (B n)
        (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj P)
        (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj Q)
        p q k h U (evalSection.{c, v, r} J B τ n (P.X p) U x)
        (evalSection.{c, v, r} J B τ n (Q.X q) U y))) e.inv_hom_id
    change (e.hom.f k).val.app U ((e.inv.f k).val.app U _) = _ at hh
    rw [evaluationTotalIso_inv_generator] at hh
    exact hh
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (cancel_epi e.inv).mp
  apply HomologicalComplex.Hom.ext
  funext k
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext
  intro p q h U x y
  obtain ⟨x, rfl⟩ := evalSection_surjective.{c, v, r} J B τ n (P.X p) U x
  obtain ⟨y, rfl⟩ := evalSection_surjective.{c, v, r} J B τ n (Q.X q) U y
  change (e'.hom.f k).val.app U ((e.inv.f k).val.app U _) =
    (e.hom.f k).val.app U ((e.inv.f k).val.app U _)
  rw [evaluationTotalIso_inv_generator]
  exact (he' p q k h U x y).trans (he p q k h U x y).symm

end Generic
end WeilConjectures
