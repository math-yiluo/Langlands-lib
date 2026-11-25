/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictDerivedComparison
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictTensorNormalized
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Strict representatives for finite coefficient extension

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

private theorem coefficientSequenceNormalized_of_iso
    {X Y : coefficientSequenceDerived l E W} (e : X ≅ Y)
    (hX : IsNormalizedCoefficientSequence l E W X) :
    IsNormalizedCoefficientSequence l E W Y := by
  intro m n h P
  let en := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
  let em := (coefficientSequenceDerivedEvaluation l E W m).mapIso e
  let G := normalizedDVRRes l E W h
  have hn := (coefficientSequenceDerivedTransition l E W h).naturality e.hom
  change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app Y =
    (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map en.hom at hn
  constructor
  · intro x y hxy
    apply (cancel_epi en.hom).1
    apply (hX h P).injective
    change (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map (en.hom ≫ x) =
      (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map (en.hom ≫ y)
    change (coefficientSequenceDerivedTransition l E W h).app Y ≫ G.map x =
      (coefficientSequenceDerivedTransition l E W h).app Y ≫ G.map y at hxy
    simp only [G.map_comp, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using congrArg (fun k ↦ em.hom ≫ k) hxy
  · intro t
    obtain ⟨s, hs⟩ := (hX h P).surjective (em.hom ≫ t)
    refine ⟨en.inv ≫ s, ?_⟩
    apply (cancel_epi em.hom).1
    change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app Y ≫
      G.map (en.inv ≫ s) = em.hom ≫ t
    rw [G.map_comp, ← Category.assoc, hn]
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_assoc]
    exact hs

private theorem coefficientExtensionGoodRepresentative
    (K : DerivedCategory (scalarReductionSource l E W)) :
    ∃ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  classical
  obtain ⟨P, q, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W)
      (DerivedCategory.Q.objPreimage K)
  have hgood : (integralOperationsGoodComplex l E W) P := by
    refine ⟨hP, fun i ↦ ?_⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E W) (P.X i)).symm (hf i)
  have : IsIso (DerivedCategory.Q.map q) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) q hq
  exact ⟨⟨P, hgood⟩, ⟨asIso (DerivedCategory.Q.map q) ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩⟩

variable (A : CoefficientExtensionSystems l E L ι W)

/-- Simultaneous strict finite quotient representatives of derived coefficient extension.
Source: integral operations, Stacks 06YY, 07A6 and 0941
(blueprint: stage3-pur-extension-strict-representatives).
Proof: use the ringed sequence projection to form the ordinary strict system whose
nth term is tensor with the nth target quotient. Its tensor generators determine
its quotient transitions. Apply it degreewise to flat-term K-flat complexes.
The given balanced associations identify the evaluated complexes with the iterated
finite scalar models. Transpose the ordinary units, using the reduction unit and
scalar evaluation formulas, to obtain a natural comparison from the specified
derived extension. At each level this is the composite of the two universal
K-flat comparisons and the given association. Both scalar extensions preserve
K-flatness, so these comparisons are invertible. The jointly conservative
evaluations make the system comparison invertible. For m at least n, scalar
extension of the mth term to the nth quotient is identified with the nth term by
balanced tensor association. Its adjoint is precisely the specified quotient
transition. Thus the universal Hom criterion gives normalization, first on good
representatives and then on every derived object by a K-flat resolution. -/
theorem coefficientExtensionStrictRepresentative_exists
    (SE : CoefficientDerivedSystemCalculus l E W)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association) :
    ∃ (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
        CochainComplex (coefficientSequenceModules l L W) ℤ)
      (directEvaluation : ∀ n : ℕ,
        direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
          (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
      (model : integralOperationsGoodLocalization l E W ⋙
        coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q),
      IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation ∧
      IsCoefficientExtensionModelEvaluation l E L ι W SE A association direct
        directEvaluation model ∧
      ∀ K : DerivedCategory (scalarReductionSource l E W),
        IsNormalizedCoefficientSequence l L W
          ((coefficientExtensionSystem l E L ι W SE A).obj K) := by
  classical
  obtain ⟨direct, directEvaluation, htransition⟩ :=
    coefficientExtensionOrdinaryStrictTensor_exists l E L ι W
  obtain ⟨model, hmodel⟩ := coefficientExtensionStrictDerivedComparison
    l E L ι W A SE association hassociation direct directEvaluation htransition
  refine ⟨direct, directEvaluation, model, htransition, hmodel, ?_⟩
  intro K
  obtain ⟨P, ⟨e⟩⟩ := coefficientExtensionGoodRepresentative l E W K
  have hP : IsNormalizedCoefficientSequence l L W
      (DerivedCategory.Q.obj (direct.obj P)) :=
    coefficientExtensionStrictTensor_normalized
      l E L ι W direct directEvaluation htransition P
  have hC : IsNormalizedCoefficientSequence l L W
      ((coefficientExtensionSystem l E L ι W SE A).obj
        ((integralOperationsGoodLocalization l E W).obj P)) :=
    coefficientSequenceNormalized_of_iso l L W (model.app P).symm hP
  intro m n h Z
  exact coefficientSequenceNormalized_of_iso l L W
    ((coefficientExtensionSystem l E L ι W SE A).mapIso e) hC h Z

end WeilConjectures
