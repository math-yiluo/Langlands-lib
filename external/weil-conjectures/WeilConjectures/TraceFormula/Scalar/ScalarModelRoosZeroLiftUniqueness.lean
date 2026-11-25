/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftNestedCoordinateExtensionality

/-! # Uniqueness of a zero-shifted scalar Roos lift

Source: Stacks Project, Tag 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-zero-lift-uniqueness)

The strict Roos coordinates determine a localized map once the shifted coordinate
vanishes. This is the coordinate/extensionality part of the scalar lift argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension completedScalarCounit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

private theorem scalarModel_cocone_degree_ext
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {K L₀ P : CochainComplex A ℤ} (φ : K ⟶ L₀)
    (f g : P ⟶ CochainComplex.mappingCocone φ) (i : ℤ)
    (hf : f.f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
      g.f i ≫ (CochainComplex.mappingCocone.fst φ).f i)
    (hs : f.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) :
    f.f i = g.f i := by
  have hi := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  calc
    f.f i = f.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (by omega) +
        (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
          (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) :=
      congrArg (f.f i ≫ ·) hi.symm
    _ = g.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (by omega) +
        (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
          (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by
      rw [Preadditive.comp_add, Preadditive.comp_add, reassoc_of% hf,
        reassoc_of% hs]
    _ = g.f i := by rw [hi, Category.comp_id]

/-- A zero-shifted strict Roos map is determined after localization by its unshifted
coordinates on nested scalar tensors.

Source: Stacks 0941; Bhatt--Scholze, Proposition 3.5.1; step 3 of
`lem-trf-scalar-model-roos-zero-lift`.

Proof in words: the zero shifted coordinates remove the second component of the
Roos cone. Tensor balancing and sheafification extend equality from nested tensor
generators to every section, while product and mapping-cocone extensionality identify
the strict chain maps. Applying the localization functor gives the displayed equality.
-/
theorem scalarModelRoosZeroLift_uniqueness
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (h g : (completedOrdinaryScalarComplex l L F j X).obj
      ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor)
    (hh : ∀ i : ℤ, h.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor)).v i (i - 1) (by omega) = 0)
    (hg : ∀ i : ℤ, g.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor)).v i (i - 1) (by omega) = 0)
    (hcoord : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : (P.obj.X i).val.obj U),
      ((h.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦
          (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
            (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
              (.up ℤ)).obj D)).asFunctor.obj (op m)) n).f i).val.app U)
        (completedScalarTensorSection l L F j X
          (((completedOrdinaryScalarComplex l E L ι X).obj P.obj).X i) U s
          (completedScalarTensorSection l E L ι X (P.obj.X i) U t x)) =
      ((g.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦
          (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
            (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
              (.up ℤ)).obj D)).asFunctor.obj (op m)) n).f i).val.app U)
        (completedScalarTensorSection l L F j X
          (((completedOrdinaryScalarComplex l E L ι X).obj P.obj).X i) U s
          (completedScalarTensorSection l E L ι X (P.obj.X i) U t x))) :
    DerivedCategory.Q.map h = DerivedCategory.Q.map g := by
  have hfirst := scalarModelRoosZeroLift_nestedCoordinate_extensionality
    l E L F ι j X P D h g hcoord
  have hstrict : h = g := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply scalarModel_cocone_degree_ext
      (scalarRoosBoundary
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor)
    · exact hfirst i
    · rw [hh i, hg i]
  exact congrArg DerivedCategory.Q.map hstrict

end WeilConjectures
