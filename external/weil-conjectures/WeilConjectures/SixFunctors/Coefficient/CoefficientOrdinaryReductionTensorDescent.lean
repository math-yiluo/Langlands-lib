/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryQuotientModel
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-! # Derived tensor comparison of reduction from a strict tensor comparison

Source: Stacks 07A4 and 0941.

A strict tensor comparison for the ordinary quotient-system functor descends to a
tensor comparison for every functor which the quotient-system functor computes on
flat-term K-flat complexes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  CoefficientClosedStructure.tensor
  coefficientIntegralTensorModelIso coefficientSystemTensorModelIso

/-- Flat-term K-flat complexes of completed-coefficient modules. -/
abbrev flatTermKFlat : ObjectProperty (CochainComplex (scalarReductionSource l E W) ℤ) :=
  fun X ↦ X.IsKFlatIndependentCoefficients ∧ ∀ p : ℤ, (X.X p).IsFlatOnSite

private theorem coefficient_total_eq :
    coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) =
      SheafOfModules.KFlatTotalTensorModel.total
        (completedIntegralCommRingSheafUnrestricted l E W) := by
  rfl

/-- Total tensor products of flat-term K-flat complexes are flat-term K-flat.
Source: Stacks 06YN, 07A4. -/
theorem flatTermKFlat_totalTensor (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : flatTermKFlat l E W P) (hQ : flatTermKFlat l E W Q) :
    flatTermKFlat l E W ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) := by
  refine ⟨coefficientTotalTensor_isKFlat.{u, t + 1, t} _ _ P Q hP.1 hQ.1, ?_⟩
  rw [coefficient_total_eq]
  exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (completedIntegralCommRingSheafUnrestricted l E W) P Q hP.1 hQ.1 hP.2 hQ.2).2.1

/-- A strict tensor comparison for the ordinary quotient-system functor descends to a
derived tensor comparison for any functor which it computes on flat-term K-flat
complexes. The descended comparison is the strict one on all such representatives.
Source: Stacks 07A4, proof of lemma-pullback-tensor-product, and 0941. -/
theorem reductionTensor_descent (M : OrdinaryModel l E W)
    (T : CoefficientDerivedSystemTensors l E W)
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (ε : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
    (hε : ∀ Q : CochainComplex (scalarReductionSource l E W) ℤ,
      Q.IsKFlatIndependentCoefficients → (∀ p : ℤ, (Q.X p).IsFlatOnSite) →
        IsIso (ε.app Q))
    (b : coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙ M.quotient l E W ≅
      (M.quotient l E W).prod (M.quotient l E W) ⋙
        coefficientTotalTensor.{u, t + 1, t} (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W))
    (hpres : ∀ P : CochainComplex (scalarReductionSource l E W) ℤ,
      P.IsKFlatIndependentCoefficients → (∀ p : ℤ, (P.X p).IsFlatOnSite) →
        CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E W) ((M.quotient l E W).obj P)) :
    ∃ μ : T.integralClosed.tensor ⋙ L ≅ L.prod L ⋙ T.systemClosed.tensor,
      ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
        (fP : ∀ p : ℤ, (P.X p).IsFlatOnSite) (fQ : ∀ p : ℤ, (Q.X p).IsFlatOnSite),
        CoefficientTensorComparisonSquare T.integralClosed.tensor T.systemClosed.tensor
          L DerivedCategory.Q
          (coefficientIntegralTensorModelIso l E W T P Q hP hQ).hom μ.hom
          (ε.app P) (ε.app Q) (ε.app _) (b.hom.app (P, Q))
          (coefficientSystemTensorModelIso l E W T ((M.quotient l E W).obj P)
            ((M.quotient l E W).obj Q) (hpres P hP fP) (hpres Q hQ fQ)).hom := by
  classical
  let A := scalarReductionSource l E W
  let B := coefficientSequenceModules l E W
  let PR := flatTermKFlat l E W
  let PK : ObjectProperty (CochainComplex A ℤ) := CochainComplex.IsKFlatIndependentCoefficients
  let PS : ObjectProperty (CochainComplex B ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, hq⟩ := exists_flatTermKFlatResolution l E W X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) (coefficientSequenceDerived l E W)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (coefficientSequenceDerived l E W)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  let G : PR.FullSubcategory ⥤ PK.FullSubcategory := ObjectProperty.ιOfLE (fun _ h ↦ h.1)
  let G' : PS.FullSubcategory ⥤ PS.FullSubcategory := 𝟭 _
  let r : (PR.ι.prod PR.ι) ⋙
      coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙
        T.integralClosed.tensor :=
    NatIso.ofComponents (fun X ↦ T.integralTensorModel.comparison.app (G.obj X.1, G.obj X.2))
      (fun f ↦ T.integralTensorModel.comparison.hom.naturality (Prod.mkHom (G.map f.1) (G.map f.2)))
  let r' : (PS.ι.prod PS.ι) ⋙
      coefficientTotalTensor.{u, t + 1, t} (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙
        T.systemClosed.tensor :=
    NatIso.ofComponents (fun X ↦ T.systemTensorModel.comparison.app (G'.obj X.1, G'.obj X.2))
      (fun f ↦ T.systemTensorModel.comparison.hom.naturality
        (Prod.mkHom (G'.map f.1) (G'.map f.2)))
  obtain ⟨μ, hμ, _⟩ := tensorComparisonDescent DerivedCategory.Q DerivedCategory.Q
    (M.quotient l E W) L ε PR PS (fun P hP ↦ hpres P hP.1 hP.2) ff'
    (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W))
    (coefficientTotalTensor.{u, t + 1, t} (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W))
    T.integralClosed.tensor T.systemClosed.tensor r r' b
    (fun P hP ↦ hε P hP.1 hP.2)
    (fun P Q hP hQ ↦ by
      have h := flatTermKFlat_totalTensor l E W P Q hP hQ
      exact hε _ h.1 h.2)
  refine ⟨μ, ?_⟩
  intro P Q hP hQ fP fQ
  unfold CoefficientTensorComparisonSquare coefficientIntegralTensorModelIso
    coefficientSystemTensorModelIso CoefficientTensorModels.iso
  exact hμ P Q ⟨hP, fP⟩ ⟨hQ, fQ⟩

end WeilConjectures.OrdinaryQuotient
