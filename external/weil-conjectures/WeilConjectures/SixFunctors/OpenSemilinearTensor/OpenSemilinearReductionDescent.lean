/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OrdinaryReductionAugmentedComputation
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Augmented open reduction descent

Source: Stacks Project, Modules on Sites, Tags 0E8I and 03DI.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
namespace WeilConjectures.OpenSemilinearTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

private theorem cancellation
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B H I : D} {M N : C} (a : A ⟶ B) (b : B ⟶ H) (c : H ⟶ I)
    (d : F.obj N ≅ I) (e : M ≅ N) :
    (a ≫ b ≫ c ≫ d.inv ≫ F.map e.inv) ≫ F.map e.hom ≫ d.hom = a ≫ b ≫ c := by
  simp only [Category.assoc, ← F.map_comp_assoc, e.inv_hom_id,
    F.map_id, Category.id_comp, d.inv_hom_id, Category.comp_id]

/-- Descent of an ordinary strict open scalar comparison through augmented computations.
Source: Stacks 06YS, 06YY, 0941 and 0GL1
(blueprint: lem-sf-open-semilinear-reduction-descent).

Proof: Compute ordinary quotient tensor simultaneously on flat-term K-flat complexes.
The scalar-unit maps give a strict augmentation whose transpose under the fixed reduction
and total-limit adjunction determines the computation comparison uniquely. Exact open
extension and the K-flat preservation hypothesis supply the same computation on the
extended complex. Conjugate the localization of the ordinary chain comparison by these
two computation isomorphisms. Naturality holds first for chain maps, then for inverses of
quasi-isomorphisms. The localization of flat-term K-flat models is equivalent to the
ordinary derived category, so this descends uniquely to all derived arrows. Each component
is an isomorphism, hence the descended transformation is a natural isomorphism. Its
construction gives the representative square, with the actual scalar-unit augmentation. -/
theorem openSemilinearReductionDescent
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (cX : CoefficientDerivedSystemCoherence l E X SX)
    (cU : CoefficientDerivedSystemCoherence l E U SU)
    (o : Operations l E j) (AX : OrdinaryReduction l E X) (AU : OrdinaryReduction l E U)
    (ordinary : IntegralOpenReduction.extension l E j o ⋙ AX.functor ≅
      AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o)
    (hk : KFlatPreservation l E j o)
    (hf : ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E U) Q →
      flatTerms.{t + 1, t, max u (t + 1)} (ProEt.topology U)
        (completedIntegralCommRingSheafUnrestricted l E U) Q →
      flatTerms.{t + 1, t, max u (t + 1)} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X) ((extensionComplex l E j o).obj Q)) :
    ∃ r : IntegralOpenReduction.shriek l E j o ⋙ SX.reduction ≅
      SU.reduction ⋙ IntegralOpenReduction.J l E j o,
      RepresentativeSquare l E j o SX SU AX AU r ordinary hk := by
  obtain ⟨eU, heU⟩ := ordinaryReductionAugmentedComputation l E U SU cU AU
  obtain ⟨eX, heX⟩ := ordinaryReductionAugmentedComputation l E X SX cX AX
  let goodU := integralOperationsGoodComplex l E U
  let goodX := integralOperationsGoodComplex l E X
  let G : goodU.FullSubcategory ⥤ goodX.FullSubcategory :=
    ObjectProperty.lift goodX (goodU.ι ⋙ extensionComplex l E j o)
      (fun P ↦ ⟨hk P.obj P.property.1 P.property.2,
        hf P.obj P.property.1 P.property.2⟩)
  let L := integralOperationsGoodLocalization l E U
  let W := (HomologicalComplex.quasiIso
    (scalarReductionSource l E U) (.up ℤ)).inverseImage goodU.ι
  let : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E U
  let ec : extensionComplex l E j o ⋙ AX.functor.mapHomologicalComplex (.up ℤ) ≅
      AU.functor.mapHomologicalComplex (.up ℤ) ⋙
        (IntegralOpenReduction.systemExtension l E j o).mapHomologicalComplex (.up ℤ) :=
    NatIso.ofComponents (ordinaryChain l E j o AX AU ordinary) (by
      intro Q Q' f
      apply HomologicalComplex.Hom.ext
      funext i
      exact ordinary.hom.naturality (f.f i))
  let b : L ⋙ (IntegralOpenReduction.shriek l E j o ⋙ SX.reduction) ≅
      L ⋙ (SU.reduction ⋙ IntegralOpenReduction.J l E j o) :=
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft goodU.ι
          (IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors) SX.reduction ≪≫
      Functor.isoWhiskerLeft G eX ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft goodU.ι ec) DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft
        (goodU.ι ⋙ AU.functor.mapHomologicalComplex (.up ℤ))
          (IntegralOpenReduction.systemExtension l E j o).mapDerivedCategoryFactors.symm ≪≫
      Functor.isoWhiskerRight eU.symm (IntegralOpenReduction.J l E j o)
  let r := Localization.liftNatIso L W _ _
    (IntegralOpenReduction.shriek l E j o ⋙ SX.reduction)
    (SU.reduction ⋙ IntegralOpenReduction.J l E j o) b
  refine ⟨r, ?_⟩
  intro Q hQ hflat
  let P : goodU.FullSubcategory := ⟨Q, hQ, hflat⟩
  let cU : Computation l E SU AU Q hQ :=
    ⟨eU.app P, (heU P).1, (heU P).2⟩
  let cX : Computation l E SX AX ((extensionComplex l E j o).obj Q)
      (hk Q hQ hflat) :=
    ⟨eX.app (G.obj P), (heX (G.obj P)).1, (heX (G.obj P)).2⟩
  refine ⟨cU, cX, ?_⟩
  have hr : r.hom.app (L.obj P) = b.hom.app P := by
    dsimp only [r, Localization.liftNatIso]
    simp only [Localization.liftNatTrans_app, Localization.Lifting.iso,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id]
  change r.hom.app (L.obj P) ≫ _ ≫ _ = _
  rw [hr]
  exact cancellation (IntegralOpenReduction.J l E j o)
    (SX.reduction.map
      ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q))
    (eX.hom.app (G.obj P))
    (DerivedCategory.Q.map (ordinaryChain l E j o AX AU ordinary Q).hom)
    ((IntegralOpenReduction.systemExtension l E j o).mapDerivedCategoryFactors.app
      ((AU.functor.mapHomologicalComplex (.up ℤ)).obj Q)) (eU.app P)

end WeilConjectures.OpenSemilinearTensor
