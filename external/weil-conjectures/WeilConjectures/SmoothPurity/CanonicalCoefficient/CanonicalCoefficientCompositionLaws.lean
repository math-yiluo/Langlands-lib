/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CanonicalCoefficient.CanonicalCoefficientReduction
import WeilConjectures.SmoothPurity.CanonicalCoefficient.CanonicalCoefficientRepresentativeLaws
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedTensorAssociativity
import all WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedInternalHomFibers
import all WeilConjectures.CategoryTheory.Ringed.RingedHomCompositionModel
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # Internal composition for normalized coefficient tensor presentations

Source: Stacks 0A98, 08JD and 0941.
(blueprint: lem-pur-canonical-coefficient-composition-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe a b v w t u c r
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures.CanonicalCoefficient

/-- The internal-composition clause, separate from naturality and transposition. -/
def CompositionLaw {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ P Q V : A,
    F.map (SA.composition P Q V) ≫ coefficientBaseChangeHom SA SB F μ P V =
      μ.hom.app (HA.obj (op Q, V), HA.obj (op P, Q)) ≫
        SB.tensor.map
          (Prod.mkHom (coefficientBaseChangeHom SA SB F μ Q V)
            (coefficientBaseChangeHom SA SB F μ P Q)) ≫
        SB.composition (F.obj P) (F.obj Q) (F.obj V)

section ModelUniqueness
open CategoryTheory.Limits
attribute [local instance 4000] HomologicalComplex.monoidalCategory
attribute [local instance 1000001] RingedDerivedNative.cachedCompose
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric
attribute [local irreducible] RingedDerivedNative.chainEquiv

private theorem tensorModels_unique
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T U : CoefficientTensorModels.{r, c, v, w} J R S) : T = U := by
  let : HasLimitsOfSize.{0, 0} (RingedTensorModules.{c, v, r} J R) :=
    RingedDerivedNative.baseLimits.{c, v, r} J R
  let : HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, r} J R) :=
    RingedDerivedNative.baseColimits.{c, v, r} J R
  let : ∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, r} J R)), X.HasTensor Y :=
    RingedDerivedNative.gradedTensor.{c, v, r} J R
  let : ∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, r} J R)),
      GradedObject.HasTensor₄ObjExt W X Y Z :=
    RingedDerivedNative.gradedTensorFour.{c, v, r} J R
  let : ∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, r} J R)),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
    RingedDerivedNative.gradedTensorLeft.{c, v, r} J R
  let : ∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, r} J R)),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
    RingedDerivedNative.gradedTensorRight.{c, v, r} J R
  have he : T.comparison = U.comparison := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    rcases X with ⟨⟨P, hP⟩, ⟨L, hL⟩⟩
    -- Currying the tensor identity pins down the inverse of each model comparison.
    let M := (coefficientTotalTensor.{r, c, v} J R).obj (P, L)
    let φ := (RingedDerivedNative.chainEquiv.{c, v, r} J R P L M) (𝟙 M)
    have hT := HomCompositionProof.normalized_uncurry.{c, v, r, w} J R S T
      P L M hP hL φ
    have hU := HomCompositionProof.normalized_uncurry.{c, v, r, w} J R S U
      P L M hP hL φ
    simp only [φ, Equiv.symm_apply_apply] at hT hU
    rw [CategoryTheory.Functor.map_id] at hT hU
    let z := (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj M)).symm
        (DerivedCategory.Q.map φ ≫ ringedHomRepresentativeMap.{c, v, r, w} J R L M)
    change (T.iso J R S P L hP hL).hom ≫ z = 𝟙 _ at hT
    change (U.iso J R S P L hP hL).hom ≫ z = 𝟙 _ at hU
    have hz : z = (T.iso J R S P L hP hL).inv := by
      apply (cancel_epi (T.iso J R S P L hP hL).hom).mp
      exact hT.trans (T.iso J R S P L hP hL).hom_inv_id.symm
    change (T.iso J R S P L hP hL).hom = (U.iso J R S P L hP hL).hom
    apply (cancel_mono (T.iso J R S P L hP hL).inv).mp
    rw [hz] at hU
    exact (T.iso J R S P L hP hL).hom_inv_id.trans hU.symm
  cases T
  cases U
  cases he
  rfl

private theorem tensorModels_coherence
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (T : CoefficientTensorModels.{r, c, v, w} J R M.closed) :
    ∃ β : @SymmetricCategory _ _ M.closed.monoidal,
      Nonempty (RingedDerivedTensorCoherence.{c, v, r, w} J R M.closed T β) := by
  -- Equal comparison maps retain all normalized associator and unitor equations.
  rw [tensorModels_unique J R M.closed T M.models]
  obtain ⟨K, _⟩ := ringedSiteTensorCoherence J R M
  exact ⟨M.symmetric, ⟨K⟩⟩

end ModelUniqueness

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Normalized reduction and finite scalar extension preserve internal composition.

Source: Stacks 0A98 (lemma-internal-hom-composition), 08JD (lemma-dual), 07A4, 0941;
canonical integral calculus, proof step 3.
(blueprint: lem-pur-canonical-coefficient-composition-laws).

Proof: use the fixed normalized duality structures on the integral, sequence and
finite sites. Their associators descend reassociation of the same total tensors.
Their tensor-Hom adjunctions are ordinary uncurrying on K-flat/K-injective pairs.
The old pure-tensor reduction and finite scalar maps, conjugated by the adjoint
comparisons, still have those formulas: transpose the comparisons into the fixed
Hom resolution and use uniqueness on sheafified tensor generators. Uncurry the
two sides of the displayed composition equation. On a triple of homogeneous
sections both reassociate the same tensor and apply the two evaluations in the
order phi(psi(x)); the total differential has the same Koszul signs on both sides.
The strict-system calculation is made before evaluation at a finite level.
Generator uniqueness proves the chain equation. K-flat localization in each
variable, followed by naturality along resolution isomorphisms, proves the
identity for all derived inputs. Apply this once to reduction and once at each
finite level. No claim is made that an arbitrary adjoint comparison is monoidal;
the normalized associator formulas are essential. The proof includes zero
objects, the empty scheme, and unbounded complexes. -/
theorem compositionLaws (S : CoefficientDerivedSystemFibers l E W) :
    let R := reduction l E W S.toCoefficientDerivedSystemReduction
    CompositionLaw R.integralClosed R.systemClosed R.reduction R.reductionTensor ∧
      ∀ n : ℕ, CompositionLaw R.integralClosed (R.finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n) := by
  classical
  let R := reduction l E W S.toCoefficientDerivedSystemReduction
  have hT : CoefficientDerivedSystemTensorCoherence l E W
      R.toCoefficientDerivedSystemTensors := by
    refine ⟨?_, ?_, ?_⟩
    · exact tensorModels_coherence (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        (IntegralOnSlice.duality l E W none) R.integralTensorModel
    · exact tensorModels_coherence
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (Classical.choice (ringedSiteDualityMaps_exists.{t+1, t, u,
          (max u (t+1))+1} (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W))) R.systemTensorModel
    · intro n
      exact tensorModels_coherence (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (Classical.choice (ringedSiteDualityMaps_exists.{t+1, t, u,
          (max u (t+1))+1} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n))) (R.finiteTensorModel n)
  have hRep := representativeLaws l E W S
  obtain ⟨ha, hf⟩ := coefficientNormalizedTensorAssociativity l E W R hT
    hRep.reduction_tensor hRep.finite_tensor
  exact ⟨baseChange_composition R.integralClosed R.systemClosed R.reduction
      R.reductionTensor ha,
    fun n ↦ baseChange_composition R.integralClosed (R.finiteClosed n)
      (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n) (hf n)⟩

end WeilConjectures.CanonicalCoefficient
