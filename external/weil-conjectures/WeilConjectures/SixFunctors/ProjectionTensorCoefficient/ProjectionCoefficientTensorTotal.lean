/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
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
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # The representative-normalized tensor comparison for projection

Source: main-20261015, projection-formula proof step 13
(blueprint: def-sf-projection-coefficient-tensor-total).
The ordinary comparison is fixed on homogeneous local pure tensors. Derived
descent and the specified quotient-completion unit then fix its integral and
rational constructible restrictions.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.ProjectionTensorCoefficient

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

/-- Termwise scalar restriction along the quotient-normalized ring isomorphism.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def complexTransport :=
  (fdCoefficientTransport l E X).mapHomologicalComplex (.up ℤ)

/-- Signed total tensor after coefficient restriction.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def totalTarget :=
  ((complexTransport l E X).prod (complexTransport l E X)) ⋙
    Functor.uncurry.obj
      ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).map₂CochainComplex)

private theorem tensor_hom_ext
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M N H : pbcModules X R)
    {f g : ((proEtaleOrdinaryTensor X R).obj M).obj N ⟶ H}
    (h : ∀ U x y, f.val.app U (proEtaleTensorPair X R M N U x y) =
      g.val.app U (proEtaleTensorPair X R M N U x y)) : f = g := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

private def coefficientIso :
    pbcAdicCompletion X (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E X := by
  let lift : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}},
      ((adicLisseForget X).obj R ⟶ (adicLisseForget X).obj S) → (R ⟶ S) :=
    fun {R S} f ↦ ⟨{
      app := fun U ↦ CommRingCat.ofHom (f.hom.app U).hom
      naturality := by
        intro U V g
        apply (forget₂ CommRingCat RingCat).map_injective
        exact f.hom.naturality g }⟩
  let e : (adicLisseForget X).obj (pbcAdicCompletion X (pbcIntegralDatum l E)) ≅
      (adicLisseForget X).obj (completedIntegralCommRingSheafUnrestricted l E X) :=
    integralDetailedCoefficientComparison X l E
  let c : pbcAdicCompletion X (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E X := {
    hom := lift e.hom
    inv := lift e.inv
    hom_inv_id := by
      apply (adicLisseForget X).map_injective
      exact e.hom_inv_id
    inv_hom_id := by
      apply (adicLisseForget X).map_injective
      exact e.inv_hom_id }
  exact c

/-- The coefficient tensor comparison is fixed on local pure tensors.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: send x tensor y to the same tensor of the two restricted sections.
Restriction along the inverse ring isomorphism gives the inverse. Balancedness
and restriction compatibility descend through sheafification. Pure tensors
locally generate the tensor sheaf, proving naturality and uniqueness. -/
theorem module_existsUnique :
    ∃! mu : ∀ M N : integralTowerModules l E X,
      (fdCoefficientTransport l E X).obj
          (((constructibleTensorOrdinary l E X).obj M).obj N) ≅
        ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
          ((fdCoefficientTransport l E X).obj M)).obj
            ((fdCoefficientTransport l E X).obj N),
      (∀ (M M' N N' : integralTowerModules l E X) (f : M ⟶ M') (g : N ⟶ N'),
        (fdCoefficientTransport l E X).map
            (((constructibleTensorOrdinary l E X).map f).app N ≫
              ((constructibleTensorOrdinary l E X).obj M').map g) ≫ (mu M' N').hom =
          (mu M N).hom ≫
            ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).map
              ((fdCoefficientTransport l E X).map f)).app
                ((fdCoefficientTransport l E X).obj N) ≫
            ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
              ((fdCoefficientTransport l E X).obj M')).map
                ((fdCoefficientTransport l E X).map g)) ∧
      ∀ (M N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
        (x : M.val.obj U) (y : N.val.obj U),
        (mu M N).hom.val.app U
          (proEtaleTensorPair X (completedIntegralCommRingSheafUnrestricted l E X) M N U x y) =
        proEtaleTensorPair X (pbcAdicCompletion X (pbcIntegralDatum l E))
          ((fdCoefficientTransport l E X).obj M)
          ((fdCoefficientTransport l E X).obj N) U x y := by
  let c := coefficientIso l E X
  let t := (SheafOfModules.ringIso_tensor_transport c).some
  let := t.monoidal
  let mu := fun (M N : integralTowerModules l E X) ↦ asIso (Functor.OplaxMonoidal.δ
    (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom) M N)
  refine ⟨mu, ⟨?_, ?_⟩, ?_⟩
  · intro M M' N N' f g
    exact (Functor.OplaxMonoidal.δ_natural
      (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom) f g).symm
  · intro M N U x y
    exact t.pure_hom M N U x y
  · intro nu hnu
    funext M N
    apply Iso.ext
    apply (cancel_epi (mu M N).inv).1
    rw [Iso.inv_hom_id]
    apply tensor_hom_ext X (pbcAdicCompletion X (pbcIntegralDatum l E))
    intro U x y
    have hi : (mu M N).inv.val.app U
        (proEtaleTensorPair X (pbcAdicCompletion X (pbcIntegralDatum l E))
          ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom).obj M)
          ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom).obj N) U x y) =
        proEtaleTensorPair X (completedIntegralCommRingSheafUnrestricted l E X)
          M N U x y := by
      have hp : (mu M N).hom.val.app U
          (proEtaleTensorPair X (completedIntegralCommRingSheafUnrestricted l E X)
            M N U x y) =
          proEtaleTensorPair X (pbcAdicCompletion X (pbcIntegralDatum l E))
            ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom).obj M)
            ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom).obj N) U x y :=
        t.pure_hom M N U x y
      rw [← hp]
      exact congrArg (fun f ↦ f.val.app U
        (proEtaleTensorPair X (completedIntegralCommRingSheafUnrestricted l E X)
          M N U x y)) (mu M N).hom_inv_id
    change (nu M N).hom.val.app U ((mu M N).inv.val.app U _) = _
    rw [hi]
    exact hnu.2 M N U x y

/-- The uniquely pure-tensor-normalized module comparison.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def moduleComparison (M N : integralTowerModules l E X) :
    (fdCoefficientTransport l E X).obj
        (((constructibleTensorOrdinary l E X).obj M).obj N) ≅
      ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
        ((fdCoefficientTransport l E X).obj M)).obj
          ((fdCoefficientTransport l E X).obj N) :=
  (module_existsUnique l E X).exists.choose M N

/-- Naturality of the specified ordinary coefficient tensor comparison.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: the first clause of the unique pure-tensor characterization gives this
identity; both sides send the generator x tensor y to f(x) tensor g(y). -/
theorem module_naturality
    {M M' N N' : integralTowerModules l E X} (f : M ⟶ M') (g : N ⟶ N') :
    (fdCoefficientTransport l E X).map
        (((constructibleTensorOrdinary l E X).map f).app N ≫
          ((constructibleTensorOrdinary l E X).obj M').map g) ≫
        (moduleComparison l E X M' N').hom =
      (moduleComparison l E X M N).hom ≫
        ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).map
          ((fdCoefficientTransport l E X).map f)).app
            ((fdCoefficientTransport l E X).obj N) ≫
        ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
          ((fdCoefficientTransport l E X).obj M')).map
            ((fdCoefficientTransport l E X).map g) := by
  exact (module_existsUnique l E X).exists.choose_spec.1 M M' N N' f g

/-- Naturality in the tensorHom coordinates used by the signed-total constructor.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: tensorHom is the first-variable tensor map followed by the
second-variable map. Thus this is precisely module_naturality, with the
same specified monoidal structures on both module categories. -/
theorem module_tensorHom_naturality
    {M M' N N' : integralTowerModules l E X} (f : M ⟶ M') (g : N ⟶ N') :
    (fdCoefficientTransport l E X).map
        (@MonoidalCategoryStruct.tensorHom (integralTowerModules l E X) _
          (SheafOfModules.monoidalCategory
            (completedIntegralCommRingSheafUnrestricted l E X)).toMonoidalCategoryStruct
          M M' N N' f g) ≫ (moduleComparison l E X M' N').hom =
      (moduleComparison l E X M N).hom ≫
        @MonoidalCategoryStruct.tensorHom
          (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) _
          (SheafOfModules.monoidalCategory
            (pbcAdicCompletion X (pbcIntegralDatum l E))).toMonoidalCategoryStruct
          _ _ _ _ ((fdCoefficientTransport l E X).map f)
          ((fdCoefficientTransport l E X).map g) := by
  exact module_naturality l E X f g

/-- The inverse module comparison summed over all bidegrees with the usual signs.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def total (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (totalTarget l E X).obj (P, Q) ⟶
      (complexTransport l E X).obj ((constructibleTensorTotal l E X).obj (P, Q)) :=
  letI : MonoidalCategory (integralTowerModules l E X) :=
    SheafOfModules.monoidalCategory (completedIntegralCommRingSheafUnrestricted l E X)
  letI : MonoidalCategory (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :=
    SheafOfModules.monoidalCategory (pbcAdicCompletion X (pbcIntegralDatum l E))
  letI : MonoidalPreadditive (integralTowerModules l E X) :=
    proEtaleTensorPreadditive X (completedIntegralCommRingSheafUnrestricted l E X)
  letI : MonoidalPreadditive
      (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :=
    proEtaleTensorPreadditive X (pbcAdicCompletion X (pbcIntegralDatum l E))
  let F : integralTowerModules l E X ⥤
      pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
    fdCoefficientTransport l E X
  letI : F.Additive := fdCoefficientTransportAdditive l E X
  tensorPullbackTotal
    (A := integralTowerModules l E X)
    (B := pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)))
    F (moduleComparison l E X)
    (module_tensorHom_naturality l E X) P Q

/-- The signed total comparison is invertible.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: exact coefficient restriction along an isomorphism preserves direct sums;
each summand comparison is invertible. The same direct-sum formula with the
inverse summand maps is the two-sided inverse chain map. -/
theorem total_isIso (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    IsIso (total l E X P Q) := by
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E X)
  let := SheafOfModules.monoidalCategory (pbcAdicCompletion X (pbcIntegralDatum l E))
  let := proEtaleTensorPreadditive X (completedIntegralCommRingSheafUnrestricted l E X)
  let := proEtaleTensorPreadditive X (pbcAdicCompletion X (pbcIntegralDatum l E))
  let F : integralTowerModules l E X ⥤
      pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
    fdCoefficientTransport l E X
  let : F.Additive := fdCoefficientTransportAdditive l E X
  let t := (SheafOfModules.ringIso_tensor_transport (coefficientIso l E X)).some
  have : F.IsEquivalence := by
    change (SheafOfModules.scalarRestriction (coefficientIso l E X).hom).IsEquivalence
    rw [← t.functor_eq]
    exact t.equivalence.isEquivalence_functor
  exact tensorPullbackTotal_isIso
    (A := integralTowerModules l E X)
    (B := pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)))
    F (moduleComparison l E X) (module_tensorHom_naturality l E X)
    F.asEquivalence.inverse F.asEquivalence.toAdjunction P Q

/-- The signed total isomorphism with the derived-square orientation.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def totalIso (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (complexTransport l E X).obj ((constructibleTensorTotal l E X).obj (P, Q)) ≅
      (totalTarget l E X).obj (P, Q) :=
  letI := total_isIso l E X P Q
  (asIso (total l E X P Q)).symm

end WeilConjectures.ProjectionTensorCoefficient
