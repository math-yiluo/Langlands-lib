/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearOrdinaryComparison
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearReductionDescent
import all WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Simultaneous open tensor comparison before scalar restriction

Source: Stacks Project, sites-modules.tex, Tag 0E8I, and sites-cohomology.tex,
Tag 0GL1; the simultaneous refinement in the node's seven proof steps
(blueprint: lem-sf-open-semilinear-tensor-model).

The coefficient index n means exponent n+1. All complexes are unbounded. The existing
open-operation interfaces are reused; the completeness-restricted comparison theorem
in their module is not used. Ordinary reduction and its comparison are natural
transformations of strict semilinear systems, before any localization or forgetting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
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

attribute [local irreducible] CategoryTheory.Limits.limit HasDerivedCategory.standard
  scalarReductionExistence scalarReductionDerivedExistence
  SheafOfModules.monoidalCategory completedIntegralCoefficientSheafUnrestricted
  SheafOfModules.extensionByZeroPresheaf SheafOfModules.overFunctor

private theorem inverseInsertion {C : Type*} [Category* C]
    {A B D H : C} (e : A ≅ D) (d : H ≅ B) (f : A ⟶ B) (g : D ⟶ H)
    (h : g ≫ d.hom = e.inv ≫ f) : f ≫ d.inv = e.hom ≫ g := by
  have hh := congrArg (fun k ↦ e.hom ≫ k ≫ d.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh.symm

open CategoryTheory.MonoidalCategory in
private def tensorComparisonNatIso {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) (T : B ⥤ A)
    (μ : ∀ M N, F.obj M ⊗ N ≅ F.obj (M ⊗ T.obj N))
    (hn : ∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      (F.map f ⊗ₘ g) ≫ (μ M' N').hom =
        (μ M N).hom ≫ F.map (f ⊗ₘ T.map g)) (M : A) :
    tensorLeft (F.obj M) ≅ T ⋙ tensorLeft M ⋙ F :=
  NatIso.ofComponents (fun N ↦ μ M N) (by
    intro N N' g
    have h := hn (𝟙 M) g
    rw [F.map_id M] at h
    simpa only [Functor.comp_map, tensorLeft, curriedTensor_obj_map, id_tensorHom] using h)

open CategoryTheory.MonoidalCategory in
private theorem tensorLeft_exact_of_comparison {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) (T : B ⥤ A)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (μ : ∀ M N, F.obj M ⊗ N ≅ F.obj (M ⊗ T.obj N))
    (hn : ∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      (F.map f ⊗ₘ g) ≫ (μ M' N').hom =
        (μ M N).hom ≫ F.map (f ⊗ₘ T.map g)) (M : A)
    (hM : exactFunctor A A (tensorLeft M)) :
    exactFunctor B B (tensorLeft (F.obj M)) := by
  let : PreservesFiniteLimits (tensorLeft M) := hM.1
  let : PreservesFiniteColimits (tensorLeft M) := hM.2
  let : PreservesFiniteLimits (tensorLeft M ⋙ F) :=
    comp_preservesFiniteLimits (tensorLeft M) F
  let : PreservesFiniteColimits (tensorLeft M ⋙ F) :=
    comp_preservesFiniteColimits (tensorLeft M) F
  let : PreservesFiniteLimits (T ⋙ tensorLeft M ⋙ F) :=
    comp_preservesFiniteLimits T (tensorLeft M ⋙ F)
  let : PreservesFiniteColimits (T ⋙ tensorLeft M ⋙ F) :=
    comp_preservesFiniteColimits T (tensorLeft M ⋙ F)
  have ht : exactFunctor B B (T ⋙ tensorLeft M ⋙ F) :=
    ⟨(show PreservesFiniteLimits (T ⋙ tensorLeft M ⋙ F) from inferInstance),
      (show PreservesFiniteColimits (T ⋙ tensorLeft M ⋙ F) from inferInstance)⟩
  exact (exactFunctor B B).prop_of_iso
    (tensorComparisonNatIso F T μ hn M).symm ht

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
open CategoryTheory.MonoidalCategory in
private theorem totalComparison_of_ordinary (o : Operations l E j)
    (μ : OrdinaryTensorComparison l E j o)
    (hn : OrdinaryNaturality l E j o μ) (hg : OrdinaryGenerators l E j o μ) :
    Nonempty (TotalComparison l E j o) := by
  let : EssentiallySmall.{max u (t + 1)} U.ProEt := essentiallySmallSelf _
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let A := scalarReductionSource l E U
  let B := scalarReductionSource l E X
  let RU : Sheaf (ProEt.topology U) CommRingCat.{max u (t + 1)} :=
    completedIntegralCommRingSheafUnrestricted l E U
  let RX : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)} :=
    completedIntegralCommRingSheafUnrestricted l E X
  let : HasSheafify (ProEt.topology U) AddCommGrpCat.{max u (t + 1)} :=
    abelianSheafify.{t + 1, t, max u (t + 1)} (ProEt.topology U)
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} :=
    abelianSheafify.{t + 1, t, max u (t + 1)} (ProEt.topology X)
  let : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    locallyBijective.{t + 1, t, max u (t + 1)} (ProEt.topology U)
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    locallyBijective.{t + 1, t, max u (t + 1)} (ProEt.topology X)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{t + 1, t, max u (t + 1)} RU
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{t + 1, t, max u (t + 1)} RX
  let : MonoidalCategory A := SheafOfModules.monoidalCategory.{t, t + 1, max u (t + 1)} RU
  let : MonoidalCategory B := SheafOfModules.monoidalCategory.{t, t + 1, max u (t + 1)} RX
  let : MonoidalPreadditive A :=
    SheafOfModules.cochainModulesPreadditive.{t + 1, t, max u (t + 1)} RU
  let : MonoidalPreadditive B :=
    SheafOfModules.cochainModulesPreadditive.{t + 1, t, max u (t + 1)} RX
  let H : A ⥤ A ⥤ A := curriedTensor A
  let H' : B ⥤ B ⥤ B := curriedTensor B
  let Fext : A ⥤ B := IntegralOpenReduction.extension l E j o
  let T : B ⥤ A := IntegralOpenReduction.restriction l E j o
  let : PreservesFiniteLimits Fext := IntegralOpenReduction.extensionLimits l E j o
  let : PreservesFiniteColimits Fext := IntegralOpenReduction.extensionColimits l E j o
  let : PreservesColimitsOfSize.{0, 0} Fext :=
    (IntegralOpenReduction.ordinaryAdjunction l E j o).leftAdjoint_preservesColimits
  let : H.PreservesZeroMorphisms :=
    SheafOfModules.ringedOpenTensorZero.{t + 1, t, max u (t + 1)} RU
  let : ∀ M, (H.obj M).PreservesZeroMorphisms :=
    SheafOfModules.ringedOpenTensorObjZero.{t + 1, t, max u (t + 1)} RU
  let : H'.PreservesZeroMorphisms :=
    SheafOfModules.ringedOpenTensorZero.{t + 1, t, max u (t + 1)} RX
  let : ∀ M, (H'.obj M).PreservesZeroMorphisms :=
    SheafOfModules.ringedOpenTensorObjZero.{t + 1, t, max u (t + 1)} RX
  let : ∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ) :=
    SheafOfModules.ringedOpenHasTotalTensor.{t + 1, t, max u (t + 1)} RU
  let : ∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ) :=
    SheafOfModules.ringedOpenHasTotalTensor.{t + 1, t, max u (t + 1)} RX
  let : (H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms :=
    SheafOfModules.precompose_preservesZero H T
  let : ∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms :=
    SheafOfModules.precompose_obj_preservesZero H T
  let : ∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ) :=
    SheafOfModules.precompose_hasTotal H T
  obtain ⟨Φ, hι, hnat⟩ := SheafOfModules.comparisonFromComponents_exists Fext T H H'
    (fun M N ↦ (μ M N).symm) (by
      intro M M' N N' a b
      have h := SheafOfModules.inverse_square (μ M N) (μ M' N')
        (ordinaryTensorHom.{t + 1, t, max u (t + 1)} (ProEt.topology X) RX (Fext.map a) b)
        (Fext.map (ordinaryTensorHom.{t + 1, t, max u (t + 1)}
          (ProEt.topology U) RU a (T.map b)))
        (hn a b)
      simpa only [H, H', curriedTensor_map_app, curriedTensor_obj_map,
        ordinaryTensorHom, ← MonoidalCategory.tensorHom_def, Iso.symm_hom] using h)
    H.map₂CochainComplex H'.map₂CochainComplex
    (fun P C p q n h ↦ HomologicalComplex.ιMapBifunctor P C H (.up ℤ) p q n h)
    (fun P C p q n h ↦ HomologicalComplex.ιMapBifunctor P C H' (.up ℤ) p q n h)
    ⟨rfl, fun _ _ _ _ _ _ ↦ HEq.rfl⟩ ⟨rfl, fun _ _ _ _ _ _ ↦ HEq.rfl⟩
  refine ⟨⟨μ, (fun Q F ↦ (Φ Q F).symm), hn, hg, ?_, ?_⟩⟩
  · intro Q F a b d h
    exact inverseInsertion (μ (Q.X a) (F.X b))
      ((HomologicalComplex.eval _ _ d).mapIso (Φ Q F)) _ _ (hι Q F a b d h)
  · intro Q Q' F F' f g
    have h := SheafOfModules.inverse_square (Φ Q F) (Φ Q' F') _ _ (hnat Q Q' F F' f g)
    exact h

set_option maxHeartbeats 50000 in
-- Keep this exactness proof below the default elaboration budget.
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
open CategoryTheory.MonoidalCategory in
private theorem flat_of_ordinary (o : Operations l E j)
    (μ : OrdinaryTensorComparison l E j o) (hn : OrdinaryNaturality l E j o μ)
    (M : scalarReductionSource l E U)
    (hM : SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E U) M) :
    SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      ((IntegralOpenReduction.extension l E j o).obj M) := by
  let : EssentiallySmall.{max u (t + 1)} U.ProEt := essentiallySmallSelf _
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let A := scalarReductionSource l E U
  let B := scalarReductionSource l E X
  let RU : Sheaf (ProEt.topology U) CommRingCat.{max u (t + 1)} :=
    completedIntegralCommRingSheafUnrestricted l E U
  let RX : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)} :=
    completedIntegralCommRingSheafUnrestricted l E X
  let : HasSheafify (ProEt.topology U) AddCommGrpCat.{max u (t + 1)} :=
    abelianSheafify.{t + 1, t, max u (t + 1)} (ProEt.topology U)
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} :=
    abelianSheafify.{t + 1, t, max u (t + 1)} (ProEt.topology X)
  let : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    locallyBijective.{t + 1, t, max u (t + 1)} (ProEt.topology U)
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    locallyBijective.{t + 1, t, max u (t + 1)} (ProEt.topology X)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{t + 1, t, max u (t + 1)} RU
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{t + 1, t, max u (t + 1)} RX
  let : MonoidalCategory A := SheafOfModules.monoidalCategory.{t, t + 1, max u (t + 1)} RU
  let : MonoidalCategory B := SheafOfModules.monoidalCategory.{t, t + 1, max u (t + 1)} RX
  let : MonoidalPreadditive A :=
    SheafOfModules.cochainModulesPreadditive.{t + 1, t, max u (t + 1)} RU
  let : MonoidalPreadditive B :=
    SheafOfModules.cochainModulesPreadditive.{t + 1, t, max u (t + 1)} RX
  let : SymmetricCategory A := SheafOfModules.cochainModulesSymmetric.{t + 1, t, max u (t + 1)} RU
  let : SymmetricCategory B := SheafOfModules.cochainModulesSymmetric.{t + 1, t, max u (t + 1)} RX
  let Fext : A ⥤ B := IntegralOpenReduction.extension l E j o
  let T : B ⥤ A := IntegralOpenReduction.restriction l E j o
  let : PreservesFiniteLimits Fext := IntegralOpenReduction.extensionLimits l E j o
  let : PreservesFiniteColimits Fext := IntegralOpenReduction.extensionColimits l E j o
  let : PreservesFiniteLimits T := by
    let : PreservesFiniteLimits
        (SheafOfModules.localizedSystemRestriction RX (IntegralOpenReduction.openObject j)) :=
      SheafOfModules.localizedSystemRestrictionLimits.{t + 1, t, max u (t + 1)} RX
        (IntegralOpenReduction.openObject j)
    change PreservesFiniteLimits
      (SheafOfModules.localizedSystemRestriction RX (IntegralOpenReduction.openObject j) ⋙
        o.integral.inverse)
    exact comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits T := by
    let : PreservesFiniteColimits
        (SheafOfModules.localizedSystemRestriction RX (IntegralOpenReduction.openObject j)) :=
      SheafOfModules.localizedSystemRestrictionColimits.{t + 1, t, max u (t + 1)} RX
        (IntegralOpenReduction.openObject j)
    change PreservesFiniteColimits
      (SheafOfModules.localizedSystemRestriction RX (IntegralOpenReduction.openObject j) ⋙
        o.integral.inverse)
    exact comp_preservesFiniteColimits _ _
  have hm : exactFunctor A A (tensorLeft M) :=
    (exactFunctor A A).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (R := RU) M ≪≫
        (BraidedCategory.tensorLeftIsoTensorRight M).symm) hM
  have he : exactFunctor B B (tensorLeft (Fext.obj M)) :=
    tensorLeft_exact_of_comparison Fext T μ (by
      intro M M' N N' f g
      simpa only [ordinaryTensorHom] using hn f g) M hm
  exact (exactFunctor B B).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight (Fext.obj M) ≪≫
      (SheafOfModules.siteSheafTensorRightIso (R := RX) (Fext.obj M)).symm) he

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
open CategoryTheory.MonoidalCategory in
private theorem kflat_of_totalComparison (o : Operations l E j)
    (c : TotalComparison l E j o) : KFlatPreservation l E j o := by
  let : EssentiallySmall.{max u (t + 1)} U.ProEt := essentiallySmallSelf _
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let A := scalarReductionSource l E U
  let B := scalarReductionSource l E X
  let RU : Sheaf (ProEt.topology U) CommRingCat.{max u (t + 1)} :=
    completedIntegralCommRingSheafUnrestricted l E U
  let RX : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)} :=
    completedIntegralCommRingSheafUnrestricted l E X
  let : HasSheafify (ProEt.topology U) AddCommGrpCat.{max u (t + 1)} :=
    abelianSheafify.{t + 1, t, max u (t + 1)} (ProEt.topology U)
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} :=
    abelianSheafify.{t + 1, t, max u (t + 1)} (ProEt.topology X)
  let : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    locallyBijective.{t + 1, t, max u (t + 1)} (ProEt.topology U)
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    locallyBijective.{t + 1, t, max u (t + 1)} (ProEt.topology X)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{t + 1, t, max u (t + 1)} RU
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{t + 1, t, max u (t + 1)} RX
  let : MonoidalCategory A := SheafOfModules.monoidalCategory.{t, t + 1, max u (t + 1)} RU
  let : MonoidalCategory B := SheafOfModules.monoidalCategory.{t, t + 1, max u (t + 1)} RX
  let : MonoidalPreadditive A :=
    SheafOfModules.cochainModulesPreadditive.{t + 1, t, max u (t + 1)} RU
  let : MonoidalPreadditive B :=
    SheafOfModules.cochainModulesPreadditive.{t + 1, t, max u (t + 1)} RX
  let : SymmetricCategory A := SheafOfModules.cochainModulesSymmetric.{t + 1, t, max u (t + 1)} RU
  let : SymmetricCategory B := SheafOfModules.cochainModulesSymmetric.{t + 1, t, max u (t + 1)} RX
  let : ∀ (P C : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor P C (curriedTensor A) (.up ℤ) :=
    SheafOfModules.ringedOpenHasTotalTensor.{t + 1, t, max u (t + 1)} RU
  let : ∀ (P C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C (curriedTensor B) (.up ℤ) :=
    SheafOfModules.ringedOpenHasTotalTensor.{t + 1, t, max u (t + 1)} RX
  let Fext : A ⥤ B := IntegralOpenReduction.extension l E j o
  let T : B ⥤ A := IntegralOpenReduction.restriction l E j o
  let : PreservesFiniteLimits Fext := IntegralOpenReduction.extensionLimits l E j o
  let : PreservesFiniteColimits Fext := IntegralOpenReduction.extensionColimits l E j o
  let : PreservesFiniteLimits T := by
    let : PreservesFiniteLimits
        (SheafOfModules.localizedSystemRestriction RX (IntegralOpenReduction.openObject j)) :=
      SheafOfModules.localizedSystemRestrictionLimits.{t + 1, t, max u (t + 1)} RX
        (IntegralOpenReduction.openObject j)
    change PreservesFiniteLimits
      (SheafOfModules.localizedSystemRestriction RX (IntegralOpenReduction.openObject j) ⋙
        o.integral.inverse)
    exact comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits T := by
    let : PreservesFiniteColimits
        (SheafOfModules.localizedSystemRestriction RX (IntegralOpenReduction.openObject j)) :=
      SheafOfModules.localizedSystemRestrictionColimits.{t + 1, t, max u (t + 1)} RX
        (IntegralOpenReduction.openObject j)
    change PreservesFiniteColimits
      (SheafOfModules.localizedSystemRestriction RX (IntegralOpenReduction.openObject j) ⋙
        o.integral.inverse)
    exact comp_preservesFiniteColimits _ _
  intro Q hQ _hf
  apply (SheafOfModules.kFlat_totalTensor_iff RX _).mpr
  exact SheafOfModules.kFlat_map_of_presented_comparison Fext T
    (SheafOfModules.acyclic_map Fext) (SheafOfModules.acyclic_map T)
    (curriedTensor A).map₂CochainComplex (curriedTensor B).map₂CochainComplex rfl rfl
    (fun P C ↦ (c.chain P C).symm) Q
      ((SheafOfModules.kFlat_totalTensor_iff RU Q).mp hQ)

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
/-- Existence of the simultaneous, generator-normalized, unbounded open comparison.
The input calculi and semilinear section construction are fixed, not replaced by arbitrary
families of evaluated arrows. The section construction is the specified one: its slice
restriction evaluation is the identity on sections, so by its unit equation the level
extension evaluation is the actual summand identification, not one twisted by a levelwise
automorphism. Neither completeness nor quasi-compactness is assumed.

Source: Stacks sites-modules.tex, Tag 0E8I; sites-cohomology.tex, Tag 0GL1.
(blueprint: lem-sf-open-semilinear-tensor-model).

Proof:
1. Identify the open site with the ambient slice. On extension-presheaf generators
send [x] tensor a to [x tensor a restricted to the slice]. Tensor balancing,
restriction compatibility and bilinear sheafification existence give the map;
bilinear sheafification uniqueness proves naturality.
2. Transpose the open unit tensored with 1, using restriction/tensor comparison.
It sends [x tensor a] back to [x] tensor a. The two inverse identities follow on
these generators, by sheafification uniqueness and the tensor universal property.
3. Sum the ordinary maps over a+b=d. Extension preserves these direct sums as a
left adjoint. Naturality in the two differentials gives the chain equation for
d_Q tensor 1 + (-1)^a 1 tensor d_F; the same calculation gives chain naturality.
This works without boundedness, since each source summand has two outgoing terms.
4. Exact restriction, tensoring by a flat term, and exact extension prove flatness
of every extended term. The ringed open total-tensor K-flat theorem proves K-flatness
and preservation of resolutions, so the extended representative computes j_!K.
5. Specialize simultaneously to every quotient coefficient in degree zero.
The generator formulas commute with every quotient and with x mapped to x tensor 1
on both sides. Thus the natural maps form an isomorphism of strict semilinear
systems, whose termwise extension to complexes is already a chain isomorphism.
6. Localize this single chain isomorphism using the augmented computation comparisons.
Descent along the localization of flat-term K-flat models gives the natural r on
all derived inputs. Its model square proves independence under changes of representative.
7. At every level the inverse is the open-unit tensor adjunct from step 2, hence
is the canonical normalized derived open tensor inverse. The same strict chain
maps, quotient identities and scalar augmentations are used for the specified
semilinear section construction before scalar restriction. No argument infers
equality of arbitrary system arrows from equality of their evaluations. -/
theorem openSemilinearTensorModel
    (_hlX : IsUnit (l : Γ(X, ⊤))) (_hlU : IsUnit (l : Γ(U, ⊤)))
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (_cX : CoefficientDerivedSystemCoherence l E X SX)
    (_cU : CoefficientDerivedSystemCoherence l E U SU)
    (sections : SemilinearDerivedSectionsData.{t + 1, t, max u (t + 1)}
      (ProEt.topology X) (IntegralOpenReduction.rings l E X)
      (IntegralOpenReduction.transitions l E X))
    (_hsections : ∀ (n : ℕ) N V x,
      HEq ((((sections.localization (IntegralOpenReduction.openObject j)).restrictionEvaluation
        n).hom.app N).val.app V x) x) :
    ∃ (o : Operations l E j) (AX : OrdinaryReduction l E X) (AU : OrdinaryReduction l E U)
      (tc : IntegralOpenReduction.TensorComparison l E j o),
      o.openSystems = sections.localization (IntegralOpenReduction.openObject j) ∧
        Nonempty (Comparison l E j o SX SU AX AU tc) := by
  obtain ⟨o, AX, AU, tc, μ, ordinary, ho, hn, hg, hc⟩ :=
    openSemilinearOrdinaryComparison l E j sections _hsections
  obtain ⟨ct⟩ := totalComparison_of_ordinary l E j o μ hn hg
  have hf : ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E U) Q →
      flatTerms.{t + 1, t, max u (t + 1)} (ProEt.topology U)
        (completedIntegralCommRingSheafUnrestricted l E U) Q →
      flatTerms.{t + 1, t, max u (t + 1)} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)
        ((extensionComplex l E j o).obj Q) := by
    intro Q _hQ hQ i
    exact flat_of_ordinary l E j o μ hn (Q.X i) (hQ i)
  have hk := kflat_of_totalComparison l E j o ct
  obtain ⟨r, hr⟩ := openSemilinearReductionDescent l E j SX SU _cX _cU
    o AX AU ordinary hk hf
  exact ⟨o, AX, AU, tc, ho, ⟨⟨ct, hf, hk, ordinary, hc, r, hr⟩⟩⟩

end WeilConjectures.OpenSemilinearTensor
