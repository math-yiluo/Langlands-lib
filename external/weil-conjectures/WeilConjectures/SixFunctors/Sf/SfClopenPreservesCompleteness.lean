/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
import WeilConjectures.SixFunctors.Sf.SfClopenScalarQuotientComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
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
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenTensorCalculus
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
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
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Derived completeness under clopen restriction

Source: Stacks Project, Tags 08TC and 06YY.
(blueprint: lem-sf-clopen-preserves-completeness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem exact_derived_products
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (I : Type*) [HasProductsOfShape I A] [HasProductsOfShape I B]
    [HasExactLimitsOfShape (Discrete I) A] [HasExactLimitsOfShape (Discrete I) B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete I) F] :
    PreservesLimitsOfShape (Discrete I) F.mapDerivedCategory := by
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  have : PreservesLimitsOfShape (Discrete I) (F.mapHomologicalComplex (.up ℤ)) := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    exact inferInstanceAs
      (PreservesLimitsOfShape (Discrete I) (HomologicalComplex.eval A (.up ℤ) n ⋙ F))
  have : PreservesLimitsOfShape (Discrete I) (Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  have hrep (K : I → CochainComplex A ℤ) :
      PreservesLimit (Discrete.functor (fun i ↦ Q.obj (K i))) F.mapDerivedCategory := by
    apply preservesLimit_of_preserves_limit_cone (DerivedCategory.isLimitFanQ K)
    exact (isLimitMapConeFanMkEquiv F.mapDerivedCategory _ _).symm
      (isLimitFanMkObjOfIsLimit (Q ⋙ F.mapDerivedCategory) K _ (productIsProduct K))
  have (K : I → DerivedCategory A) :
      PreservesLimit (Discrete.functor K) F.mapDerivedCategory := by
    let K' : I → CochainComplex A ℤ := fun i ↦ Q.objPreimage (K i)
    let : PreservesLimit (Discrete.functor (fun i ↦ Q.obj (K' i)))
        F.mapDerivedCategory := hrep K'
    exact preservesLimit_of_iso_diagram F.mapDerivedCategory
      (Discrete.natIso (F := Discrete.functor fun i ↦ Q.obj (K' i))
        (G := Discrete.functor K) fun i ↦ Q.objObjPreimageIso (K i.as))
  exact preservesLimitsOfShape_of_discrete F.mapDerivedCategory

private theorem clopen_derived_products
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) :
    PreservesLimitsOfShape (Discrete ℕ) (sfClopenDerivedRestriction d) := by
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  let := integralCoefficientAbSheafify.{t, u} U.toScheme
  let := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  let R := completedIntegralCoefficientSheafUnrestricted l E T
  let S := completedIntegralCoefficientSheafUnrestricted l E U.toScheme
  let := SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, max u (t + 1), 0}
    (Scheme.ProEt.topology T) R
  let := SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, max u (t + 1), 0}
    (Scheme.ProEt.topology U.toScheme) S
  let := Scheme.ProEt.products_exact.{t, u, 0} T R ℕ
  let := Scheme.ProEt.products_exact.{t, u, 0} U.toScheme S ℕ
  let F := sfClopenModuleRestriction U R S d.completion
  let G := SheafOfModules.pushforward.{max u (t + 1)}
    (F := sfClopenSiteInclusion U) d.completion.hom
  let : G.IsRightAdjoint :=
    SheafOfModules.module_pushforward_isRightAdjoint_of_universes d.completion.hom
  let e : G ≅ F := Iso.refl _
  have : PreservesLimitsOfShape (Discrete ℕ) F := preservesLimitsOfShape_of_natIso e
  exact exact_derived_products ℕ F

private theorem clopen_kflat
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (hU : IsClosed (U : Set T)) (d : SfClopenCoefficientRestriction l E T U)
    (P : CochainComplex (scalarReductionSource l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E U.toScheme)
      ((sfClopenComplexRestriction d).obj P) := by
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  let := integralCoefficientAbSheafify.{t, u} U.toScheme
  let := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  let V : T.Opens := ⟨(U : Set T)ᶜ, hU.isOpen_compl⟩
  let W : Bool → T.Opens := fun b ↦ if b then V else U
  let Y : Bool → Scheme.{t} := fun b ↦ (W b).toScheme
  let j : ∀ b, Y b ⟶ T := fun b ↦ (W b).ι
  have hopen : ∀ b, IsOpenImmersion (j b) := fun _ ↦ inferInstance
  have hr (b : Bool) : Set.range (j b) = (W b : Set T) := (W b).range_ι
  have hclosed : ∀ b, IsClosedImmersion (j b) := by
    intro b
    apply IsClosedImmersion.of_isPreimmersion
    rw [hr]
    cases b
    · exact hU
    · exact U.isOpen.isClosed_compl
  have hdisj : Pairwise (fun b c ↦ Disjoint (Set.range (j b)) (Set.range (j c))) := by
    intro b c hbc
    rw [hr, hr]
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact disjoint_compl_right
    · exact disjoint_compl_left
    · exact (hbc rfl).elim
  have hcover : ∀ x : T, ∃ b, x ∈ Set.range (j b) := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨false, by rw [hr]; exact hx⟩
    · exact ⟨true, by rw [hr]; exact hx⟩
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let S := completedIntegralCommRingSheafUnrestricted l E U.toScheme
  have hk := ((Scheme.ProEt.FiniteClopenTensor.finite_clopen_tensor_calculus
    T Bool Y j hdisj hcover R).2.1 P).mp hP false
  let c : S ≅ (Scheme.ProEt.FiniteClopenTensor.rings.{t, u} U.ι).obj R :=
    (sheafCompose (Scheme.ProEt.topology U.toScheme)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).preimageIso d.completion
  have hc : (sheafCompose (Scheme.ProEt.topology U.toScheme)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map c.hom =
        d.completion.hom := by
    simp [c]
  obtain ⟨tr⟩ := SheafOfModules.ringIso_tensor_transport c
  have ht := (tr.kflat_iff
    (((Scheme.ProEt.FiniteClopenTensor.restriction U.ι R).mapHomologicalComplex
      (.up ℤ)).obj P)).mpr hk
  simp only [SheafOfModules.scalarRestriction, hc] at ht
  change CochainComplex.IsKFlatIndependentCoefficients (R := S) _
  convert ht using 1
  rfl

private theorem sf_clopen_localization_naturality
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U)
    {P Q : CochainComplex (scalarReductionSource l E T) ℤ} (f : P ⟶ Q) :
    (sfClopenDerivedRestriction d).map (DerivedCategory.Q.map f) ≫
        (sfClopenLocalizationIso d Q).hom =
      (sfClopenLocalizationIso d P).hom ≫
        DerivedCategory.Q.map ((sfClopenComplexRestriction d).map f) := by
  let := d.additive
  let := d.limits
  let := d.colimits
  exact (sfClopenModuleRestriction U _ _ d.completion).mapDerivedCategoryFactors_hom_naturality f

private theorem sf_clopen_transition_tensor
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t})
    (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) (q : ℤ)
    (V : T.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E T (n + 1)).obj.obj V)
    (x : (P.X q).val.obj V) :
    ((unrestrictedTowerTransition l E T P n).f q).val.app V
        (unrestrictedTowerTensorSection l E T (n + 1) (P.X q) V s x) =
      unrestrictedTowerTensorSection l E T n (P.X q) V
        ((integralCoefficientSheafTransition l E T n).hom.app V s) x := by
  exact (unrestrictedIntegralTransition_existsUnique l E T n).exists.choose_spec P q V s x

private theorem clopen_augmented_tower
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (hU : IsClosed (U : Set T)) (d : SfClopenCoefficientRestriction l E T U) :
    ∃ tower : ∀ P : CochainComplex (scalarReductionSource l E T) ℤ,
      canonicalIntegralReductionTower l E T P ⋙ sfClopenDerivedRestriction d ≅
        canonicalIntegralReductionTower l E U.toScheme ((sfClopenComplexRestriction d).obj P),
      ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
        (sfClopenDerivedRestriction d).map
            (DerivedCategory.Q.map (unrestrictedTowerUnit l E T P n)) ≫
          (tower P).hom.app (op n) =
        (sfClopenLocalizationIso d P).hom ≫
          DerivedCategory.Q.map (unrestrictedTowerUnit l E U.toScheme
            ((sfClopenComplexRestriction d).obj P) n) := by
  obtain ⟨_, _, quotient, _, _, hquotient⟩ :=
    sf_clopen_scalar_quotient_comparison l E T U hU d
  have htransition (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :
      (sfClopenComplexRestriction d).map (unrestrictedTowerTransition l E T P n) ≫
          (quotient P n).hom =
        (quotient P (n + 1)).hom ≫
          unrestrictedTowerTransition l E U.toScheme ((sfClopenComplexRestriction d).obj P) n := by
    apply (cancel_epi (quotient P (n + 1)).inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    apply HomologicalComplex.hom_ext
    intro q
    apply unrestrictedReduction_hom_ext l E U.toScheme (n + 1)
    intro V s x
    change ((quotient P n).hom.f q).val.app V
        (((unrestrictedTowerTransition l E T P n).f q).val.app
          (op ((sfClopenSiteInclusion U).obj V.unop))
          (((quotient P (n + 1)).inv.f q).val.app V
            (unrestrictedTowerTensorSection l E U.toScheme (n + 1)
              (((sfClopenComplexRestriction d).obj P).X q) V s x))) =
      ((unrestrictedTowerTransition l E U.toScheme
        ((sfClopenComplexRestriction d).obj P) n).f q).val.app V
          (unrestrictedTowerTensorSection l E U.toScheme (n + 1)
            (((sfClopenComplexRestriction d).obj P).X q) V s x)
    have hinv :
        ((quotient P (n + 1)).inv.f q).val.app V
            (unrestrictedTowerTensorSection l E U.toScheme (n + 1)
              (((sfClopenComplexRestriction d).obj P).X q) V s x) =
          unrestrictedTowerTensorSection l E T (n + 1) (P.X q)
            (op ((sfClopenSiteInclusion U).obj V.unop))
            ((d.finite (n + 1)).hom.hom.app V s) x := by
      have h := congrArg (((quotient P (n + 1)).inv.f q).val.app V)
        (hquotient P (n + 1) q V.unop s x)
      have hid := congrArg
        (fun f ↦ ((f.f q).val.app V)
          (unrestrictedTowerTensorSection l E T (n + 1) (P.X q)
            (op ((sfClopenSiteInclusion U).obj V.unop))
            ((d.finite (n + 1)).hom.hom.app V s) x))
        (quotient P (n + 1)).hom_inv_id
      exact h.symm.trans hid
    rw [hinv, sf_clopen_transition_tensor, sf_clopen_transition_tensor]
    have hcoeff :
        (integralCoefficientSheafTransition l E T n).hom.app
            (op ((sfClopenSiteInclusion U).obj V.unop))
            ((d.finite (n + 1)).hom.hom.app V s) =
          (d.finite n).hom.hom.app V
            ((integralCoefficientSheafTransition l E U.toScheme n).hom.app V s) := by
      exact congrArg (fun f ↦ (f.hom.app V).hom s) (d.transition n)
    rw [hcoeff]
    exact hquotient P n q V.unop
      ((integralCoefficientSheafTransition l E U.toScheme n).hom.app V s) x
  have hunit (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :
      (sfClopenComplexRestriction d).map (unrestrictedTowerUnit l E T P n) ≫
          (quotient P n).hom =
        unrestrictedTowerUnit l E U.toScheme ((sfClopenComplexRestriction d).obj P) n := by
    ext q V x
    change ((quotient P n).hom.f q).val.app V
        (((unrestrictedTowerUnit l E T P n).f q).val.app
          (op ((sfClopenSiteInclusion U).obj V.unop)) x) =
      ((unrestrictedTowerUnit l E U.toScheme
        ((sfClopenComplexRestriction d).obj P) n).f q).val.app V x
    have hglobal := congrArg (((quotient P n).hom.f q).val.app V)
      (unrestrictedTowerUnit_condition l E T P n q
        (op ((sfClopenSiteInclusion U).obj V.unop)) x)
    have hlocal := unrestrictedTowerUnit_condition l E U.toScheme
      ((sfClopenComplexRestriction d).obj P) n q V x
    apply hglobal.trans
    apply Eq.trans _ hlocal.symm
    simpa only [map_one] using hquotient P n q V.unop 1 x
  let component (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :=
    sfClopenLocalizationIso d (unrestrictedTowerComplex l E T n P) ≪≫
      DerivedCategory.Q.mapIso (quotient P n)
  have naturality (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :
      (sfClopenDerivedRestriction d).map
          (DerivedCategory.Q.map (unrestrictedTowerTransition l E T P n)) ≫
          (component P n).hom =
        (component P (n + 1)).hom ≫
          DerivedCategory.Q.map
            (unrestrictedTowerTransition l E U.toScheme
              ((sfClopenComplexRestriction d).obj P) n) := by
    dsimp only [component, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, sf_clopen_localization_naturality, Category.assoc,
      ← DerivedCategory.Q.map_comp, htransition, DerivedCategory.Q.map_comp, Category.assoc]
  let comparison (P : CochainComplex (scalarReductionSource l E T) ℤ) :
      canonicalIntegralReductionTower l E T P ⋙ sfClopenDerivedRestriction d ⟶
        canonicalIntegralReductionTower l E U.toScheme
          ((sfClopenComplexRestriction d).obj P) :=
    NatTrans.ofOpSequence (fun n ↦ (component P n).hom) (by
      intro n
      simpa only [Functor.comp_map, canonicalIntegralReductionTower,
        Functor.ofOpSequence_map_homOfLE_succ] using naturality P n)
  let tower (P : CochainComplex (scalarReductionSource l E T) ℤ) :
      canonicalIntegralReductionTower l E T P ⋙ sfClopenDerivedRestriction d ≅
        canonicalIntegralReductionTower l E U.toScheme
          ((sfClopenComplexRestriction d).obj P) :=
    NatIso.ofComponents (fun n ↦ component P n.unop) (by
      intro i j f
      exact (comparison P).naturality f)
  refine ⟨tower, ?_⟩
  intro P n
  change (sfClopenDerivedRestriction d).map
      (DerivedCategory.Q.map (unrestrictedTowerUnit l E T P n)) ≫
        ((sfClopenLocalizationIso d (unrestrictedTowerComplex l E T n P)).hom ≫
          DerivedCategory.Q.map (quotient P n).hom) = _
  rw [← Category.assoc, sf_clopen_localization_naturality, Category.assoc,
    ← DerivedCategory.Q.map_comp, hunit]

private theorem roos_transport
    {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (Φ : C ⥤ D) [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Additive]
    {K : ℕ → C} [HasProduct K]
    [PreservesLimit (Discrete.functor K) Φ]
    {K' : ℕ → D} (f : ∀ n, K (n + 1) ⟶ K n)
    (f' : ∀ n, K' (n + 1) ⟶ K' n) (e : ∀ n, Φ.obj (K n) ≅ K' n)
    (hnat : ∀ n, Φ.map (f n) ≫ (e n).hom = (e (n + 1)).hom ≫ f' n)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f L p δ)
    (legs : ∀ n, Φ.obj L ⟶ K' n)
    (hlegs : ∀ n, legs n = Φ.map (p ≫ Pi.π K n) ≫ (e n).hom) :
    ∃ hprod : HasProduct K', letI := hprod
      ∃ δ' : (∏ᶜ K') ⟶ (Φ.obj L)⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle f' (Φ.obj L) (Pi.lift legs) δ' := by
  let P := Fan.mk (Φ.obj (∏ᶜ K)) (fun n ↦ Φ.map (Pi.π K n) ≫ (e n).hom)
  let hP₀ := isLimitFanMkObjOfIsLimit Φ K (Pi.π K) (productIsProduct K)
  have hP : IsLimit P := Fan.IsLimit.mk P
    (fun s ↦ Fan.IsLimit.lift hP₀ (fun n ↦ s.proj n ≫ (e n).inv))
    (by
      intro s n
      change (Fan.IsLimit.lift hP₀ _) ≫ (Φ.map (Pi.π K n) ≫ (e n).hom) = _
      have hf := Fan.IsLimit.fac hP₀ (fun n ↦ s.proj n ≫ (e n).inv) n
      change Fan.IsLimit.lift hP₀ _ ≫ Φ.map (Pi.π K n) = _ at hf
      rw [← Category.assoc, hf]
      simp)
    (by
      intro s m hm
      apply Fan.IsLimit.hom_ext hP₀
      intro n
      rw [Fan.IsLimit.fac]
      have hn := hm n
      change m ≫ (Φ.map (Pi.π K n) ≫ (e n).hom) = _ at hn
      rw [← Category.assoc] at hn
      exact (Iso.eq_comp_inv (e n)).mpr hn)
  let hprod : HasProduct K' := ⟨⟨P, hP⟩⟩
  let := hprod
  let b : Φ.obj (∏ᶜ K) ≅ ∏ᶜ K' := hP.conePointUniqueUpToIso (productIsProduct K')
  have hb (n : ℕ) : b.hom ≫ Pi.π K' n = Φ.map (Pi.π K n) ≫ (e n).hom :=
    hP.conePointUniqueUpToIso_hom_comp (productIsProduct K') ⟨n⟩
  have hp : Φ.map p ≫ b.hom = Pi.lift legs := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hb, Pi.lift_comp_π, ← Category.assoc, ← Φ.map_comp, hlegs]
  have ht : Φ.map (towerTransitionEndomorphism f) ≫ b.hom =
      b.hom ≫ towerTransitionEndomorphism f' := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hb, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Pi.lift_comp_π,
      Functor.map_sub]
    simp only [← Category.assoc, ← Φ.map_comp, Pi.lift_comp_π, Category.id_comp]
    rw [Φ.map_comp, Category.assoc, hnat, ← Category.assoc, ← hb]
    simp only [Category.assoc]
    simpa only [Category.assoc] using
      congrArg (fun v ↦ b.hom ≫ Pi.π K' n - v ≫ f' n) (hb (n + 1)).symm
  refine ⟨hprod, b.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app L, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ (Φ.map_distinguished _ h)
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) b.symm b.symm ?_ ?_ ?_
  · change Pi.lift legs ≫ b.inv = 𝟙 _ ≫ Φ.map p
    rw [← hp]
    simp
  · change towerTransitionEndomorphism f' ≫ b.inv =
      b.inv ≫ Φ.map (towerTransitionEndomorphism f)
    apply (cancel_epi b.hom).1
    rw [← Category.assoc, ← ht]
    simp
  · simp

private instance clopen_commShift
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) :
    (sfClopenDerivedRestriction d).CommShift ℤ := by
  unfold sfClopenDerivedRestriction
  infer_instance

private instance clopen_triangulated
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) :
    (sfClopenDerivedRestriction d).IsTriangulated := by
  dsimp [sfClopenDerivedRestriction, clopen_commShift]
  infer_instance

private instance clopen_additive
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) :
    (sfClopenDerivedRestriction d).Additive := by
  unfold sfClopenDerivedRestriction
  infer_instance

/-- Derived completeness under clopen restriction.

Source: Stacks Project, Tags 08TC and 06YY; the Roos paragraph of
lem-sf-clopen-derived-compatibility
(blueprint: lem-sf-clopen-preserves-completeness).

Proof: Choose the K-flat resolution and the specified augmented Roos triangle in the
global completeness witness. Ordinary module restriction is a right adjoint and
preserves products. Exact products on the two pro-etale module categories imply
that localization preserves products, and hence the induced derived restriction
preserves them as well. Apply the finite-clopen tensor calculus to U and its open
complement, and then transport along the completed coefficient isomorphism, to
obtain a restricted K-flat complex. Its identity resolution, together with the
mapped localization isomorphism, supplies the local representative. The normalized quotient
comparison commutes with transitions and with x mapping to 1 tensor x. Thus the
image of the global augmented tower is isomorphic to the local augmented tower.
Apply the triangulated restriction functor to the Roos triangle and identify its
two product vertices with the local product using the projection equations. On
projection n, its middle map is pi_n minus tau_n pi_(n+1), hence exactly the local
Roos endomorphism. Its first map is the local canonical augmentation, by the unit
comparison. Transport the connecting map along the product and shift isomorphisms.
This gives the required local completeness witness with the same auxiliary finite
field datum. If U is empty, the image triangle is the zero distinguished triangle. -/
theorem sf_clopen_preserves_completeness
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (hU : IsClosed (U : Set T)) (d : SfClopenCoefficientRestriction l E T U) :
    ∀ M : DerivedCategory (scalarReductionSource l E T),
    IsDerivedCompleteUnrestricted l E T M →
      IsDerivedCompleteUnrestricted l E U.toScheme ((sfClopenDerivedRestriction d).obj M) := by
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  let := integralCoefficientAbSheafify.{t, u} U.toScheme
  let := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  let := d.additive
  let := d.limits
  let := d.colimits
  intro M hM
  obtain ⟨D, hl, P, G, q, hq, e, hprod, δ, hδ⟩ := hM
  let : QuasiIso q := hq.1
  let Φ := sfClopenDerivedRestriction d
  let Ψ := sfClopenComplexRestriction d
  let : PreservesLimitsOfShape (Discrete ℕ) Φ := clopen_derived_products d
  let eP :=
    integralTowerAugmentationIso l E T D hl q hq ≪≫ e
  let e' : DerivedCategory.Q.obj (Ψ.obj P) ≅ Φ.obj M :=
    (sfClopenLocalizationIso d P).symm ≪≫ Φ.mapIso eP
  have hP' := clopen_kflat T U hU d P hq.2
  have hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheaf l E U.toScheme D hl) (𝟙 (Ψ.obj P)) :=
    ⟨inferInstance, hP'⟩
  refine ⟨D, hl, Ψ.obj P, Ψ.obj P, 𝟙 _, hq', e', ?_⟩
  let K : ℕ → DerivedCategory (scalarReductionSource l E T) :=
    fun n ↦ (integralReductionTower l E T D hl P).obj (op n)
  let : HasProduct K := hprod
  let c := (integralReductionTowerCone l E T D hl q hq).extend e.inv
  let p : M ⟶ ∏ᶜ K := Pi.lift (fun n ↦ c.π.app (op n))
  obtain ⟨tower, hunit⟩ := clopen_augmented_tower T U hU d
  have hn (n : ℕ) : Φ.map
        (DerivedCategory.Q.map (unrestrictedTowerTransition l E T P n)) ≫
        (tower P).hom.app (op n) =
      (tower P).hom.app (op (n + 1)) ≫ DerivedCategory.Q.map
        (unrestrictedTowerTransition l E U.toScheme (Ψ.obj P) n) := by
    simpa only [canonicalIntegralReductionTower, Functor.comp_map,
      Functor.ofOpSequence_map_homOfLE_succ] using
        (tower P).hom.naturality (homOfLE n.le_succ).op
  let K' : ℕ → DerivedCategory (scalarReductionSource l E U.toScheme) :=
    fun n ↦ (integralReductionTower l E U.toScheme D hl (Ψ.obj P)).obj (op n)
  let legs (n : ℕ) : Φ.obj M ⟶ K' n := e'.inv ≫ DerivedCategory.Q.map
    (integralTowerUnit l E U.toScheme D hl (Ψ.obj P) n)
  have hlegs (n : ℕ) : legs n =
      Φ.map (p ≫ Pi.π K n) ≫ (tower P).hom.app (op n) := by
    dsimp only [p]
    rw [Pi.lift_comp_π]
    change legs n = Φ.map (e.inv ≫ integralReductionTowerMap l E T D hl q hq n) ≫ _
    rw [integralReductionTowerMap, integralTowerUnit_eq]
    dsimp only [legs]
    rw [integralTowerUnit_eq]
    rw [Φ.map_comp, Φ.map_comp, Category.assoc, Category.assoc, hunit]
    simp only [e', eP, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
      Φ.map_comp, Category.assoc]
    rfl
  obtain ⟨hprod', δ', hδ'⟩ := roos_transport Φ (K := K) (K' := K')
    (fun n ↦ (integralReductionTower l E T D hl P).map (homOfLE n.le_succ).op)
    (fun n ↦ (integralReductionTower l E U.toScheme D hl (Ψ.obj P)).map
      (homOfLE n.le_succ).op)
    (fun n ↦ (tower P).app (op n)) (by
      intro n
      dsimp only [integralReductionTower]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ,
        integralTowerTransition_eq, integralTowerTransition_eq]
      exact hn n) M p δ hδ legs hlegs
  let := hprod'
  refine ⟨hprod', δ', ?_⟩
  have hf : (Pi.lift (fun n : ℕ ↦
      ((integralReductionTowerCone l E U.toScheme D hl (𝟙 (Ψ.obj P)) hq').extend
        e'.inv).π.app (op n))) = Pi.lift legs := by
    apply Pi.hom_ext
    intro n
    rw [Pi.lift_comp_π, Pi.lift_comp_π]
    change e'.inv ≫
      (integralTowerAugmentationIso l E U.toScheme D hl (𝟙 (Ψ.obj P)) hq').inv ≫
        DerivedCategory.Q.map (integralTowerUnit l E U.toScheme D hl (Ψ.obj P) n) = _
    change e'.inv ≫ inv (DerivedCategory.Q.map (𝟙 (Ψ.obj P))) ≫
      DerivedCategory.Q.map (integralTowerUnit l E U.toScheme D hl (Ψ.obj P) n) =
        e'.inv ≫ DerivedCategory.Q.map (integralTowerUnit l E U.toScheme D hl (Ψ.obj P) n)
    have hid : inv (DerivedCategory.Q.map (𝟙 (Ψ.obj P))) = 𝟙 _ := by
      apply IsIso.inv_eq_of_hom_inv_id
      erw [Category.comp_id, DerivedCategory.Q.map_id]
    erw [hid, Category.id_comp]
  rw [hf]
  exact hδ'

end WeilConjectures
