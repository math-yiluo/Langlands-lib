/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeScalarExtension
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import WeilConjectures.CategoryTheory.Finite.FinitePowerComplex
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackConeProZero
import all WeilConjectures.CategoryTheory.Finite.FiniteFreeStrictTowerTransport
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Quasi-isomorphism of the normalized finite pullback Roos map

Source: Stacks, sites-cohomology.tex, Tags 07A4 and 0941; derived.tex,
Tag 08TC; proetale.tex, Tag 099N (completion context). This is the
cofinal-filtration specialization in the integral scalar comparison proof.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted

attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

section Proofs

attribute [local irreducible] SheafOfModules.unit CategoryTheory.Limits.limit
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
set_option backward.defeqAttrib.useBackward true

private theorem scalar_products (W : AlgebraicGeometry.Scheme.{u}) :
    PreservesLimitsOfShape (Discrete ℕ) (integralOrdinaryScalar l E L ι W) := by
  classical
  let φ := integralCompletedScalarMap l E L ι W
  let := ι.toAlgebra
  obtain ⟨e⟩ := completedIntegralFiniteFree.{u, u} l E W L ι φ
    (integralCompletedScalarMap_projection l E L ι W)
  let A := completedIntegralCoefficientSheafUnrestricted l E W
  let U := SheafOfModules.restrictScalars.{u+1}
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u+1} RingCat.{u+1})).map φ)
  let F := integralOrdinaryScalar l E L ι W
  let α : F ⋙ U ≅ finitePowerFunctor (A := SheafOfModules.{u+1} A)
      (Module.finrank E L) :=
    NatIso.ofComponents (fun M ↦
      U.mapIso (eqToIso (integralOrdinaryScalar_obj l E L ι W M)) ≪≫
        SheafOfModules.scalarExtensionIso φ (Module.finrank E L) e.symm M) (by
      intro M N f
      change U.map (F.map f) ≫ (U.map (eqToHom
          (integralOrdinaryScalar_obj l E L ι W N)) ≫ _) =
        (U.map (eqToHom (integralOrdinaryScalar_obj l E L ι W M)) ≫ _) ≫ _
      rw [integralOrdinaryScalar_map l E L ι W f, Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc, ← U.map_comp_assoc, eqToHom_trans, eqToHom_refl,
        U.map_id, Category.id_comp]
      exact congrArg (fun k ↦ U.map (eqToHom
        (integralOrdinaryScalar_obj l E L ι W M)) ≫ k)
        (SheafOfModules.scalarExtensionIso_naturality φ (Module.finrank E L) e.symm f))
  obtain ⟨href, hlim, _⟩ := SheafOfModules.scalarRestrictionProperties
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u+1} RingCat.{u+1})).map φ)
  have : U.ReflectsIsomorphisms := href
  have : PreservesLimitsOfSize.{u+1, u+1} U := hlim
  have : PreservesLimitsOfSize.{0, 0} U := preservesLimitsOfSize_shrink U
  have : PreservesLimitsOfShape (Discrete ℕ) (F ⋙ U) :=
    preservesLimitsOfShape_of_natIso α.symm
  have : ReflectsLimitsOfShape (Discrete ℕ) U :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves F U

section ProductComparison
universe a b c d
open CochainComplex
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

private noncomputable def coconeCoordinates {K L : CochainComplex A ℤ}
    (φ : K ⟶ L) (i : ℤ) :
    (mappingCocone φ).X i ≅ K.X i ⊞ L.X (i - 1) where
  hom := biprod.lift ((mappingCocone.fst φ).f i)
    ((mappingCocone.snd φ).v i (i - 1) (by omega))
  inv := biprod.desc ((mappingCocone.inl φ).v i i (by omega))
    ((mappingCocone.inr φ).1.v (i - 1) i (by omega))
  hom_inv_id := by simpa using mappingCocone.id_X φ i (i - 1) (by omega)
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

private theorem product_roos_isIso (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : IsIso (scalarRoosMap F C) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let pc := piComparison G (fun n : ℕ ↦ C.obj (op n))
  have hpc : IsIso pc := by dsimp only [pc]; infer_instance
  obtain ⟨hf, hs⟩ := scalarRoosCoordinates F C
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hpcf (i : ℤ) : IsIso (pc.f i) := inferInstance
  have hi (i : ℤ) : IsIso ((scalarRoosMap F C).f i) := by
    let eY := coconeCoordinates (scalarRoosBoundary C) i
    let eX := coconeCoordinates (scalarRoosBoundary (C ⋙ G)) i
    have he : F.map eY.hom ≫
        (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom =
        biprod.lift (F.map ((mappingCocone.fst (scalarRoosBoundary C)).f i))
          (F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
            i (i - 1) (by omega))) :=
      biprod.map_lift_mapBiprod F _ _ _ _
    have hm : (scalarRoosMap F C).f i ≫ eX.hom =
        F.map eY.hom ≫ (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
            ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom ≫
          biprod.map (pc.f i) (pc.f (i - 1)) := by
      rw [← Category.assoc, he]
      apply biprod.hom_ext
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
        exact congrArg (fun f ↦ f.f i) hf
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
        exact hs i
    have : IsIso ((scalarRoosMap F C).f i ≫ eX.hom) := by
      rw [hm]
      change IsIso (((F.mapIso eY) ≪≫
        F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1)) ≪≫
        biprod.mapIso (asIso (pc.f i)) (asIso (pc.f (i - 1)))).hom)
      infer_instance
    exact IsIso.of_isIso_comp_right _ eX.hom
  exact HomologicalComplex.Hom.isIso_of_components _
end ProductComparison

private theorem roos_pro_zero (W : AlgebraicGeometry.Scheme.{u})
    {C D : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ} (α : C ⟶ D)
    (hv : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      (DerivedCategory.Q (C := integralTowerModules.{u, u} l E W)).map
        ((CochainComplex.mappingCone (C := ℕᵒᵖ ⥤ integralTowerModules.{u, u} l E W)
          (koszulTowerComplexMap.{u+1, u, u+1}
            (completedIntegralCommRingSheafUnrestricted l E W) α)).asFunctor.map
            (homOfLE h).op) = 0) : QuasiIso (integralOperationsRoosMap α) := by
  let A := integralTowerModules l E W
  let R := completedIntegralCoefficientSheafUnrestricted l E W
  let : HasDerivedCategory.{u+2} (ringedSiteModules.{u+1} R) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u+2} (ℕᵒᵖ ⥤ ringedSiteModules.{u+1} R) :=
    HasDerivedCategory.standard _
  have : HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u+1} R) :=
    integralOperationsExactProducts l E W
  have hcomm (U : W.ProEtᵒᵖ) (a b : R.obj.obj U) : a * b = b * a :=
    completedIntegralCoefficient_mul_commUnrestricted l E W U a b
  let v := koszulTowerComplexMap.{u+1, u, u+1}
    (completedIntegralCommRingSheafUnrestricted l E W) α
  obtain ⟨RF, η, hRF, hI, _, hshift, hp, E', ε, p, δ, _, _, _, _, _, hi⟩ :=
    ringedStrictTowerHomotopyLimitIndependentCoefficients.{u+2, u+1, u, u+1}
      (AlgebraicGeometry.Scheme.ProEt.topology W) R hcomm
  have hv' : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      (E'.obj (DerivedCategory.Q.obj (CochainComplex.mappingCone v))).map (homOfLE h).op =
        0 := by
    intro n
    obtain ⟨m, h, hm⟩ := hv n
    refine ⟨m, h, ?_⟩
    apply (cancel_mono ((ε.app (CochainComplex.mappingCone v)).hom.app (op n))).1
    have hn := (ε.app (CochainComplex.mappingCone v)).hom.naturality (homOfLE h).op
    dsimp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map] at hn
    rw [hn]
    change _ ≫ DerivedCategory.Q.map
      ((CochainComplex.mappingCone v).asFunctor.map (homOfLE h).op) = 0 ≫ _
    rw [hm, comp_zero, zero_comp]
  have hvRF : IsIso (RF.map (DerivedCategory.Q.map v)) := hi _ _ v hv'
  obtain ⟨CF, k, hCF, _⟩ := strictRoosDerivation.{u+1, u, 0, u+2}
    (AlgebraicGeometry.Scheme.ProEt.topology W) R hcomm
  let := hRF
  let := hCF
  let τ := Functor.isoWhiskerRight
    (strictTowerLimitIso (A := ringedSiteModules.{u+1} R)) DerivedCategory.Q
  have : (DerivedCategory.Q (C := ℕᵒᵖ ⥤ ringedSiteModules.{u+1} R)).IsLocalization
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u+1} R) (.up ℤ)) :=
    inferInstance
  let c := CF.rightDerivedNatIso RF (roosDerivedUnit k) η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u+1} R) (.up ℤ)) τ
  let θ := k ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q c
  have hq : IsIso (DerivedCategory.Q.map (roosF.map v)) :=
    (NatIso.isIso_map_iff θ v).2 hvRF
  have hroos : QuasiIso (roosF.map v) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A _).1 hq
  have heq : integralOperationsRoosMap α = roosF.map v := by
    unfold integralOperationsRoosMap
    rw [cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square α)]
    rfl
  rw [heq]
  exact hroos

end Proofs

/-- The strict, generator-normalized pullback comparison is a quasi-isomorphism
on a good representative, after applying the additive Roos comparison.
Source: Stacks, sites-cohomology.tex, Tags 07A4 and 0941; derived.tex,
Tag 08TC; proetale.tex, Tag 099N supplies the completion context.
This generator-normalized specialization is extracted from the item proof.
(blueprint: lem-pur-integral-scalar-pullback-roos-quasi-iso).
Proof: write the source uniformizer as a unit times the e-th power of the target
uniformizer, with e positive. Completed constant-sheaf reduction and tensor
associativity identify the scalar extension of the source level n with target
level e(n+1)-1. Under this identification, the assumed generator equation makes
alpha the transition from that level to n. These identifications respect every
strict transition and the differentials, by the balanced tensor and inverse-image
universal properties. Finite freeness of the completed coefficient extension
commutes with countable products; the two equations for kappa identify it with
the diagonal product comparison on both summands of the shifted cone. Thus the
displayed composite is the cofinal-filtration comparison on the two Roos
coordinates. Cofinality makes this map a quasi-isomorphism: the transition map from
the arithmetic subsequence to the original tower induces the identity on the
identified inverse limits. Countable products are exact on the pro-etale site.
One may forget to abelian sheaves: the exact conservative forgetful functor
creates products, preserves the Roos coordinates, and detects quasi-isomorphisms.
Applying K-injective tower resolutions and the Roos comparison then proves the
assertion by two-out-of-three. Equivalently, finite
transition sums give a telescoping chain homotopy inverse. K-flatness and termwise flatness
of P identify all finite tensor models with their derived reductions. For e=1
the comparison is the termwise tensor-association isomorphism; zero complexes
and empty sites satisfy the same formulas. No completeness of P is assumed. -/
theorem integralScalarPullbackRoosQuasiIso {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P)
    (α : ((integralOperationsPullbackTowerFunctor l E f).obj P) ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ) ⟶
      (integralOperationsPullbackTowerFunctor l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P))
    (hα :
      ∀ (n : ℕ) (i : ℤ) (V : Y.ProEt)
        (x : (P.X i).val.obj (op V)),
        ((α.app (op n)).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X
            (((integralOperationsPullbackLevel l E f n).obj P).X i)
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
            (integralOperationsPullbackGenerator l E f n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
        integralOperationsPullbackGenerator l L f n
          (((unrestrictedIntegralFiniteComplex l L Y n).obj
            (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)).X i) V
          (unrestrictedIntegralTensorSection l L Y n
            ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) (op V) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x)))
    (κ : ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj
        (integralOperationsRoos ((integralOperationsPullbackTowerFunctor l E f).obj P)) ⟶
      integralOperationsRoos (((integralOperationsPullbackTowerFunctor l E f).obj P) ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)))
    (hκ : let C := (integralOperationsPullbackTowerFunctor l E f).obj P
      let G := (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)
      (∀ n : ℕ, κ ≫ CochainComplex.mappingCocone.fst
          ((towerTransitionEndomorphism (K := fun n ↦ G.obj (C.obj (op n)))
            (integralOperationsTowerStep (C ⋙ G)))) ≫
          Pi.π (fun n ↦ (G).obj (C.obj (op n))) n =
        (G).map
          (CochainComplex.mappingCocone.fst
            ((towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
            (integralOperationsTowerStep C))) ≫
            Pi.π (fun n ↦ C.obj (op n)) n)) ∧
      (∀ (i j : ℤ) (h : i + -1 = j) (n : ℕ), κ.f i ≫
          (CochainComplex.mappingCocone.snd
            ((towerTransitionEndomorphism (K := fun n ↦ G.obj (C.obj (op n)))
            (integralOperationsTowerStep (C ⋙ G))))).v i j h ≫
          (Pi.π (fun n ↦ (G).obj
            (C.obj (op n))) n).f j =
        (integralOrdinaryScalar l E L ι X).map
          ((CochainComplex.mappingCocone.snd
            ((towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
            (integralOperationsTowerStep C)))).v i j h ≫
          (Pi.π (fun n ↦ C.obj (op n)) n).f j))) :
    QuasiIso (κ ≫ integralOperationsRoosMap α) := by
  let C := (integralOperationsPullbackTowerFunctor l E f).obj P
  let F := integralOrdinaryScalar l E L ι X
  have hκeq : κ = scalarRoosMap F C :=
    (scalarRoosMap_existsUnique F C).unique hκ
      (scalarRoosMap_existsUnique F C).exists.choose_spec
  have : PreservesLimitsOfShape (Discrete ℕ) F := scalar_products l E L ι X
  have : IsIso κ := by
    rw [hκeq]
    exact product_roos_isIso F C
  have hαq : QuasiIso (integralOperationsRoosMap α) :=
    roos_pro_zero l L X α (by
      intro n
      obtain ⟨m, h, ⟨H⟩⟩ := integralScalarPullbackConeProZero l E L ι f P hP α hα n
      refine ⟨m, h, ?_⟩
      simpa using
        DerivedCategory.Q_map_eq_of_homotopy (integralTowerModules l L X) H)
  exact quasiIso_comp κ (integralOperationsRoosMap α) (hφ' := hαq)

end WeilConjectures
