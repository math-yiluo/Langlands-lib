/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels

import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorRamifiedLevel
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelReduction
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeScalarExtension
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import WeilConjectures.CategoryTheory.Finite.FinitePowerComplex
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
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
import WeilConjectures.Algebra.Homology.SmoothPurity.DiagonalConeTransitionHomotopy

/-! # The normalized scalar tensor Roos comparison

Source: Stacks 03EL, 07A4, 0941 and 08TC; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-pur-integral-scalar-tensor-chain-quasi-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor
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
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

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
attribute [local implicit_reducible] integralOperationsRoos
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
    have : IsIso (pc.f i) := hpcf i
    have : IsIso (pc.f (i - 1)) := hpcf (i - 1)
    have : IsIso ((scalarRoosMap F C).f i ≫ eX.hom) := by
      rw [hm]
      change IsIso (((F.mapIso eY) ≪≫
        F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1)) ≪≫
        biprod.mapIso (asIso (pc.f i)) (asIso (pc.f (i - 1)))).hom)
      infer_instance
    have : IsIso eX.hom := eX.isIso_hom
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
    erw [hm, comp_zero, zero_comp]
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

section FiniteTensor

attribute [local implicit_reducible] integralOperationsTensorTowerFunctor

private theorem tensor_tower_generator
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l F W) ℤ)
    {n m : ℕ} (h : n ≤ m) (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((integralOperationsTensorTowerFunctor l F W).obj (P, Q)).map
        (homOfLE h).op).f (p + q)).val.app U
      (integralOperationsTotalTensorSection l F W m P Q p q U
        (unrestrictedIntegralTensorSection l F W m (P.X p) U 1 x)
        (unrestrictedIntegralTensorSection l F W m (Q.X q) U 1 y)) =
    integralOperationsTotalTensorSection l F W n P Q p q U
      (unrestrictedIntegralTensorSection l F W n (P.X p) U 1 x)
      (unrestrictedIntegralTensorSection l F W n (Q.X q) U 1 y) := by
  induction m, h using Nat.le_induction with
  | base => simp; rfl
  | @succ m h ih =>
    have he : (homOfLE (by omega : n ≤ m + 1)).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, Functor.map_comp]
    have hs : ((integralOperationsTensorTowerFunctor l F W).obj (P, Q)).map
        (homOfLE (Nat.le_succ m)).op =
        (integralOperationsTensorTransition l F W m).app (P, Q) := by
      simp only [integralOperationsTensorTowerFunctor, Functor.flip_obj_map,
        Functor.ofOpSequence_map_homOfLE_succ]
    rw [hs]
    change ((((integralOperationsTensorTowerFunctor l F W).obj (P, Q)).map
        (homOfLE h).op).f (p + q)).val.app U
      ((((integralOperationsTensorTransition l F W m).app (P, Q)).f
        (p + q)).val.app U _) = _
    erw [tensor_transition_apply, reduction_transition_apply, reduction_transition_apply]
    have h1 := ((integralCoefficientSheafTransition l F W m).hom.app U).hom.map_one
    erw [h1]
    exact ih

private theorem extended_tensor_hom_ext (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ)
    (H : CochainComplex (integralTowerModules l L W) ℤ)
    (a b : ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj
      ((integralOperationsTensorLevel l E W n).obj (P, Q)) ⟶ H)
    (hab : ∀ (p q : ℤ) (U : W.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      (a.f (p + q)).val.app U
        (integralOrdinaryTensorSection l E L ι W _ U 1
          (integralOperationsTotalTensorSection l E W n P Q p q U
            (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
            (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))) =
      (b.f (p + q)).val.app U
        (integralOrdinaryTensorSection l E L ι W _ U 1
          (integralOperationsTotalTensorSection l E W n P Q p q U
            (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
            (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)))) : a = b := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ((scalarAdjunction l E L ι W).homEquiv _ _).injective
  apply finite_tensor_ext l E W n P Q k
  intro p q hpq U x y
  subst k
  change (a.f (p + q)).val.app U (((scalarAdjunction l E L ι W).unit.app _).val.app U
      (integralOperationsTotalTensorSection l E W n P Q p q U
        (unrestrictedIntegralTensorSection l E W n _ U 1 x)
        (unrestrictedIntegralTensorSection l E W n _ U 1 y))) =
    (b.f (p + q)).val.app U (((scalarAdjunction l E L ι W).unit.app _).val.app U
      (integralOperationsTotalTensorSection l E W n P Q p q U
        (unrestrictedIntegralTensorSection l E W n _ U 1 x)
        (unrestrictedIntegralTensorSection l E W n _ U 1 y)))
  have hs := scalarAdjunction_unit l E L ι W
    (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U
    (integralOperationsTotalTensorSection l E W n P Q p q U
      (unrestrictedIntegralTensorSection l E W n _ U 1 x)
      (unrestrictedIntegralTensorSection l E W n _ U 1 y))
  exact (congrArg ((a.f (p + q)).val.app U) hs).trans
    ((hab p q U x y).trans (congrArg ((b.f (p + q)).val.app U) hs.symm))

private theorem tensor_transition_factorization (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    let C := ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)) ⋙
      (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)
    let D := (integralOperationsTensorTowerFunctor l L W).obj
      ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q))
    let α := (scalarTensorTower l E L ι W).app (P, Q)
    ∃ (m : ℕ) (h : n ≤ m) (b : D.obj (op m) ⟶ C.obj (op n)),
      α.app (op m) ≫ b = C.map (homOfLE h).op ∧
        b ≫ α.app (op n) = D.map (homOfLE h).op := by
  dsimp only
  obtain ⟨m, h, d, hd⟩ := integralScalarTensorRamifiedLevel l E L ι W P Q n
  have hα (k : ℕ) : ((scalarTensorTower l E L ι W).app (P, Q)).app (op k) =
      (scalarTensorLevel l E L ι W k).app (P, Q) :=
    (scalarTensorTower_existsUnique l E L ι W).exists.choose_spec P Q k
  refine ⟨m, h, d.inv, ?_, ?_⟩
  · apply (cancel_mono d.hom).mp
    erw [Category.assoc, d.inv_hom_id, Category.comp_id]
    apply extended_tensor_hom_ext l E L ι W P Q m
    intro p q U x y
    change ((((scalarTensorTower l E L ι W).app (P, Q)).app (op m)).f
        (p + q)).val.app U _ =
      (d.hom.f (p + q)).val.app U
        (((integralOrdinaryScalar l E L ι W).map
          ((((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).map
            (homOfLE h).op).f (p + q))).val.app U _)
    rw [hα]
    erw [(scalarTensorLevel_existsUnique l E L ι W m).exists.choose_spec,
      scalar_map_tensor, tensor_tower_generator, hd]
  · apply (cancel_epi d.hom).mp
    erw [← Category.assoc, d.hom_inv_id, Category.id_comp]
    apply extended_tensor_hom_ext l E L ι W P Q n
    intro p q U x y
    change ((((scalarTensorTower l E L ι W).app (P, Q)).app (op n)).f
        (p + q)).val.app U _ =
      ((((integralOperationsTensorTowerFunctor l L W).obj
        ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q))).map
            (homOfLE h).op).f (p + q)).val.app U
        ((d.hom.f (p + q)).val.app U _)
    rw [hα]
    erw [(scalarTensorLevel_existsUnique l E L ι W n).exists.choose_spec,
      hd, tensor_tower_generator]
    rfl

end FiniteTensor

attribute [local irreducible] integralOperationsTensorTowerFunctor
  integralOperationsTensorLevel scalarTensorTower integralOperationsRoos scalarRoosMap
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  integralOperationsRoosFunctor
set_option backward.defeqAttrib.useBackward true

/-- The prescribed strict scalar tensor comparison is a quasi-isomorphism on good pairs.
Source: Stacks, sites-modules.tex, Tag 03EL; sites-cohomology.tex, Tags 07A4 and 0941;
derived.tex, Tag 08TC; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-pur-integral-scalar-tensor-chain-quasi-iso).
Proof: at every finite source level choose the normalized ramified tensor
isomorphism to a later target level. Its inverse is a diagonal factorization
of both tower transitions, as checked on total pure generators. The diagonal
cone-transition homotopy therefore makes the cone tower pro-zero in the
derived category. The strict-tower homotopy-limit theorem and the strict Roos
comparison show that the specified tower map induces a quasi-isomorphism on
Roos complexes. Finite freeness makes ordinary scalar extension preserve
countable products. The two prescribed Roos coordinates identify its additive
Roos comparison with product and biproduct isomorphisms, so this comparison is
itself an isomorphism. Their composite is exactly scalarTensorChain.
Only the finite ramified tensor isomorphism is postponed. The remaining
argument applies even without flatness or boundedness of the complexes. -/
theorem scalarTensorChainQuasiIso (W : AlgebraicGeometry.Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    QuasiIso (scalarTensorChain l E L ι W P.obj Q.obj) := by
  let C := (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)
  let F := integralOrdinaryScalar l E L ι W
  let α := (scalarTensorTower l E L ι W).app (P.obj, Q.obj)
  have : PreservesLimitsOfShape (Discrete ℕ) F := scalar_products l E L ι W
  have : IsIso (scalarRoosMap F C) := product_roos_isIso F C
  have hα : QuasiIso (integralOperationsRoosMap α) :=
    roos_pro_zero l L W α (by
      intro n
      obtain ⟨m, h, b, hb₁, hb₂⟩ :=
        tensor_transition_factorization l E L ι W P.obj Q.obj n
      have hnull : Nonempty (Homotopy
          ((CochainComplex.mappingCone
            (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l L W)
              α)).asFunctor.map (homOfLE h).op) 0) := by
        apply HomologicalComplex.diagonalConeTransitionHomotopy
          (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l L W) α)
          (homOfLE h).op b
        · intro i
          exact congrArg (fun k ↦ k.f i) hb₁
        · intro i
          exact congrArg (fun k ↦ k.f i) hb₂
      obtain ⟨H⟩ := hnull
      refine ⟨m, h, ?_⟩
      simpa using DerivedCategory.Q_map_eq_of_homotopy (integralTowerModules l L W) H)
  unfold scalarTensorChain
  exact quasiIso_comp (scalarRoosMap F C) (integralOperationsRoosMap α) (hφ' := hα)

end WeilConjectures
