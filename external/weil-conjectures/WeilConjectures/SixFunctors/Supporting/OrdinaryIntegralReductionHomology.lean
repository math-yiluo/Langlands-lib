/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import all WeilConjectures.SmoothPurity.IntegralAmbient.NormalizedIntegralPullbackTower
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import all WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackHomology
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations

/-! # Cohomology of ordinary pullback and finite integral reduction

Source: Stacks Project, Tags 06YY and 0735; Bhatt--Scholze, Lemma 6.5.8.
(blueprint: lem-fix-ordinary-integral-reduction-homology).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local instance] scalarReductionExtensionAdditive

private local instance (priority := 5000) reductionSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
private local instance (priority := 5000) reductionAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private local instance (priority := 5000) reductionAbLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

attribute [local irreducible] HasDerivedCategory.standard scalarReductionExistence
  scalarReductionDerivedExistence

section
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

-- Transfer the ringed-topos K-flat computation to the chosen ordinary adjoint.
private theorem reductionPull_kflat
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      ((ordinaryIntegralPullComplex l E f).obj P) := by
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists f
    (completedIntegralCommRingSheafUnrestricted l E Y)
  have hk := (SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1))) I (ordinaryTensorRingMap l E f)
    (ordinaryTensorPull l E f)
    (fun M ↦ congrArg
      (SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1}
        (ordinaryTensorRingMap l E f)).obj
      (congrArg (fun T ↦ T.obj M) hI.symm))
    (fun {M N} a ↦ ordinaryFunctorMap _ _
      (SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1}
        (ordinaryTensorRingMap l E f)) hI.symm a) P hP.1 hP.2).1
  exact SheafOfModules.kFlat_of_iso_independent
    ((NatIso.mapHomologicalComplex (ordinaryTensorPullIso l E f) (.up ℤ)).app P) hk

-- Use the specified scalar counit, with the cochain/homotopy factorization maps.
private noncomputable def reductionModel (W : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    (scalarReductionDerivedExtension l E W n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) := by
  letI : IsIso ((scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.2.2 P hP
  exact (scalarReductionDerivedExtension l E W n).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    asIso ((scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

-- Both finite pullbacks are left adjoint to the same constant-section direct image.
private noncomputable def reductionFinitePullIso (n : ℕ) :
    integralOperationsLevelPullback l E f n ≅
      proEtaleConstantModulePullbackFunctor f (Padic.coefficientExtensionRing l E (n + 1)) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have hm : proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (asIso (proEtaleCoefficientInverseImageMap f A)) =
      coefficientProEtaleDirectRingMap.{u, u} f
        (CommRingCat.of (ULift.{u + 1} A)) :=
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hd : proEtaleRingModuleDirectImage f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (asIso (proEtaleCoefficientInverseImageMap f A)) =
      coefficientProEtaleModuleDirectImage.{u, u} f
        (CommRingCat.of (ULift.{u + 1} A)) := by
    unfold proEtaleRingModuleDirectImage coefficientProEtaleModuleDirectImage
    rw [hm]
  exact (coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} A))).leftAdjointUniq
      ((proEtaleRingModuleAdjunction f (proEtaleConstantRing Y A)
        (proEtaleConstantRing X A) (asIso (proEtaleCoefficientInverseImageMap f A))).ofNatIsoRight
          (eqToIso hd))

-- The finite-level part of the existing normalized tower comparison.
private noncomputable def reductionOrdinarySquare (n : ℕ) :
    ordinaryIntegralModulePull l E f ⋙ scalarReductionExtension l E X n ≅
      scalarReductionExtension l E Y n ⋙
        proEtaleConstantModulePullbackFunctor f (Padic.coefficientExtensionRing l E (n + 1)) :=
  Functor.isoWhiskerRight (ordinaryAmbientPullIso l E f) (scalarReductionExtension l E X n) ≪≫
    IntegralAmbient.finitePullComparison l E f n ≪≫
    Functor.isoWhiskerLeft (scalarReductionExtension l E Y n) (reductionFinitePullIso l E f n)

end

/-- Finite reduction after ordinary integral pullback has the pulled-back cohomology
of the original finite reduction. No derived completion occurs.

Source: Stacks Project, Tags 06YY (derived tensor pullback) and 0735 (exact pullback
and cohomology); Bhatt--Scholze, Lemma 6.5.8. This is the finite-reduction part of
step 3 of lem-fix-constructible-residue-tree.
(blueprint: lem-fix-ordinary-integral-reduction-homology).

Proof: choose a flat-term K-flat representative P of K. The projection equations
for ordinaryIntegralDirectRingMap give the commutative square of completed and
finite constant coefficient sheaves. Associativity of tensor extension identifies
finite reduction of ordinary pullback of P with constant-coefficient pullback of
the finite reduction of P. The identification sends a pulled section tensored with
a residue coefficient to that same section and coefficient; thus it is compatible
with sheafification, differentials and the resolution counits. Ordinary module
pullback preserves flat modules, so these complexes compute the corresponding
left derived functors; uniqueness compatible with their counits descends the
identification to K. Constant-coefficient pullback is exact, hence commutes with
cohomology. Compose this homology comparison with the descended tensor comparison.
The tensor formulas also include zero modules, the zero coefficient ring and the
empty scheme. Index n denotes the positive exponent n + 1. -/
theorem ordinaryIntegralReductionHomology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y)) (n : ℕ) (q : ℤ) :
    Nonempty (((DerivedCategory.homologyFunctor _ q).obj
      ((scalarReductionDerivedExtension l E X n).obj
        ((ordinaryIntegralDerivedPull l E f).obj K))) ≅
      proEtaleConstantModulePullback f (Padic.coefficientExtensionRing l E (n + 1))
        ((DerivedCategory.homologyFunctor _ q).obj
          ((scalarReductionDerivedExtension l E Y n).obj K))) := by
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let F := proEtaleConstantModulePullbackFunctor f A
  have : F.Additive := proEtaleConstantModulePullbackFunctor_additive f A
  let C := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) C
  have hg : integralOperationsGoodComplex l E Y P := ⟨hp, fun i ↦
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E Y) (P.X i)).symm (hf i)⟩
  have := hq
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have := ordinaryIntegralPullComplexCounit_isIso l E f ⟨P, hg⟩
  let U := (ordinaryIntegralPullComplex l E f).obj P
  let V := ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P
  let b : ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj U ≅
      (F.mapHomologicalComplex (.up ℤ)).obj V :=
    (Functor.mapHomologicalComplexCompIso (reductionOrdinarySquare l E f n) (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (scalarReductionExtension l E Y n ⋙ F)) (.up ℤ)).app P).symm
  let d : (scalarReductionDerivedExtension l E X n).obj
      ((ordinaryIntegralDerivedPull l E f).obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj V) :=
    (scalarReductionDerivedExtension l E X n).mapIso
      ((ordinaryIntegralDerivedPull l E f).mapIso e.symm ≪≫
        asIso (ordinaryIntegralPullComplexCounit l E f P)) ≪≫
    reductionModel l E X n U (reductionPull_kflat l E f P hg) ≪≫
    DerivedCategory.Q.mapIso b
  let r : DerivedCategory.Q.obj V ≅ (scalarReductionDerivedExtension l E Y n).obj K :=
    (reductionModel l E Y n P hp).symm ≪≫
      (scalarReductionDerivedExtension l E Y n).mapIso e
  exact ⟨(DerivedCategory.homologyFunctor _ q).mapIso d ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
    proEtaleConstantModulePullbackHomologyIso f A V q ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso r)⟩

end WeilConjectures
