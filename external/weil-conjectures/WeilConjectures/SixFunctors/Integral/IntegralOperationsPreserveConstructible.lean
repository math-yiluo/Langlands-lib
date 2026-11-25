/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationRoosEffectivity
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTensorConstructibleCohomology
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import Mathlib.Algebra.Field.ULift
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
import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteLocalConstancyPullback

/-!
# Integral pullback and completed tensor preserve constructibility

Source: Bhatt--Scholze, Lemmas 6.5.3--6.5.5 and 6.5.9(5); Stacks Project,
Tags 099M, 099N, 09BQ and 054I
(blueprint: lem-pur-integral-operations-preserve-constructible).

Finite reductions use index `n` for the positive exponent `n + 1`. The reduction
comparisons below are the adjoints of the actual Roos projections, transported
through the defining representative comparisons of the integral operations.
Their targets compute the finite pullback and finite derived tensor on K-flat
representatives. All good representatives and all identifications with the input
objects are allowed; no resolutions or comparison morphisms are extra hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] integralDerivedPullback integralCompletedTensor
  scalarReductionExistence scalarReductionDerivedExistence

/-- The canonical reduction comparison for integral pullback. Its adjoint is the
Roos projection, after the defining representative comparison and exact-restriction
factorization. Thus this map is fixed, rather than an arbitrary isomorphism.
Source: Stacks Tag 099N(5); Bhatt--Scholze, Lemma 6.5.9(5)
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralPullbackFiniteComparison {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (K : DerivedCategory (integralTowerModules l E Y))
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj ((integralDerivedPullback l E f).obj K) ⟶
      DerivedCategory.Q.obj (integralPullbackFiniteComplex l E f P.obj n) :=
  (((derivedScalarExtensionRestrictionAdjunction l E X n).choose).homEquiv _ _).symm
    ((integralDerivedPullback l E f).map e.inv ≫
      (integralDerivedPullbackComparison l E f).hom.app P ≫
        integralOperationRoosProjection l E X
          ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
          (integralPullbackFiniteComplex l E f P.obj n))

/-- The canonical reduction comparison for the completed integral tensor.
Its adjoint is the actual projection to `Res_n(P_n tensor Q_n)` of the defining Roos
complex. The finite tensor is computed on reduced K-flat representatives.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5; Stacks Tags 099M and 09BQ
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralTensorFiniteComparison (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ M) (d : DerivedCategory.Q.obj Q.obj ≅ N) (n : ℕ) :
    (scalarReductionDerivedExtension l E W n).obj
        ((integralCompletedTensor l E W).obj (M, N)) ⟶
      DerivedCategory.Q.obj (integralTensorFiniteComplex l E W P.obj Q.obj n) :=
  (((derivedScalarExtensionRestrictionAdjunction l E W n).choose).homEquiv _ _).symm
    ((integralCompletedTensor l E W).map (e.inv, d.inv) ≫
      (integralCompletedTensorComparison l E W).hom.app (P, Q) ≫
        integralOperationRoosProjection l E W
          ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)) n ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app
          (integralTensorFiniteComplex l E W P.obj Q.obj n))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem goodRepresentative (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules l E W)) :
    ∃ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _
  have := Localization.essSurj (DerivedCategory.Q (C := integralTowerModules l E W))
    (HomologicalComplex.quasiIso _ (.up ℤ))
  let L := (DerivedCategory.Q (C := integralTowerModules l E W)).objPreimage K
  let e := (DerivedCategory.Q (C := integralTowerModules l E W)).objObjPreimageIso K
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) L
  let : QuasiIso f := hf
  let : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (integralTowerModules l E W) f).2 hf
  have hsite (i : ℤ) : SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (P.X i) := by
    exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (P.X i)).symm (hflat i)
  exact ⟨⟨P, hP, hsite⟩, ⟨asIso (DerivedCategory.Q.map f) ≪≫ e⟩⟩

attribute [local irreducible] unrestrictedIntegralReductionExistence

private theorem finiteReduction_kflat (W : AlgebraicGeometry.Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) :
    CochainComplex.IsAcyclicTensorKFlat
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := integralCoefficientCommRingSheaf.{u, u} l E W n)
      ((unrestrictedIntegralFiniteComplex l E W n).obj P.obj) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W
  let S := integralCoefficientCommRingSheaf.{u, u} l E W n
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} S
  let φ := completedIntegralCommRingProjectionUnrestricted l E W n
  let F := unrestrictedIntegralReductionFunctor l E W n
  let : MonoidalCategory (integralTowerModules l E W) :=
    SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
    SheafOfModules.monoidalCategory.{u, u + 1, u + 1} S
  have ho := (unrestrictedIntegralReductionExistence l E W n).choose_spec.choose
  let e : (F.mapHomologicalComplex (.up ℤ)).obj P.obj ≅
      SheafOfModules.changeOfRingsComplex.{u + 1, u} φ P.obj :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (ho (P.obj.X i))) (by
      intro i j hij
      symm
      change F.map (P.obj.d i j) ≫ eqToHom (ho (P.obj.X j)) =
        eqToHom (ho (P.obj.X i)) ≫
          SheafOfModules.changeOfRingsHom φ (P.obj.X i) (P.obj.d i j)
      have hm : F.map (P.obj.d i j) = eqToHom (ho (P.obj.X i)) ≫
          SheafOfModules.changeOfRingsHom φ (P.obj.X i) (P.obj.d i j) ≫
            eqToHom (ho (P.obj.X j)).symm := by
        set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            exact (unrestrictedIntegralReductionExistence l E W n).choose_spec.choose_spec.choose
              (P.obj.d i j)
      rw [hm]
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  have hflat (i : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.obj.X i)) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R (P.obj.X i)) (P.property.2 i)
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms.{u + 1, u}
    φ P.obj P.property.1 hflat
  let : (MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E W n)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let : ∀ M : integralOperationsFiniteModules l E W n,
      ((MonoidalCategory.curriedTensor _).obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  intro A hA i
  let T := ((MonoidalCategory.curriedTensor
    (integralOperationsFiniteModules l E W n)).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)).obj A
  exact (h.1 A hA i).of_iso (T.mapIso e).symm

private def finiteReductionIso (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules l E W))
    (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ) :
    (scalarReductionDerivedExtension l E W n).obj K ≅
      DerivedCategory.Q.obj ((unrestrictedIntegralFiniteComplex l E W n).obj P.obj) := by
  have hqid : QuasiIso (𝟙 P.obj) := quasiIso_of_isIso (𝟙 P.obj)
  let r := unrestrictedTowerResolutionIso l E W n (𝟙 P.obj) ⟨hqid, P.property.1⟩
  have heq : unrestrictedTowerFiniteComplex l E W n P.obj =
      (unrestrictedIntegralFiniteComplex l E W n).obj P.obj := by rfl
  exact (scalarReductionDerivedExtension l E W n).mapIso e.symm ≪≫ r ≪≫
    DerivedCategory.Q.mapIso (eqToIso heq)

open AlgebraicGeometry.Scheme in
private theorem reductionConstructible_iso (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    {K L : DerivedCategory (integralOperationsFiniteModules l E W n)} (e : K ≅ L)
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W K) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W L := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let C : ObjectProperty (proEtaleDerivedCategory W A) :=
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W
  have : C.IsClosedUnderIsomorphisms := (proEtale_bounded_constructible_isTriangulated W A).1
  exact C.prop_of_iso e hK

open AlgebraicGeometry.Scheme in
private theorem support_iso (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    {K L : DerivedCategory (integralOperationsFiniteModules l E W n)} (e : K ≅ L)
    (a b : ℤ) (hK : proEtaleCohomologicalSupport K ⊆ Set.Icc a b) :
    proEtaleCohomologicalSupport L ⊆ Set.Icc a b := by
  intro i hi
  apply hK
  intro hz
  exact hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e.symm))

open AlgebraicGeometry.Scheme in
private theorem tor_iso (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    {K L : DerivedCategory (integralOperationsFiniteModules l E W n)} (e : K ≅ L)
    (a b : ℤ) (hK : HasProEtaleTorAmplitude W
      (Padic.coefficientExtensionRing l E (n + 1)) K a b) :
    HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1)) L a b := by
  refine ⟨hK.1, ?_⟩
  rintro S P ⟨e'⟩ f hf hP M i hi
  exact hK.2 S P ⟨e' ≪≫ e.symm⟩ f hf hP M i hi

open AlgebraicGeometry.Scheme in
private theorem finiteReduction_constructible (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules l E W))
    (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ)
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W
      ((scalarReductionDerivedExtension l E W n).obj K)) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W
      (DerivedCategory.Q.obj ((unrestrictedIntegralFiniteComplex l E W n).obj P.obj)) := by
  exact reductionConstructible_iso l E W n (finiteReductionIso l E W K P e n) hK

open AlgebraicGeometry.Scheme in
private theorem finiteLocal_iso (W : AlgebraicGeometry.Scheme.{u}) (A : Type u)
    [CommRing A] {F G : proEtaleRingModules W (proEtaleConstantRing W A)} (e : F ≅ G)
    (hF : IsLocallyConstantProEtaleModuleSheaf W A F ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : AlgebraicGeometry.Scheme.Spec.obj
        (op (CommRingCat.of Ω)) ⟶ W),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing W A) F)) :
    IsLocallyConstantProEtaleModuleSheaf W A G ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : AlgebraicGeometry.Scheme.Spec.obj
        (op (CommRingCat.of Ω)) ⟶ W),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing W A) G) := by
  constructor
  · obtain ⟨I, U, f, hf, h⟩ := hF.1
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨eM⟩⟩ := h i
    exact ⟨M, ⟨((SheafOfModules.overFunctor _ (U i)).mapIso e).symm ≪≫ eM⟩⟩
  · intro Ω _ _ y
    let O := proEtaleConstantRing W A
    let E := (SheafOfModules.forget _).mapIso e
    let D := (PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
      (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso E
    let t := (PresheafOfModules.colimitFunctor
      (colimit.isColimit (proEtaleGeometricStalkRingDiagram y O))).mapIso D
    exact @Finite.of_equiv _ _ (hF.2 Ω y) t.toLinearEquiv.toEquiv

open AlgebraicGeometry.Scheme in
private theorem constructible_pullback {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (hF : IsConstructibleProEtaleModuleSheaf Y A F) :
    IsConstructibleProEtaleModuleSheaf X A (proEtaleConstantModulePullback f A F) := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S.pullback f, hn, fun i ↦ ?_⟩
  let p := pullback.fst (S.immersion i) f
  let q := pullback.snd (S.immersion i) f
  obtain ⟨e₁⟩ := proEtaleConstantModulePullback_comp f q A
  obtain ⟨e₂⟩ := proEtaleConstantModulePullback_comp (S.immersion i) p A
  have heq : q ≫ f = p ≫ S.immersion i := pullback.condition.symm
  let e := (e₂.app F).symm ≪≫
    eqToIso (congrArg (fun g ↦ proEtaleConstantModulePullback g A F) heq.symm) ≪≫
    e₁.app F
  exact finiteLocal_iso _ A e
    (proEtale_finiteLocalConstancy_pullback p A _ (hS i))

open AlgebraicGeometry.Scheme in
private theorem constructible_iso (W : AlgebraicGeometry.Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] {F G : proEtaleRingModules W (proEtaleConstantRing W A)}
    (e : F ≅ G) (hF : IsConstructibleProEtaleModuleSheaf W A F) :
    IsConstructibleProEtaleModuleSheaf W A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  exact finiteLocal_iso _ A
    ((proEtaleConstantModulePullbackFunctor (S.immersion i) A).mapIso e) (hS i)

open AlgebraicGeometry.Scheme in
private theorem finiteTensor_bounds (W : AlgebraicGeometry.Scheme.{u})
    [∀ x : W, Invertible (l : W.residueField x)] (n : ℕ)
    (P Q : CochainComplex (integralOperationsFiniteModules l E W n) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := integralCoefficientCommRingSheaf.{u, u} l E W n) P)
    (a b c d : ℤ)
    (hPc : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W
      (DerivedCategory.Q.obj P))
    (hQc : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W
      (DerivedCategory.Q.obj Q))
    (hPt : HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1))
      (DerivedCategory.Q.obj P) a b)
    (hQb : proEtaleCohomologicalSupport (DerivedCategory.Q.obj Q) ⊆ Set.Icc c d) :
    let V := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P Q
      (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)))
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W V ∧
      proEtaleCohomologicalSupport V ⊆ Set.Icc (a + c) (b + d) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := integralCoefficientCommRingSheaf.{u, u} l E W n
  let C := integralOperationsFiniteModules l E W n
  let : MonoidalCategory C := SheafOfModules.monoidalCategory R
  let : SymmetricCategory C := SheafOfModules.symmetricCategory R
  let : MonoidalClosed C := SheafOfModules.monoidalClosed_kfg (R := R)
  have : MonoidalPreadditive C := SheafOfModules.monoidalPreadditive_kfg R
  have : IsGrothendieckAbelian.{u + 1} C := SheafOfModules.isGrothendieckAbelian_kfg R
  have : Abelian.HasFunctorialFlatResolution C :=
    SheafOfModules.hasFunctorialFlatResolution_kfg R
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let := HasDerivedCategory.standard C
  have := DerivedCategory.hasDerivedMonoidalCategory C
  let : MonoidalCategory (DerivedCategory C) := inferInstance
  have hqid : QuasiIso (𝟙 P) := quasiIso_of_isIso (𝟙 P)
  have hk : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hr : HomotopyCategory.subcategoryAcyclic C
        (MonoidalCategory.tensorObj ((HomotopyCategory.quotient C (.up ℤ)).obj N)
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)) :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩
  have ht : DerivedCategory.torAmplitudeIn C a b (DerivedCategory.Q.obj P) := by
    intro M
    let e := MonoidalCategory.tensorIso (Iso.refl (DerivedCategory.Q.obj P))
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app M) ≪≫
        DerivedCategory.QObjTensorQObjIsoOfKFlatLeft (C := C) P _ hk
    rw [DerivedCategory.homologyConcentratedIn_iff]
    constructor
    · apply (DerivedCategory.isGE_iff _ a).2
      intro i hi
      exact (hPt.2 P P ⟨Iso.refl _⟩ (𝟙 P) hqid hP M i (.inl hi)).of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso e)
    · apply (DerivedCategory.isLE_iff _ b).2
      intro i hi
      exact (hPt.2 P P ⟨Iso.refl _⟩ (𝟙 P) hqid hP M i (.inr hi)).of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso e)
  have hq : DerivedCategory.homologyConcentratedIn c d (DerivedCategory.Q.obj Q) := by
    rw [DerivedCategory.homologyConcentratedIn_iff]
    constructor
    · apply (DerivedCategory.isGE_iff _ c).2
      intro i hi
      by_contra hz
      have := (hQb hz).1
      omega
    · apply (DerivedCategory.isLE_iff _ d).2
      intro i hi
      by_contra hz
      have := (hQb hz).2
      omega
  have hb := DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left ht hq
  let e := DerivedCategory.QObjTensorQObjIsoOfKFlatLeft (C := C) P Q hk
  let V : CochainComplex C ℤ := MonoidalCategory.tensorObj P Q
  have hbound : proEtaleCohomologicalSupport (DerivedCategory.Q.obj V) ⊆
      Set.Icc (a + c) (b + d) := by
    intro i hi
    by_contra hout
    obtain ⟨hge, hle⟩ := (DerivedCategory.homologyConcentratedIn_iff _ _ _).1 hb
    apply hi
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor C i).mapIso e.symm)
    rcases not_and_or.mp hout with ha | hb
    · exact (DerivedCategory.isGE_iff _ (a + c)).1 hge i (lt_of_not_ge ha)
    · exact (DerivedCategory.isLE_iff _ (b + d)).1 hle i (lt_of_not_ge hb)
  exact ⟨⟨(Set.finite_Icc _ _).subset hbound,
    finiteTensor_constructible_cohomology l E (n + 1) (Nat.succ_pos n) W
      P Q P (𝟙 P) hqid hP hPc hQc⟩, hbound⟩

open AlgebraicGeometry.Scheme in
private theorem finitePullback_bounds {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) (P : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (a b : ℤ)
    (hP : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y
      (DerivedCategory.Q.obj P))
    (hb : proEtaleCohomologicalSupport (DerivedCategory.Q.obj P) ⊆ Set.Icc a b) :
    let V := DerivedCategory.Q.obj
      (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj P)
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X V ∧
      proEtaleCohomologicalSupport V ⊆ Set.Icc a b := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let G := proEtaleConstantModulePullbackFunctor f A
  let V := ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj P
  let e := (NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
    (.up ℤ)).app P
  let h (i : ℤ) :
      (DerivedCategory.homologyFunctor (integralOperationsFiniteModules l E X n) i).obj
          (DerivedCategory.Q.obj V) ≅
        G.obj ((DerivedCategory.homologyFunctor
          (integralOperationsFiniteModules l E Y n) i).obj (DerivedCategory.Q.obj P)) :=
    (DerivedCategory.homologyFunctor _ i).mapIso (DerivedCategory.Q.mapIso e) ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
      proEtaleConstantModulePullbackHomologyIso f A P i
  have hbound : proEtaleCohomologicalSupport (DerivedCategory.Q.obj V) ⊆ Set.Icc a b := by
    intro i hi
    by_contra hout
    apply hi
    have hz : IsZero ((DerivedCategory.homologyFunctor
        (integralOperationsFiniteModules l E Y n) i).obj (DerivedCategory.Q.obj P)) := by
      by_contra hn
      exact hout (hb hn)
    exact (G.map_isZero hz).of_iso (h i)
  refine ⟨⟨(Set.finite_Icc a b).subset hbound, fun i ↦ ?_⟩, hbound⟩
  exact constructible_iso X A (h i).symm (constructible_pullback f A _ (hP.2 i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_effectivity {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (integralTowerModules l E Y))
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) :
    IsSfDerivedComplete l E X ((integralDerivedPullback l E f).obj K) ∧
      ∀ n, IsIso (integralPullbackFiniteComparison l E f K P e n) := by
  let r := (integralDerivedPullback l E f).mapIso e.symm ≪≫
    (integralDerivedPullbackComparison l E f).app P
  have h := (integralOperationRoos_effectivity l E).1 f P _ r
  refine ⟨h.1, fun n ↦ ?_⟩
  have hn := h.2 n
  dsimp only [r, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] at hn
  simpa only [integralPullbackFiniteComparison, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Category.assoc] using hn

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_effectivity (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ M) (d : DerivedCategory.Q.obj Q.obj ≅ N) :
    IsSfDerivedComplete l E W ((integralCompletedTensor l E W).obj (M, N)) ∧
      ∀ n, IsIso (integralTensorFiniteComparison l E W M N P Q e d n) := by
  let r := (integralCompletedTensor l E W).mapIso (Iso.prod e.symm d.symm) ≪≫
    (integralCompletedTensorComparison l E W).app (P, Q)
  have h := (integralOperationRoos_effectivity l E).2 W P Q _ r
  refine ⟨h.1, fun n ↦ ?_⟩
  have hn := h.2 n
  dsimp only [r, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] at hn
  simpa only [integralTensorFiniteComparison, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Iso.prod_hom, Prod.mkHom, Category.assoc] using hn

private def auxiliaryDatum (q : ℕ) (hq : q.Prime) : FiniteFieldDatum.{u} := by
  letI : Fact q.Prime := ⟨hq⟩
  exact {
    p := q
    a := 1
    q := q
    prime := hq
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one q).symm
    k₀ := ULift.{u} (ZMod q)
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ULift.{u} (ZMod q)) }

private theorem tensor_constructible (W : AlgebraicGeometry.Scheme.{u})
    [∀ x : W, Invertible (l : W.residueField x)]
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : sfIntegralConstructible l E W M) (hN : sfIntegralConstructible l E W N) :
    sfIntegralConstructible l E W ((integralCompletedTensor l E W).obj (M, N)) ∧
      ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ M) (d : DerivedCategory.Q.obj Q.obj ≅ N)
        (n : ℕ), IsIso (integralTensorFiniteComparison l E W M N P Q e d n) := by
  obtain ⟨P, ⟨e⟩⟩ := goodRepresentative l E W M
  obtain ⟨Q, ⟨d⟩⟩ := goodRepresentative l E W N
  have heff := tensor_effectivity l E W M N P Q e d
  refine ⟨⟨heff.1, ?_⟩, fun P Q e d n ↦ (tensor_effectivity l E W M N P Q e d).2 n⟩
  obtain ⟨a, b, hab, hMb⟩ := hM.2
  obtain ⟨c, d', hcd, hNb⟩ := hN.2
  refine ⟨a + c, b + d', add_le_add hab hcd, fun n ↦ ?_⟩
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (l + 1)
  have hlq : l ≠ q := by omega
  have ht := (integral_residue_tor.{u, u} (auxiliaryDatum.{u} q hqp) l hlq E W).1 M hM a b hab
    (fun i hi ↦ (hMb 0).2 hi) n
  let er := finiteReductionIso l E W M P e n
  let dr := finiteReductionIso l E W N Q d n
  have hf := finiteTensor_bounds l E W n _ _ (finiteReduction_kflat l E W P n)
    a b c d' (finiteReduction_constructible l E W M P e n (hMb n).1)
    (finiteReduction_constructible l E W N Q d n (hNb n).1)
    (tor_iso l E W n er a b ht) (support_iso l E W n dr c d' (hNb n).2)
  have := heff.2 n
  let ec := asIso (integralTensorFiniteComparison l E W M N P Q e d n)
  exact ⟨reductionConstructible_iso l E W n ec.symm hf.1,
    support_iso l E W n ec.symm (a + c) (b + d') hf.2⟩

/-- Integral pullback and completed tensor preserve the bounded constructible
 derived-complete category, and their canonical finite-reduction maps are isomorphisms.

Source: Bhatt--Scholze, Lemmas 6.5.3--6.5.5 and 6.5.9(5); Stacks Tags 099M, 099N,
09BQ and 054I (blueprint: lem-pur-integral-operations-preserve-constructible).

Proof:
1. Choose good representatives by the independent-coefficient K-flat resolution theorem,
transporting categorical flatness to site flatness with siteSheafTensorRightIso.
2. The separate integralOperationRoos_effectivity theorem gives completeness and the
canonical reduction comparisons on arbitrary good representatives. Its unbounded
normalization calculation is independent of the constructibility argument below.
3. At each finite level, use integralFinitePullbackModel to identify finite pullback
with the exact constant-module inverse image. Pull back the finite stratification.
The constant-module composition comparison and finite-local-constancy pullback theorem
show constructibility on the pulled-back strata. Exactness identifies cohomology and
preserves vanishing outside the original common interval.
4. For tensor use integral_residue_tor on the first input's residue interval.
Compare each actual reduced good complex with the concrete change-of-rings complex
to establish K-flatness. Its identity is therefore an allowed K-flat resolution.
5. Convert the first finite reduction's Tor condition to categorical Tor amplitude.
The proved source-library homologyConcentratedIn_tensor_of_torAmplitudeIn_left adds
this interval to the second reduction's cohomology interval. The K-flat comparison
identifies categorical tensor with the specified total tensor of the actual reductions.
6. finiteTensor_constructible_cohomology supplies all constructible cohomology sheaves.
The uniform support interval makes their support finite. Transport these conclusions
through the canonical reduction isomorphisms; together with completeness they give
exactly sfIntegralConstructible for each operation. Both comparison assertions hold
for all representatives because step 2 did not require chosen ones. -/
theorem integralOperations_preserve_constructible
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (∀ K : DerivedCategory (integralTowerModules l E Y),
      sfIntegralConstructible l E Y K →
      sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K) ∧
        ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
          (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ),
          IsIso (integralPullbackFiniteComparison l E f K P e n)) ∧
    (∀ (W : AlgebraicGeometry.Scheme.{u}), W = X ∨ W = Y →
      ∀ M N : DerivedCategory (integralTowerModules l E W),
      sfIntegralConstructible l E W M → sfIntegralConstructible l E W N →
      sfIntegralConstructible l E W ((integralCompletedTensor l E W).obj (M, N)) ∧
        ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
          (e : DerivedCategory.Q.obj P.obj ≅ M) (d : DerivedCategory.Q.obj Q.obj ≅ N)
          (n : ℕ), IsIso (integralTensorFiniteComparison l E W M N P Q e d n)) := by
  constructor
  · intro K hK
    obtain ⟨P, ⟨e⟩⟩ := goodRepresentative l E Y K
    have heff := pullback_effectivity l E f K P e
    refine ⟨⟨heff.1, ?_⟩, fun P e n ↦ (pullback_effectivity l E f K P e).2 n⟩
    obtain ⟨a, b, hab, hb⟩ := hK.2
    refine ⟨a, b, hab, fun n ↦ ?_⟩
    have hf := finitePullback_bounds l E f n _ a b
      (finiteReduction_constructible l E Y K P e n (hb n).1)
      (support_iso l E Y n (finiteReductionIso l E Y K P e n) a b (hb n).2)
    have := heff.2 n
    let ec := asIso (integralPullbackFiniteComparison l E f K P e n)
    exact ⟨reductionConstructible_iso l E X n ec.symm hf.1,
      support_iso l E X n ec.symm a b hf.2⟩
  · intro W hW M N hM hN
    rcases hW with rfl | rfl <;> exact tensor_constructible l E _ M N hM hN

end WeilConjectures
