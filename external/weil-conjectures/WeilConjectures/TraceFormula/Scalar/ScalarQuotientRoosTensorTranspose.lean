/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.TraceFormula.Scalar.ScalarRoosDerivedNaturality
import all WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.TraceFormula.Supporting.RoosAdjunctionTranspose

/-! # Tensor transposition on a coherent quotient presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit completedScalarChangeData

attribute [local implicit_reducible] completedOrdinaryScalarComplex integralOperationsRoos
  integralOperationsRoosFunctor completedScalarRoosEndomorphism integralScalarComplexFunctor

private def quotientScalarTowerMap
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l L X) ℤ) :
    (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
      C).asFunctor ⋙ completedOrdinaryScalarComplex l L F j X ⟶
    (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
      (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
        (.up ℤ)).obj C)).asFunctor where
  app n := ScalarRoosLiftProof.levelChange l L F j X C n.unop
  naturality _ _ f := ScalarRoosLiftProof.levelChange_horizontal l L F j X C f

private def towerScalarNat
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u}) :
    restrictedTower l L X ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (completedOrdinaryScalarComplex l L F j X) ⟶
    (integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex (.up ℤ) ⋙
      restrictedTower l F X where
  app C := quotientScalarTowerMap l L F j X C
  naturality C D f := by
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.hom_ext
    intro i
    exact (ScalarRoosLiftProof.scalarComponentNat l L F j X n.unop).naturality (f.f i)

-- Compute Roos coordinates before specializing to the sheaf categories.
private theorem quotientRoosMap_fst
    {A B : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [Category B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] {C : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    {D E : ℕᵒᵖ ⥤ CochainComplex B ℤ}
    (a : C ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ D) (q : D ⟶ E)
    {P : CochainComplex A ℤ} (f : P ⟶ integralOperationsRoos C) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map f ≫ scalarRoosMap F C ≫
        integralOperationsRoosMap a ≫ integralOperationsRoosMap q ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary E) ≫
        Pi.π (fun m ↦ E.obj (op m)) n =
      (F.mapHomologicalComplex (.up ℤ)).map
        (f ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
          Pi.π (fun m ↦ C.obj (op m)) n) ≫ a.app (op n) ≫ q.app (op n) := by
  rw [reassoc_of% (scalarRoosTowerCoordinates q).1]
  simp only [Limits.Pi.map_π]
  rw [reassoc_of% (scalarRoosTowerCoordinates a).1]
  rw [Limits.Pi.map_π_assoc]
  rw [reassoc_of% (scalarRoosCoordinates F C).1]
  simp only [Category.assoc, piComparison_comp_π_assoc, Functor.map_comp]

private theorem quotientRoosMap_snd_zero
    {A B : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [Category B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] {C : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    {D E : ℕᵒᵖ ⥤ CochainComplex B ℤ}
    (a : C ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ D) (q : D ⟶ E)
    {P : CochainComplex A ℤ} (f : P ⟶ integralOperationsRoos C) (i : ℤ)
    (hf : f.f i ≫ (CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v
      i (i - 1) (by omega) = 0) :
    ((F.mapHomologicalComplex (.up ℤ)).map f ≫ scalarRoosMap F C ≫
        integralOperationsRoosMap a ≫ integralOperationsRoosMap q).f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary E)).v
          i (i - 1) (by omega) = 0 := by
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [(scalarRoosTowerCoordinates q).2 i (i - 1) (by omega),
    reassoc_of% (scalarRoosTowerCoordinates a).2 i (i - 1) (by omega),
    reassoc_of% (scalarRoosCoordinates F C).2 i]
  rw [Functor.mapHomologicalComplex_map_f, ← Functor.map_comp_assoc, hf,
    Functor.map_zero, zero_comp]

-- Tensor section types involve several equivalent presentations of the scalar functor.
private theorem quotientScalarChainComparison
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})
    (P : (integralOperationsGoodComplex l L X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l L X n).obj P.obj)
    (c : ((Functor.const ℕᵒᵖ : scalarReductionSource l L X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l L X).mapHomologicalComplex (.up ℤ)).obj P.obj ⟶
      ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C)
    (hc : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U),
      (((c.f i).app (op n)).val.app U) x =
        integralComparisonRestrictedSection l L X (C.X i) n U
          (integralComparisonSequenceSection l L X (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l L X n (P.obj.X i) U 1 x))))
    (q : (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l L F j X).obj P.obj)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (coefficientSequenceCommRingSheaf l F X).obj.obj (op (n, U.unop)))
      (x : (P.obj.X i).val.obj U),
      ((q.hom.app (op n)).f i).val.app U
        (integralComparisonRestrictedSection l F X
          ((integralComparisonSequenceScalarModel l L F j X).E.obj (C.X i)) n U
          (integralComparisonSequenceTensorSection l L F j X (C.X i)
            (op (n, U.unop)) s
            (integralComparisonSequenceSection l L X (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l L X n (P.obj.X i) U 1 x))))) =
        integralScalarTensorSection l L F j X n (P.obj.X i) U s x)
 :
    (completedOrdinaryScalarComplex l L F j X).map
      (((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l L X)).mapHomologicalComplex
        (.up ℤ)).homEquiv P.obj _ c ≫ integralComparisonLimitToRoos l L X _) ≫
      scalarRoosMap (completedOrdinaryScalarExtension l L F j X)
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
          C).asFunctor ≫
      integralOperationsRoosMap (quotientScalarTowerMap l L F j X C) ≫
      integralOperationsRoosFunctor.map q.hom =
    (completedScalarChainComparison l L F j X).app P.obj := by
  let CL := ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C
  let G := completedOrdinaryScalarComplex l L F j X
  let u := ((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l L X)).mapHomologicalComplex
    (.up ℤ)).homEquiv P.obj CL c
  let a := quotientScalarTowerMap l L F j X C
  have hu (n : ℕ) (i : ℤ) : u.f i ≫ limit.π (CL.X i) (op n) = (c.f i).app (op n) := by
    have h := (((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l L X)).mapHomologicalComplex
       (.up ℤ)).homEquiv P.obj CL).symm_apply_apply c
    rw [Adjunction.homEquiv_counit] at h
    exact congrArg (fun f ↦ (f.f i).app (op n)) h
  have hι := (integralComparisonLimitToRoos_existsUnique l L X CL).exists.choose_spec
  change (∀ n, integralComparisonLimitToRoos l L X CL ≫ _ ≫ _ = _) ∧ _ at hι
  have hb := (completedScalarChainComparison_existsUnique l L F j X).exists.choose_spec
  change (∀ P i n U s x, (((completedScalarChainComparison l L F j X).app P).f i ≫
    _ ≫ _).val.app U (completedScalarTensorSection l L F j X (P.X i) U s x) = _) ∧ _ at hb
  let δ := completedScalarRoosEndomorphism l L F j X P.obj
  change G.map (u ≫ integralComparisonLimitToRoos l L X CL) ≫
    scalarRoosMap (completedOrdinaryScalarExtension l L F j X) CL.asFunctor ≫
      integralOperationsRoosMap a ≫ integralOperationsRoosFunctor.map q.hom =
        (completedScalarChainComparison l L F j X).app P.obj
  apply cone_ext δ
  · apply Pi.hom_ext
    intro n
    simp only [Category.assoc]
    erw [quotientRoosMap_fst]
    have hi := hι.1 n
    have hfirst : G.map ((u ≫ integralComparisonLimitToRoos l L X CL) ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary CL.asFunctor) ≫
        Pi.π (fun n : ℕ ↦ CL.asFunctor.obj (op n)) n) =
        G.map (u ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app CL) := by
      rw [Category.assoc, hi]
    erw [hfirst]
    apply HomologicalComplex.Hom.ext
    funext i
    apply completedScalar_tensor_ext l L F j X
    intro U s x
    change ((q.hom.app (op n)).f i).val.app U
      (((a.app (op n)).f i).val.app U
        (((completedOrdinaryScalarExtension l L F j X).map
          ((u ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app CL).f i)).val.app
            U (completedScalarTensorSection l L F j X (P.obj.X i) U s x))) = _
    rw [completedScalarTensorSection_naturality]
    change ((q.hom.app (op n)).f i).val.app U
      (((ScalarRoosLiftProof.scalarComponentNat l L F j X n).app (C.X i)).val.app U
        (completedScalarTensorSection l L F j X
          (((coefficientSequenceRestriction l L X).obj (C.X i)).obj (op n)) U s
          ((u.f i ≫ limit.π (CL.X i) (op n)).val.app U x))) = _
    have hc' := congrArg (fun f ↦ f.val.app U x) (hu n i)
    change (u.f i ≫ limit.π (CL.X i) (op n)).val.app U x = _ at hc'
    rw [hc']
    erw [hc n i U x, ScalarRoosLiftProof.scalarComponent_tensor]
    exact (hq n i U _ x).trans (hb.1 P.obj i n U s x).symm
  · intro i
    have hz : (u ≫ integralComparisonLimitToRoos l L X CL).f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary CL.asFunctor)).v
          i (i - 1) (by omega) = 0 := by
      have hi2 : (integralComparisonLimitToRoos l L X CL).f i ≫
          (CochainComplex.mappingCocone.snd (scalarRoosBoundary CL.asFunctor)).v
            i (i - 1) (by omega) = 0 := hι.2 i (i - 1) (by omega)
      simp only [HomologicalComplex.comp_f, Category.assoc, hi2, comp_zero]
    exact (quotientRoosMap_snd_zero (completedOrdinaryScalarExtension l L F j X)
      a q.hom (u ≫ integralComparisonLimitToRoos l L X CL) i hz).trans (hb.2 P.obj i).symm

/-- Transposing a quotient tensor family commutes with scalar change, independently
of any chosen derived reduction calculus or completed scalar realization.

Source: Stacks Project, Tags 06YY and 0941; Bhatt--Scholze, Proposition 3.5.1;
step 3 of the whole-system scalar counit calculation.
(blueprint: lem-trf-scalar-quotient-roos-tensor-transpose)

Proof in words: the residue formula ha determines a as the canonical natural
scalar map of the restricted tower, by tensor generator extensionality. Transpose
c through the ordinary constant/limit adjunction. Its limit projections are the
specified quotient tensor units and its shifted Roos coordinate is zero. Apply
ordinary scalar extension. On every unshifted projection, tensor naturality and
the generator formula hq identify the result with the finite-free scalar chain
comparison. The shifted projection is zero on both sides, since the scalar Roos
map and the Roos map of the canonical tower map preserve that coordinate. Product
extensionality and the two mapping-cocone coordinates prove the chain equality.
Cancel the Roos map of q, use naturality of the universal scalar cochain counit,
and apply scalarRoosDerivedNaturality to h. The latter uses a K-flat resolution
of the middle complex in a right fraction; it does not assume that ordinary
system scalar extension is exact. The zero complex and the identity coefficient
inclusion give the same calculation, with zero shifted coordinate.
-/
theorem scalarQuotientRoosTensorTranspose
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (P : (integralOperationsGoodComplex l L X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l L X n).obj P.obj)
    (c : ((Functor.const ℕᵒᵖ : scalarReductionSource l L X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l L X).mapHomologicalComplex (.up ℤ)).obj P.obj ⟶
      ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C)
    (hc : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U),
      (((c.f i).app (op n)).val.app U) x =
        integralComparisonRestrictedSection l L X (C.X i) n U
          (integralComparisonSequenceSection l L X (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l L X n (P.obj.X i) U 1 x))))
    (q : (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l L F j X).obj P.obj)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (coefficientSequenceCommRingSheaf l F X).obj.obj (op (n, U.unop)))
      (x : (P.obj.X i).val.obj U),
      ((q.hom.app (op n)).f i).val.app U
        (integralComparisonRestrictedSection l F X
          ((integralComparisonSequenceScalarModel l L F j X).E.obj (C.X i)) n U
          (integralComparisonSequenceTensorSection l L F j X (C.X i)
            (op (n, U.unop)) s
            (integralComparisonSequenceSection l L X (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l L X n (P.obj.X i) U 1 x))))) =
        integralScalarTensorSection l L F j X n (P.obj.X i) U s x)
    [IsIso ((coefficientSequenceLimit l F X).map
      ((integralComparisonSequenceScalarModel l L F j X).ε.app C))]
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (h : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj D)
    (a :
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        D).asFunctor ⋙ completedOrdinaryScalarComplex l L F j X ⟶
      (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor)
    (ha : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (x : (D.X i).val.obj (op (n, U.unop))),
      ((a.app (op n)).f i).val.app U
        (completedScalarTensorSection l L F j X
          (((coefficientSequenceRestriction l L X).obj (D.X i)).obj (op n)) U s
          (integralComparisonRestrictedSection l L X (D.X i) n U x)) =
        integralComparisonRestrictedSection l F X
          ((integralComparisonSequenceScalarModel l L F j X).E.obj (D.X i)) n U
          (integralComparisonSequenceTensorSection l L F j X (D.X i)
            (op (n, U.unop))
            ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s) x)) :
    completedScalarCounit l L F j X P.obj ≫
      DerivedCategory.Q.map ((completedScalarChainComparison l L F j X).app P.obj) ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.inv) ≫
      (integralComparisonRoosBridge l F X ρF _).inv ≫
      inv ((coefficientSequenceLimit l F X).map
        ((integralComparisonSequenceScalarModel l L F j X).ε.app C)) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l L F j X).map h) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
      (integralComparisonRoosBridge l F X ρF _).hom =
    (completedDerivedScalarExtension l L F j X).map
      (DerivedCategory.Q.map
          (((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l L X)).mapHomologicalComplex
            (.up ℤ)).homEquiv P.obj _ c ≫ integralComparisonLimitToRoos l L X _) ≫
        (integralComparisonRoosBridge l L X ρL C).inv ≫
        (coefficientSequenceLimit l L X).map h ≫
        (integralComparisonRoosBridge l L X ρL D).hom) ≫
      completedScalarCounit l L F j X
        (integralOperationsRoos
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            D).asFunctor) ≫
      DerivedCategory.Q.map
        (scalarRoosMap (completedOrdinaryScalarExtension l L F j X)
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            D).asFunctor ≫ integralOperationsRoosMap a) := by
  have ha' : a = quotientScalarTowerMap l L F j X D := by
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.hom_ext
    intro i
    apply completedScalar_tensor_ext l L F j X
    intro U s x
    let y := cast (integralComparisonRestrictedSectionType l L X (D.X i) n.unop U) x
    have hx : integralComparisonRestrictedSection l L X (D.X i) n.unop U y = x := by
      simp only [integralComparisonRestrictedSection, y, cast_cast, cast_eq]
    rw [← hx]
    exact (ha n.unop i U s y).trans
      (ScalarRoosLiftProof.scalarComponent_tensor l L F j X (D.X i) n.unop U s y).symm
  subst a
  let CL := ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C
  let G := completedOrdinaryScalarComplex l L F j X
  let B := completedDerivedScalarExtension l L F j X
  let f := ((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l L X)).mapHomologicalComplex
    (.up ℤ)).homEquiv P.obj CL c ≫ integralComparisonLimitToRoos l L X CL
  have hchain : (completedScalarChainComparison l L F j X).app P.obj ≫
      integralOperationsRoosFunctor.map q.inv =
      G.map f ≫ scalarRoosMap (completedOrdinaryScalarExtension l L F j X) CL.asFunctor ≫
        integralOperationsRoosMap (quotientScalarTowerMap l L F j X C) := by
    apply (cancel_mono (integralOperationsRoosFunctor.map q.hom)).1
    simp only [Category.assoc, ← integralOperationsRoosFunctor.map_comp, q.inv_hom_id,
      integralOperationsRoosFunctor.map_id]
    exact (quotientScalarChainComparison l L F j X P C κ c hc q hq).symm
  have hQ := congrArg DerivedCategory.Q.map hchain
  simp only [Functor.map_comp] at hQ
  rw [reassoc_of% hQ]
  have hε : B.map (DerivedCategory.Q.map f) ≫
      completedScalarCounit l L F j X (integralOperationsRoos CL.asFunctor) =
      completedScalarCounit l L F j X P.obj ≫ DerivedCategory.Q.map (G.map f) :=
    (completedCounitNat l L F j X).naturality f
  rw [← reassoc_of% hε]
  have hn := scalarRoosDerivedNaturality l L F j X ρL ρF
    (towerScalarNat l L F j X) C D h
  simpa only [towerScalarNat, f, CL, B, Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ B.map (DerivedCategory.Q.map f) ≫ k) hn

end WeilConjectures
