/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import WeilConjectures.TraceFormula.Scalar.ScalarQuotientRoosTensorTranspose
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import WeilConjectures.TraceFormula.Supporting.RoosAdjunctionTranspose
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Normalized scalar change and the whole-system Roos counit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction
  integralScalarExtensionOfUniverses completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit

attribute [local implicit_reducible] coefficientSequenceLimit
  integralComparisonDerivedSequenceScalar integralOperationsRoosFunctor
  integralOperationsRoos HomologicalComplex.complexOfFunctorsToFunctorToComplex
  integralTowerHasDerivedCategory scalarReductionSourceDerived
  integralComparisonConstantTower integralComparisonTowerCounit
  integralComparisonConstantAdjunction integralScalarComplexFunctor
  completedScalarRoosEndomorphism

private theorem scalarCounit_normalization_of_fac
    {𝒞 : Type*} [Category 𝒞] {A B C D E F G H : 𝒞}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ≅ D) (d : D ⟶ E) [IsIso d]
    (e : E ≅ F) (f : F ≅ G) (t : B ⟶ G) (k : A ⟶ H) (n : H ⟶ G)
    (hb : b ≫ c.hom ≫ d ≫ e.hom ≫ f.hom = t) (ha : a ≫ t = k ≫ n) :
    a ≫ b = k ≫ n ≫ f.inv ≫ e.inv ≫ inv d ≫ c.inv := by
  apply (cancel_mono (c.hom ≫ d ≫ e.hom ≫ f.hom)).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id, hb] using ha

/-- The normalized scalar realization commutes with the whole-system counit in
Roos coordinates. This is an equation on the target system alone, before inserting
any map from a good complex or identifying any strict zero-shift lift.

Source: Stacks 06YY, 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-counit-normalization)

Proof in words: resolve the restricted target diagram simultaneously by a
K-injective diagram. The normalized Roos bridge identifies its derived-limit
counit with the ordinary compatible limit tuple followed by the resolution
inverse. Present a flat-term K-flat source by its coherent quotient system and
apply the scalar realization normalization to that presentation. Transpose its
quotient tensor unit through the ordinary scalar adjunction. The residue square
identifies this transpose with the coordinates of a. The universal cochain
counit and the coefficient-action counit identify the resulting composite with
scalarRoosMap followed by the Roos map of a; both cocone coordinates are used.
Naturality and uniqueness of the derived comparison descend the equation from
these good representatives to the arbitrary derived limit of D. The specified
tensor coordinates determine a by the tensor and sheafification universal
properties. No zero-shift hypothesis on a map into the Roos complex is used.
-/
theorem scalarModelRoos_counit_normalization
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
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
    (completedDerivedScalarExtension l L F j X).map
        (integralComparisonRoosBridge l L X ρL D).inv ≫
      (completedScalarComparison l L F j X).app
        ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
      b.realization.hom.app
        ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l L F j X).map
          (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
      (integralComparisonRoosBridge l F X ρF _).hom =
    completedScalarCounit l L F j X
      (integralOperationsRoos
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
          D).asFunctor) ≫
      DerivedCategory.Q.map
        (scalarRoosMap (completedOrdinaryScalarExtension l L F j X)
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            D).asFunctor ≫ integralOperationsRoosMap a) := by
  classical
  let H := coefficientSequenceLimit l L X
  let HF := coefficientSequenceLimit l F X
  let T := integralComparisonDerivedSequenceScalar l L F j X
  let m := integralComparisonSequenceScalarModel l L F j X
  let B := completedDerivedScalarExtension l L F j X
  let χ := completedScalarComparison l L F j X
  let := integralOperationsGoodLocalization_isLocalization l L X
  let := Localization.essSurj (integralOperationsGoodLocalization l L X)
    ((HomologicalComplex.quasiIso (integralTowerModules l L X) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l L X).ι)
  let P := (integralOperationsGoodLocalization l L X).objPreimage
    (H.obj (DerivedCategory.Q.obj D))
  let z : DerivedCategory.Q.obj P.obj ≅ H.obj (DerivedCategory.Q.obj D) :=
    (integralOperationsGoodLocalization l L X).objObjPreimageIso _
  obtain ⟨C, e, κ, hp, hc⟩ := coherentPrimitiveReductionPresentation l L SL P
  obtain ⟨q, hq, hn⟩ := b.normalization P C e κ hp hc
  rw [IsIntegralComparisonPresentationCoherent] at hc
  obtain ⟨c, hct, hc⟩ := hc
  let RC := ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C
  let f := ((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l L X)).mapHomologicalComplex
    (.up ℤ)).homEquiv P.obj RC c ≫ integralComparisonLimitToRoos l L X RC
  let h : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj D :=
    e.inv ≫ SL.reduction.map z.hom ≫ SL.adjunction.counit.app (DerivedCategory.Q.obj D)
  have hε : IsIso (HF.map (m.ε.app C)) := by
    have htail : IsIso (HF.map (T.map e.hom) ≫ HF.map (m.ε.app C) ≫
        (integralComparisonRoosBridge l F X ρF _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)) :=
      IsIso.of_isIso_fac_left hn
    have htail' : IsIso (HF.map (m.ε.app C) ≫
        (integralComparisonRoosBridge l F X ρF _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)) :=
      IsIso.of_isIso_comp_left (HF.map (T.map e.hom)) _
    exact IsIso.of_isIso_comp_right _
      ((integralComparisonRoosBridge l F X ρF _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom))
  let := hε
  have ht : SL.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫ H.map e.hom ≫
      (integralComparisonRoosBridge l L X ρL C).hom = DerivedCategory.Q.map f := by
    let R := coefficientSequenceRestriction l L X
    let A := integralComparisonConstantAdjunction l L X
    let δ := (Functor.const ℕᵒᵖ : scalarReductionSource l L X ⥤
      ℕᵒᵖ ⥤ scalarReductionSource l L X).mapDerivedCategoryFactors
    have ha : SL.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫ H.map e.hom =
        A.homEquiv _ _ (δ.hom.app P.obj ≫ DerivedCategory.Q.map c ≫
          R.mapDerivedCategoryFactors.inv.app C) := by
      apply (A.homEquiv _ _).symm.injective
      erw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
      exact hc
    rw [← Category.assoc, ha]
    dsimp only [integralComparisonRoosBridge, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom]
    erw [← Category.assoc, ← A.homEquiv_naturality_right]
    dsimp only [R]
    simp only [Category.assoc]
    erw [(coefficientSequenceRestriction l L X).mapDerivedCategoryFactors.inv_hom_id_app]
    erw [Category.comp_id]
    exact integralComparisonRoosTranspose l L X ρL P.obj RC c
  have hz : DerivedCategory.Q.map f ≫
      (integralComparisonRoosBridge l L X ρL C).inv ≫ H.map h = z.hom := by
    rw [← ht]
    dsimp only [h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
    simp only [← H.map_comp_assoc, e.hom_inv_id_assoc]
    have hu := SL.adjunction.unit.naturality z.hom
    dsimp only [Functor.comp_map, Functor.id_map] at hu
    rw [← reassoc_of% hu]
    rw [SL.adjunction.right_triangle_components, Category.comp_id]
  have hχ := completedScalarComparison_spec l L F j X P
  have hnorm : χ.app (DerivedCategory.Q.obj P.obj) ≫
      b.realization.hom.app (DerivedCategory.Q.obj P.obj) =
      completedScalarCounit l L F j X P.obj ≫
        DerivedCategory.Q.map ((completedScalarChainComparison l L F j X).app P.obj) ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.inv) ≫
        (integralComparisonRoosBridge l F X ρF _).inv ≫
        inv (HF.map (m.ε.app C)) ≫ HF.map (T.map e.inv) := by
    exact scalarCounit_normalization_of_fac (χ.app _) (b.realization.hom.app _)
      (HF.mapIso (T.mapIso e)) (HF.map (m.ε.app C))
      (integralComparisonRoosBridge l F X ρF _)
      ((integralOperationsRoosFunctor ⋙ DerivedCategory.Q).mapIso q) _ _ _ hn hχ
  have htrans := scalarQuotientRoosTensorTranspose l L F j X ρL ρF P C κ c hct q hq D h a ha
  have hcalc : B.map z.hom ≫ χ.app (H.obj (DerivedCategory.Q.obj D)) ≫
      b.realization.hom.app (H.obj (DerivedCategory.Q.obj D)) ≫
      HF.map (T.map (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) ≫
      HF.map (m.ε.app D) ≫ (integralComparisonRoosBridge l F X ρF _).hom =
      B.map (z.hom ≫ (integralComparisonRoosBridge l L X ρL D).hom) ≫
        completedScalarCounit l L F j X
          (integralOperationsRoos
            (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
              D).asFunctor) ≫
        DerivedCategory.Q.map
          (scalarRoosMap (completedOrdinaryScalarExtension l L F j X)
            (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
              D).asFunctor ≫ integralOperationsRoosMap a) := by
    rw [χ.naturality_assoc, b.realization.hom.naturality_assoc]
    dsimp only [Functor.comp_map]
    rw [reassoc_of% hnorm]
    have hz' : DerivedCategory.Q.map f ≫
        (integralComparisonRoosBridge l L X ρL C).inv ≫ H.map h ≫
        (integralComparisonRoosBridge l L X ρL D).hom =
        z.hom ≫ (integralComparisonRoosBridge l L X ρL D).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ (integralComparisonRoosBridge l L X ρL D).hom) hz
    rw [hz'] at htrans
    simpa only [h, HF, T, m, B, Functor.map_comp, Category.assoc] using htrans
  apply (cancel_epi (B.map (z.hom ≫
    (integralComparisonRoosBridge l L X ρL D).hom))).1
  have hb : B.map (z.hom ≫ (integralComparisonRoosBridge l L X ρL D).hom) ≫
      B.map (integralComparisonRoosBridge l L X ρL D).inv = B.map z.hom := by
    rw [← B.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp only [B] at hb
  simpa only [H, HF, T, m, B, χ, Category.assoc, reassoc_of% hb] using hcalc

end WeilConjectures
