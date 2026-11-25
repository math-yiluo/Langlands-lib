/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares

/-! # K-flat descent of a finite quotient/pullback comparison

Source: Stacks Tags 06YY and 07A4.
(blueprint: lem-pur-finite-quotient-pullback-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory
  coefficientFiniteQuotientExtension coefficientFiniteQuotientDerived

attribute [local instance] sfIntrinsicPullback_additive
  coefficientFiniteQuotientExtensionAdditive

private theorem cochainComparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (p : A ⥤ B) [p.Additive] [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    (q : C ⥤ D) [q.Additive] [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    (s : A ⥤ C) [s.Additive] (t : B ⥤ D) [t.Additive]
    (S : DerivedCategory A ⥤ DerivedCategory C)
    (T : DerivedCategory B ⥤ DerivedCategory D)
    (εS : DerivedCategory.Q ⋙ S ⟶ s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εT : DerivedCategory.Q ⋙ T ⟶ t.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : p.mapHomologicalComplex (.up ℤ) ⋙ t.mapHomologicalComplex (.up ℤ) ≅
      s.mapHomologicalComplex (.up ℤ) ⋙ q.mapHomologicalComplex (.up ℤ))
    (R : ObjectProperty (CochainComplex A ℤ))
    (ff : ((whiskeringLeft R.FullSubcategory (DerivedCategory A) (DerivedCategory D)).obj
      (R.ι ⋙ DerivedCategory.Q)).FullyFaithful)
    (hS : ∀ P, R P → IsIso (εS.app P))
    (hT : ∀ P, R P → IsIso (εT.app ((p.mapHomologicalComplex (.up ℤ)).obj P))) :
    ∃! a : p.mapDerivedCategory ⋙ T ≅ S ⋙ q.mapDerivedCategory,
      ∀ P, R P →
        T.map (p.mapDerivedCategoryFactors.hom.app P) ≫
          εT.app ((p.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map (c.hom.app P) =
        a.hom.app (DerivedCategory.Q.obj P) ≫ q.mapDerivedCategory.map (εS.app P) ≫
          q.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj P) := by
  let F := p.mapDerivedCategory ⋙ T
  let G := S ⋙ q.mapDerivedCategory
  let H := s.mapHomologicalComplex (.up ℤ) ⋙ q.mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q
  let α : DerivedCategory.Q ⋙ F ⟶ H :=
    whiskerRight p.mapDerivedCategoryFactors.hom T ≫
      whiskerLeft (p.mapHomologicalComplex (.up ℤ)) εT ≫
        whiskerRight c.hom DerivedCategory.Q
  let β : DerivedCategory.Q ⋙ G ⟶ H :=
    whiskerRight εS q.mapDerivedCategory ≫
      whiskerLeft (s.mapHomologicalComplex (.up ℤ)) q.mapDerivedCategoryFactors.hom
  have hα (P) (hP : R P) : IsIso (α.app P) := by
    have := hT P hP
    change IsIso (T.map (p.mapDerivedCategoryFactors.hom.app P) ≫
      εT.app ((p.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (c.hom.app P))
    infer_instance
  have hβ (P) (hP : R P) : IsIso (β.app P) := by
    have := hS P hP
    change IsIso (q.mapDerivedCategory.map (εS.app P) ≫
      q.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj P))
    infer_instance
  exact SequenceDerivedProof.normalizedComparisonDescent
    DerivedCategory.Q R ff F G H α β hα hβ

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def quotientComplexCounit (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    DerivedCategory.Q ⋙ coefficientFiniteQuotientDerived l E W h ⟶
      (coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  CategoryTheory.derivedCochainCounit _ _ (coefficientFiniteQuotientCounit l E W h)

private theorem quotientComplexCounit_app (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := integralCoefficientCommRingSheaf l E W m) P) :
    (quotientComplexCounit l E W h).app P =
      (coefficientFiniteQuotientModel l E W h P hP).hom := by
  rw [quotientComplexCounit, CategoryTheory.cochainCounit_app_eq]
  simp only [coefficientFiniteQuotientModel, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, asIso_hom]
  change _ = (coefficientFiniteQuotientDerived l E W h).map (𝟙 _) ≫ _ ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, asIso_hom]

attribute [local irreducible] quotientComplexCounit

/-- Descend a finite quotient comparison of complexes using the universal quotient counits.
Source: Stacks Tags 06YY and 07A4
(blueprint: lem-pur-finite-quotient-pullback-descent).
Proof: transport the homotopy counits to cochain localization. On K-flat complexes
these are precisely the prescribed quotient models. The first horizontal pullback
preserves the K-flat representatives by hypothesis, and both horizontal pullbacks
are exact. Apply the existing normalized comparison descent to their two composites.
Restriction to K-flat representatives is fully faithful, so its counit square fixes
the descended natural isomorphism uniquely. No termwise flatness condition is imposed
on the given representatives. -/
theorem finiteQuotientPullbackDescent {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m)
    (c : (sfIntrinsicPullback
        (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex (.up ℤ) ⋙
        (coefficientFiniteQuotientExtension l E X h).mapHomologicalComplex (.up ℤ) ≅
      (coefficientFiniteQuotientExtension l E Y h).mapHomologicalComplex (.up ℤ) ⋙
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ))
    (hgood : ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (R := integralCoefficientCommRingSheaf l E Y m) P →
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (R := integralCoefficientCommRingSheaf l E X m)
        (((sfIntrinsicPullback
          (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃! e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f,
      ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (R := integralCoefficientCommRingSheaf l E Y m) P),
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            (coefficientFiniteQuotientModel l E Y h P hP).hom ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientFiniteQuotientDerived l E X h).map
          ((sfIntrinsicPullback
            (finiteCoefficientRing l E (m + 1)) f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientFiniteQuotientModel l E X h _ (hgood P hP)).hom ≫
          DerivedCategory.Q.map (c.hom.app P) := by
  have := sfIntrinsicPullback_additive (finiteCoefficientRing l E (m + 1)) f
  have := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  have := coefficientFiniteQuotientExtensionAdditive l E X h
  have := coefficientFiniteQuotientExtensionAdditive l E Y h
  let p : normalizedDVRModules l E Y m ⥤ normalizedDVRModules l E X m :=
    sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f
  let q : normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
    sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  let s := coefficientFiniteQuotientExtension l E Y h
  let t := coefficientFiniteQuotientExtension l E X h
  let S := coefficientFiniteQuotientDerived l E Y h
  let T := coefficientFiniteQuotientDerived l E X h
  have : p.Additive := sfIntrinsicPullback_additive _ f
  have : q.Additive := sfIntrinsicPullback_additive _ f
  have : PreservesFiniteLimits p := sfIntrinsicPullback_preservesFiniteLimits _ f
  have : PreservesFiniteColimits p := sfIntrinsicPullback_preservesFiniteColimits _ f
  have : PreservesFiniteLimits q := sfIntrinsicPullback_preservesFiniteLimits _ f
  have : PreservesFiniteColimits q := sfIntrinsicPullback_preservesFiniteColimits _ f
  let εS := quotientComplexCounit l E Y h
  let εT := quotientComplexCounit l E X h
  let R : ObjectProperty (CochainComplex (normalizedDVRModules l E Y m) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := integralCoefficientCommRingSheaf l E Y m)
  obtain ⟨ff⟩ := SequenceDerivedProof.kflatWhiskering
    (D := proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1)))
    (integralCoefficientCommRingSheaf l E Y m)
  have hS (P) (hP : R P) : IsIso (εS.app P) := by
    rw [quotientComplexCounit_app l E Y h P hP]
    infer_instance
  have hT (P) (hP : R P) :
      IsIso (εT.app ((p.mapHomologicalComplex (.up ℤ)).obj P)) := by
    rw [quotientComplexCounit_app l E X h _ (hgood P hP)]
    infer_instance
  have hd := cochainComparison p q s t S T εS εT c R ff hS hT
  obtain ⟨a, ha, hu⟩ := hd
  refine ⟨a, ?_, ?_⟩
  · intro P hP
    have hp := ha P hP
    rw [quotientComplexCounit_app l E Y h P hP,
      quotientComplexCounit_app l E X h _ (hgood P hP)] at hp
    exact hp.symm
  · intro a' ha'
    apply hu a'
    intro P hP
    rw [quotientComplexCounit_app l E Y h P hP,
      quotientComplexCounit_app l E X h _ (hgood P hP)]
    exact (ha' P hP).symm

end WeilConjectures
