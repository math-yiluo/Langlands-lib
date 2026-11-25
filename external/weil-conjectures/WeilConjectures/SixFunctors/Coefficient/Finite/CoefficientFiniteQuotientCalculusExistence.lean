/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair
import WeilConjectures.SixFunctors.Coefficient.CoefficientPrescribedPairTensorModels
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement

/-! # Existence of the finite quotient calculus

Source: Stacks 06YY, 07A4 and 0941
(blueprint: lem-coef-finite-quotient-calculus-existence).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] WeilConjectures.coefficientFiniteQuotientExtensionAdditive
universe t u c v r w a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] SheafOfModules.instPreadditive HomologicalComplex.instPreadditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

-- Normalize the sheafification unit before substituting the large coefficient rings.
private theorem ordinaryAdjunctionNormalized
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B)
    (F : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom a M f ≫ eqToHom (hobj N).symm) :
    ∃ adj : F ⊣ SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map a),
      ∀ M V x, (adj.unit.app M).val.app V x =
        (eqToHom (hobj M).symm).val.app V
          ((toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app V
            ((ModuleCat.extendRestrictScalarsAdj (a.hom.app V).hom).unit.app
              (M.val.obj V) x)) := by
  exact SheafOfModules.ScalarReductionProof.tensorAdjunction_of_identifications a F hobj hmap

section OrdinaryCore
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B)
  (F : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
  (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
  (hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hobj M) ≫
    SheafOfModules.changeOfRingsHom a M f ≫ eqToHom (hobj N).symm)

private structure OrdinaryModel where
  adjunction : F ⊣ SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  unit : ∀ M V x,
    coefficientRestrictionSection ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
      (F.obj M) V ((adjunction.unit.app M).val.app V x) =
    (eqToHom (hobj M).symm).val.app V
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app V
        ((ModuleCat.extendRestrictScalarsAdj (a.hom.app V).hom).unit.app
          (M.val.obj V) x))

private noncomputable def ordinaryModel : OrdinaryModel.{c, v, r} a F hobj :=
  { adjunction := (ordinaryAdjunctionNormalized a F hobj hmap).choose
    unit := (ordinaryAdjunctionNormalized a F hobj hmap).choose_spec }

private theorem ordinaryModel_forward_unit
    (d : OrdinaryModel.{c, v, r} a F hobj)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (eqToHom (hobj M)).val.app V ((d.adjunction.unit.app M).val.app V x) =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app V
        ((ModuleCat.extendRestrictScalarsAdj (a.hom.app V).hom).unit.app
          (M.val.obj V) x) := by
  have he := congrArg ((eqToHom (hobj M)).val.app V) (d.unit M V x)
  apply he.trans
  exact congrArg (fun f ↦ f.val.app V
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app V
      ((ModuleCat.extendRestrictScalarsAdj (a.hom.app V).hom).unit.app (M.val.obj V) x)))
    (eqToIso (hobj M)).inv_hom_id

end OrdinaryCore

private theorem ordinaryModel_section_unit
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    {A B : Sheaf J CommRingCat.{max c v u}} (a : A ⟶ B)
    (F : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⥤
        SheafOfModules.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (d : OrdinaryModel a F hobj)
    (M : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) (V : Cᵒᵖ) (x : M.val.obj V) :
    coefficientRestrictionSection ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
      (F.obj M) V ((d.adjunction.unit.app M).val.app V x) =
        (eqToHom (hobj M).symm).val.app V
          (coefficientChangeOfRingsUnitSection.{u, c, v} J A B a M V x) := by
  exact d.unit M V x

private def OrdinaryForwardUnit
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    {A B : Sheaf J CommRingCat.{max c v u}} (a : A ⟶ B)
    (F : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⥤
        SheafOfModules.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (am : F ⊣ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)) : Prop :=
  ∀ (M : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) (V : Cᵒᵖ) (x : M.val.obj V),
    (eqToHom (hobj M)).val.app V ((am.unit.app M).val.app V x) =
      coefficientChangeOfRingsUnitSection.{u, c, v} J A B a M V x

private theorem ordinaryModel_section_forward_unit
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    {A B : Sheaf J CommRingCat.{max c v u}} (a : A ⟶ B)
    (F : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⥤
        SheafOfModules.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (d : OrdinaryModel a F hobj) : OrdinaryForwardUnit.{u, c, v} a F hobj d.adjunction := by
  exact fun M V x ↦ ordinaryModel_forward_unit a F hobj d M V x

section GenericPair
open SheafOfModules
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
  [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]

@[no_expose] private noncomputable def scalarPairWithSectionAdjunction
    (E : scalarModules J R ⥤ scalarModules J S)
    (hobj : ∀ M, E.obj M = changeOfRings a M)
    (hmap : ∀ {M N : scalarModules J R} (f : M ⟶ N),
      E.map f = eqToHom (hobj M) ≫ changeOfRingsHom a M f ≫
        eqToHom (hobj N).symm)
    (hadd : E.Additive)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶ scalarHomotopy E hadd ⋙ DerivedCategory.Qh)
    (hF : F.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (scalarModules J R) (.up ℤ)))
    (hc : ∀ P : CochainComplex (scalarModules J R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (am : E ⊣ scalarRestriction a)
    (hu : OrdinaryForwardUnit.{r, c, v} a E hobj am)
    (d : F ⊣ scalarDerivedRestriction a)
    (hd : ∀ (P : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      d.unit.app (DerivedCategory.Q.obj P) ≫
        (scalarDerivedRestriction a).map
          (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (scalarRestriction a).mapDerivedCategoryFactorsh.hom.app
          ((E.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
        DerivedCategory.Qh.map ((am.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
    ScalarDerivedPair a :=
  CategoryTheory.ScalarHomTensor.scalarPairWithAdjunction.{c, v, r, w} a E hobj hmap hadd
    F ε hF hc am (fun M V x ↦ hu M V x) d hd

omit [EssentiallySmall.{max c v r} C] in
private theorem scalarComparison_model
    (E : scalarModules J R ⥤ scalarModules J S) (hE : E.Additive)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶ scalarHomotopy E hE ⋙ DerivedCategory.Qh)
    (P : CochainComplex (scalarModules J R) ℤ)
    (hε : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
    scalarPairComplexComparison E hE F ε P =
      (coefficientLocalizedCounitModel F P ((scalarComplex E hE).obj P)
        (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) hε).hom := by
  rfl

end GenericPair

private theorem replaceGeneratorUnits {A B C D : Type*} {f : A → D} {g : B → C → D}
    {x x' : A} {y y' : B} {z z' : C} (h : f x = g y z)
    (hx : x = x') (hy : y = y') (hz : z = z') : f x' = g y' z' := by
  cases hx
  cases hy
  cases hz
  exact h

section GenericSquare
open SheafOfModules CategoryTheory.ScalarHomTensor
private theorem prescribedTensorGenerators
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{max c v r} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
    (s : ScalarDerivedPair a)
    (SR : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (SS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S))
    (TR : CoefficientTensorModels.{r, c, v, w} J R SR)
    (TS : CoefficientTensorModels.{r, c, v, w} J S SS)
    (c : PairTensorComparison.{c, v, r, w} a s SR SS TR TS)
    (P Q : CochainComplex (scalarModules J R) ℤ) :
    CoefficientScalarTensorGenerators.{r, c, v} J R S s.extension
      (hF := s.extension_additive)
      (fun M V x ↦ (eqToHom (s.extension_obj M).symm).val.app V
        (coefficientChangeOfRingsUnitSection.{r, c, v} J R S a M V x))
      P Q (c.complexIso P Q) := by
  intro p q k hpq V x y
  exact replaceGeneratorUnits (c.generators P Q p q k hpq V x y)
    (pairUnit_eq_tensorSection.{c, v, r, w} a s _ V _)
    (pairUnit_eq_tensorSection.{c, v, r, w} a s _ V x)
    (pairUnit_eq_tensorSection.{c, v, r, w} a s _ V y)

end GenericSquare

private theorem replaceSquareModels
    {A : Type a} {B : Type b} {K : Type c}
    [Category.{v} A] [Category.{w} B] [Category.{r} K]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (F : A ⥤ B) (Q : K ⥤ B)
    {X Y Z : A} {X' Y' Z' N : K}
    (s : Z ⟶ T.obj (X, Y)) (μ : T ⋙ F ⟶ F.prod F ⋙ T')
    (p : F.obj X ⟶ Q.obj X') (q : F.obj Y ⟶ Q.obj Y')
    (z : F.obj Z ⟶ Q.obj Z') (e : Z' ⟶ N)
    (t : Q.obj N ⟶ T'.obj (Q.obj X', Q.obj Y'))
    (p' : F.obj X ⟶ Q.obj X') (q' : F.obj Y ⟶ Q.obj Y') (z' : F.obj Z ⟶ Q.obj Z')
    (hp : p = p') (hq : q = q') (hz : z = z')
    (h : CoefficientTensorComparisonSquare T T' F Q s μ p q z e t) :
    CoefficientTensorComparisonSquare T T' F Q s μ p' q' z' e t := by
  cases hp
  cases hq
  cases hz
  exact h

private theorem quotientIso_hom
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (P : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).hom.app P = 𝟙 _ := rfl

private theorem quotientIso_inv
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (P : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).inv.app P = 𝟙 _ := rfl

private theorem homotopyFactors_inv
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (P : CochainComplex A ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := rfl

attribute [local implicit_reducible] CategoryTheory.uniformProd
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
attribute [local irreducible] coefficientFiniteQuotientExistence
  coefficientFiniteQuotientDerivedExistence HasDerivedCategory.standard
  coefficientTotalTensor coefficientFiniteTensorModelIso
  CoefficientTensorModels.iso CoefficientClosedStructure.tensor

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem quotientExtension_map {m n : ℕ} (h : n ≤ m)
    {M N : normalizedDVRModules l E W m} (f : M ⟶ N) :
    (coefficientFiniteQuotientExtension l E W h).map f =
      eqToHom (coefficientFiniteQuotientExtension_obj l E W h M) ≫
        SheafOfModules.changeOfRingsHom (coefficientFiniteQuotient l E W h) M f ≫
          eqToHom (coefficientFiniteQuotientExtension_obj l E W h N).symm := by
  exact (coefficientFiniteQuotientExistence l E W h).choose_spec.choose_spec.choose f

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private noncomputable def quotientOrdinaryModel {m n : ℕ} (h : n ≤ m) :
    OrdinaryModel.{t+1, t, max u (t+1)}
      (coefficientFiniteQuotient l E W h)
      (coefficientFiniteQuotientExtension l E W h)
      (coefficientFiniteQuotientExtension_obj l E W h) :=
  ordinaryModel.{t+1, t, max u (t+1)} (coefficientFiniteQuotient l E W h)
    (coefficientFiniteQuotientExtension l E W h)
    (coefficientFiniteQuotientExtension_obj l E W h)
    (quotientExtension_map l E W h)

attribute [local irreducible] quotientOrdinaryModel

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem quotientUnit {m n : ℕ} (h : n ≤ m)
    (M : normalizedDVRModules l E W m) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    coefficientRestrictionSection (normalizedDVRQuotient l E W h)
      ((coefficientFiniteQuotientExtension l E W h).obj M) V
        (((quotientOrdinaryModel l E W h).adjunction.unit.app M).val.app V x) =
      coefficientFiniteQuotientUnitSection l E W h M V x := by
  exact ordinaryModel_section_unit.{u, t+1, t}
    (coefficientFiniteQuotient l E W h) (coefficientFiniteQuotientExtension l E W h)
    (coefficientFiniteQuotientExtension_obj l E W h) (quotientOrdinaryModel l E W h) M V x

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem quotientDerived_isLeftDerived {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientDerived l E W h).IsLeftDerivedFunctor
      (coefficientFiniteQuotientCounit l E W h)
      (HomotopyCategory.quasiIso (normalizedDVRModules l E W m) (.up ℤ)) := by
  exact (coefficientFiniteQuotientDerivedExistence l E W h).choose_spec.choose_spec.1

attribute [local irreducible] coefficientFiniteQuotientExtension
  coefficientFiniteQuotientDerived coefficientFiniteQuotientCounit

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem quotientDerivedAdjunction {m n : ℕ} (h : n ≤ m)
    (am : coefficientFiniteQuotientExtension l E W h ⊣ normalizedDVRModuleRes l E W h) :
    ∃ ad : coefficientFiniteQuotientDerived l E W h ⊣ normalizedDVRRes l E W h,
        ∀ (P : CochainComplex (normalizedDVRModules l E W m) ℤ),
          CochainComplex.IsKFlatIndependentCoefficients
            (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P →
          ad.unit.app (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
            (normalizedDVRRes l E W h).map ((coefficientFiniteQuotientCounit l E W h).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
            (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactorsh.hom.app
              (((coefficientFiniteQuotientExtension l E W h).mapHomotopyCategory
                (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
            DerivedCategory.Qh.map ((am.mapHomotopyCategory (.up ℤ)).unit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨ad, hd⟩ := ScalarReductionDerivedProof.derivedAdjunction_of_resolutions
    (coefficientFiniteQuotientExtension l E W h) (normalizedDVRModuleRes l E W h) am
    (coefficientFiniteQuotientDerived l E W h) (coefficientFiniteQuotientCounit l E W h)
    (quotientDerived_isLeftDerived l E W h)
    (by
      intro X
      obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      obtain ⟨P, f, hP, hf⟩ := ScalarReductionDerivedProof.kFlatResolutions
        (J := Scheme.ProEt.topology W) (O := integralCoefficientCommRingSheaf l E W m) G
      exact ⟨_, (HomotopyCategory.quotient _ (.up ℤ)).map f,
        coefficientFiniteQuotientCounit_isIso l E W h P hP,
        (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩)
  exact ⟨ad, fun P _ ↦ hd ((HomotopyCategory.quotient _ (.up ℤ)).obj P)⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[no_expose] private noncomputable def quotientDerivedAdj {m n : ℕ} (h : n ≤ m) :
    coefficientFiniteQuotientDerived l E W h ⊣ normalizedDVRRes l E W h :=
  (quotientDerivedAdjunction l E W h (quotientOrdinaryModel l E W h).adjunction).choose

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem quotientForwardUnit {m n : ℕ} (h : n ≤ m) :
    OrdinaryForwardUnit.{u, t+1, t} (coefficientFiniteQuotient l E W h)
      (coefficientFiniteQuotientExtension l E W h)
      (coefficientFiniteQuotientExtension_obj l E W h)
      (quotientOrdinaryModel l E W h).adjunction := by
  exact ordinaryModel_section_forward_unit.{u, t+1, t}
    (coefficientFiniteQuotient l E W h) (coefficientFiniteQuotientExtension l E W h)
    (coefficientFiniteQuotientExtension_obj l E W h) (quotientOrdinaryModel l E W h)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem quotientDerivedUnit {m n : ℕ} (h : n ≤ m) :
    letI := coefficientFiniteQuotientExtensionAdditive l E W h
    ∀ (P : CochainComplex (normalizedDVRModules l E W m) ℤ),
          CochainComplex.IsKFlatIndependentCoefficients
            (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P →
          (quotientDerivedAdj l E W h).unit.app (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
            (normalizedDVRRes l E W h).map ((coefficientFiniteQuotientCounit l E W h).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
            (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactorsh.hom.app
              (((coefficientFiniteQuotientExtension l E W h).mapHomotopyCategory
                (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
            DerivedCategory.Qh.map (((quotientOrdinaryModel l E W h).adjunction.mapHomotopyCategory
              (.up ℤ)).unit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  exact (quotientDerivedAdjunction l E W h (quotientOrdinaryModel l E W h).adjunction).choose_spec

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [local irreducible] scalarPairWithSectionAdjunction in
@[no_expose] private noncomputable def quotientPair {m n : ℕ} (h : n ≤ m) :
    SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology W) (coefficientFiniteQuotient l E W h) :=
    scalarPairWithSectionAdjunction.{t+1, t, u, max (t+2) (u+1)}
      (coefficientFiniteQuotient l E W h)
      (coefficientFiniteQuotientExtension l E W h)
      (coefficientFiniteQuotientExtension_obj l E W h)
      (quotientExtension_map l E W h)
      (coefficientFiniteQuotientExtensionAdditive l E W h)
      (coefficientFiniteQuotientDerived l E W h) (coefficientFiniteQuotientCounit l E W h)
      (quotientDerived_isLeftDerived l E W h)
      (coefficientFiniteQuotientCounit_isIso l E W h) ((quotientOrdinaryModel l E W h).adjunction)
      (quotientForwardUnit l E W h) (quotientDerivedAdj l E W h)
      (quotientDerivedUnit l E W h)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[instance_reducible] private noncomputable def quotientHasDerivedFamily :
    ∀ A : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t+1)},
      HasDerivedCategory.{max (t+2) (u+1)}
        (SheafOfModules.scalarModules (Scheme.ProEt.topology W) A) :=
  fun _ ↦ HasDerivedCategory.standard _

attribute [local instance] quotientHasDerivedFamily

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[no_expose] private noncomputable def quotientComparison
    (T : CoefficientDerivedSystemTensors l E W) {m n : ℕ} (h : n ≤ m) :
    CategoryTheory.ScalarHomTensor.PairTensorComparison.{t+1, t, u, max (t+2) (u+1)}
      (coefficientFiniteQuotient l E W h) (quotientPair l E W h)
      (T.finiteClosed m) (T.finiteClosed n) (T.finiteTensorModel m)
      (T.finiteTensorModel n) := by
  exact (coefficientPrescribedPairTensorComparison.{t+1, t, u, max (t+2) (u+1)}
    (coefficientFiniteQuotient l E W h) (quotientPair l E W h)
    (T.finiteClosed m) (T.finiteClosed n) (T.finiteTensorModel m)
    (T.finiteTensorModel n)).some

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[no_expose] private noncomputable def quotientData
    (T : CoefficientDerivedSystemTensors l E W) : CoefficientFiniteQuotientData l E W T where
  ordinaryAdjunction := fun h ↦ (quotientOrdinaryModel l E W h).adjunction
  adjunction := fun h ↦ (quotientDerivedAdjunction l E W h
    (quotientOrdinaryModel l E W h).adjunction).choose
  preservesKFlat := fun h ↦ (quotientComparison l E W T h).preservesKFlat
  tensor := fun h ↦ (quotientComparison l E W T h).iso

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem quotientData_ordinary (T : CoefficientDerivedSystemTensors l E W) :
    CoefficientFiniteQuotientOrdinaryUnit l E W T (quotientData l E W T) := by
  exact fun h M V x ↦ quotientUnit l E W h M V x

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem quotientData_derived (T : CoefficientDerivedSystemTensors l E W) :
    CoefficientFiniteQuotientDerivedUnit l E W T (quotientData l E W T) := by
  intro m n h P hP
  let am := (quotientOrdinaryModel l E W h).adjunction
  let ad := (quotientDerivedAdjunction l E W h am).choose
  have hh := (quotientDerivedAdjunction l E W h am).choose_spec P hP
  have hf : (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactorsh.hom.app
      (((coefficientFiniteQuotientExtension l E W h).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactors.hom.app
        (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
          (.up ℤ)).obj P) := by
    change (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
          (.up ℤ)).obj P)) = _
    erw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [quotientIso_hom, quotientIso_inv, homotopyFactors_inv]
    erw [(normalizedDVRModuleRes l E W h).mapDerivedCategory.map_id
      (DerivedCategory.Q.obj
        (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex (.up ℤ)).obj P)),
      DerivedCategory.Qh.map_id]
    change 𝟙 _ ≫ (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactors.hom.app
      (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex (.up ℤ)).obj P) ≫
        𝟙 _ ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  erw [hf, Adjunction.mapHomotopyCategory_unit_app_quotient] at hh
  have hc : (coefficientFiniteQuotientModel l E W h P hP).hom =
      (coefficientFiniteQuotientCounit l E W h).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    unfold coefficientFiniteQuotientModel coefficientLocalizedCounitModel
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
      Iso.app_inv, quotientIso_hom, quotientIso_inv]
    erw [(coefficientFiniteQuotientDerived l E W h).map_id (DerivedCategory.Q.obj P)]
    change 𝟙 _ ≫ (coefficientFiniteQuotientCounit l E W h).app _ ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  change ad.unit.app _ ≫ _ ≫ _ = _
  rw [hc]
  exact hh

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem quotientData_tensor (T : CoefficientDerivedSystemTensors l E W) :
    CoefficientFiniteQuotientTensorNormalization l E W T (quotientData l E W T) := by
  intro m n h P Q hP hQ
  refine ⟨(quotientComparison l E W T h).complexIso P Q, ?_, ?_⟩
  · exact prescribedTensorGenerators.{t+1, t, u, max (t+2) (u+1)}
      (coefficientFiniteQuotient l E W h) (quotientPair l E W h)
      (T.finiteClosed m) (T.finiteClosed n) (T.finiteTensorModel m) (T.finiteTensorModel n)
      (quotientComparison l E W T h) P Q
  · have hn := (quotientComparison l E W T h).normalization P Q hP hQ
    have model (K : CochainComplex (normalizedDVRModules l E W m) ℤ)
        (hK : CochainComplex.IsKFlatIndependentCoefficients
          (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) K) :
        SheafOfModules.scalarPairComplexComparison
          (quotientPair l E W h).extension (quotientPair l E W h).extension_additive
          (quotientPair l E W h).derived (quotientPair l E W h).counit K =
          (coefficientFiniteQuotientModel l E W h K hK).hom := by
      exact scalarComparison_model.{t+1, t, u, max (t+2) (u+1)}
        (quotientPair l E W h).extension (quotientPair l E W h).extension_additive
        (quotientPair l E W h).derived (quotientPair l E W h).counit K
        (coefficientFiniteQuotientCounit_isIso l E W h K hK)
    have hnorm := replaceSquareModels _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (model P hP) (model Q hQ)
      (model _ (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W m) P Q hP hQ)) hn
    unfold coefficientFiniteTensorModelIso
    exact hnorm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/--
For any tensor presentation, every finite quotient map of the normalized coefficient
rings has its ordinary and derived scalar adjunctions, K-flat preservation, and the
pure-tensor comparison.  These data assemble into the finite quotient calculus.
Source: Stacks 06YY, 07A4 and 0941.
(blueprint: lem-coef-finite-quotient-calculus-existence)
-/
theorem coefficientFiniteQuotientCalculus_exists
    (T : CoefficientDerivedSystemTensors l E W) :
    Nonempty (CoefficientFiniteQuotientCalculus l E W T) := by
  exact ⟨{ toCoefficientFiniteQuotientData := quotientData l E W T
           ordinary_unit := quotientData_ordinary l E W T
           unit_model := quotientData_derived l E W T
           tensor_model := quotientData_tensor l E W T }⟩

end WeilConjectures
