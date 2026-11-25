/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRScalarCokernelComparison
import WeilConjectures.SixFunctors.SheafRestrictionTowerData.StrictRestrictionTower

/-! # Scalar cokernels of strict finite flat DVR models

Source: Stacks Tags 06YS, 06YY, 03EK and 05RT; blueprint DVR effectivity,
proof paragraphs 1--3. (blueprint: lem-coef-normalized-dvr-flat-cokernel).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 30000] SheafOfModules.instPreadditive
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace WeilConjectures
section ExactHelpers
universe a b c v w z
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v} A] [Category.{w} B] [Category.{z} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (H : A ⥤ B) (R : B ⥤ C) (S : A ⥤ C)
  [H.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  (i : H ⋙ R ≅ S)

private theorem exactComp_fac (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso H R ≪≫
        Functor.mapDerivedCategoryNatIso i).hom.app (DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategoryFactors.hom.app K =
    R.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app
        ((H.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso i (.up ℤ)).hom.app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryNatIso_fac]
  have h := Functor.mapDerivedCategoryCompIso_fac H R K
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  congr 1
  apply CategoryTheory.Functor.congr_map
  ext j
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f,
    Iso.refl_hom, NatTrans.id_app]
  exact Category.id_comp _

private theorem exactComp_map (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (f : L ⟶ (H.mapHomologicalComplex (.up ℤ)).obj K) :
    R.mapDerivedCategory.map
        (DerivedCategory.Q.map f ≫ H.mapDerivedCategoryFactors.inv.app K) ≫
      (Functor.mapDerivedCategoryCompIso H R ≪≫
        Functor.mapDerivedCategoryNatIso i).hom.app (DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategoryFactors.hom.app K =
    R.mapDerivedCategoryFactors.hom.app L ≫
      DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map f ≫
        (Functor.mapHomologicalComplexCompIso i (.up ℤ)).hom.app K) := by
  rw [exactComp_fac]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [← R.mapDerivedCategory.map_comp_assoc
    (H.mapDerivedCategoryFactors.inv.app K) (H.mapDerivedCategoryFactors.hom.app K),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := R.mapDerivedCategoryFactors.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]

end ExactHelpers

private theorem exact_comp_inv
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (H : A ⥤ B) (R : B ⥤ C) (S : A ⥤ C)
    [H.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (i : H ⋙ R ≅ S) (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (f : L ⟶ (H.mapHomologicalComplex (.up ℤ)).obj K) :
    DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map f ≫
        (Functor.mapHomologicalComplexCompIso i (.up ℤ)).hom.app K) ≫
        S.mapDerivedCategoryFactors.inv.app K =
      R.mapDerivedCategoryFactors.inv.app L ≫ R.mapDerivedCategory.map
        (DerivedCategory.Q.map f ≫ H.mapDerivedCategoryFactors.inv.app K) ≫
      (Functor.mapDerivedCategoryCompIso H R ≪≫
        Functor.mapDerivedCategoryNatIso i).hom.app (DerivedCategory.Q.obj K) := by
  apply (cancel_epi (R.mapDerivedCategoryFactors.hom.app L)).1
  apply (cancel_mono (S.mapDerivedCategoryFactors.hom.app K)).1
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id, Iso.hom_inv_id_app_assoc]
  exact (exactComp_map H R S i K L f).symm

private theorem universal_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    (H : A ⥤ B) (R : B ⥤ C) (S : A ⥤ C) (i : H ⋙ R ≅ S)
    {M : C} {N : B} {K : A} (η : M ⟶ R.obj N) (η' : N ⟶ H.obj K)
    (hη : ∀ Z, Function.Bijective (fun f : N ⟶ Z ↦ η ≫ R.map f))
    (hη' : ∀ Z, Function.Bijective (fun f : K ⟶ Z ↦ η' ≫ H.map f)) :
    ∀ Z, Function.Bijective
      (fun f : K ⟶ Z ↦ (η ≫ R.map η' ≫ i.hom.app K) ≫ S.map f) := by
  intro Z
  convert (((i.app Z).homToEquiv (Z := M)).bijective.comp (hη _)).comp (hη' Z) using 1
  ext f
  have hn := i.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  change (η ≫ R.map η' ≫ i.hom.app K) ≫ S.map f =
    (η ≫ R.map (η' ≫ H.map f)) ≫ i.hom.app Z
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, hn]

private theorem universal_iso
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {M M' : B} {N N' : A} (eM : M ≅ M') (eN : N ≅ N')
    (η : M ⟶ R.obj N) (η' : M' ⟶ R.obj N')
    (he : η ≫ R.map eN.hom = eM.hom ≫ η')
    (hη' : ∀ Z, Function.Bijective (fun f : N' ⟶ Z ↦ η' ≫ R.map f)) :
    ∀ Z, Function.Bijective (fun f : N ⟶ Z ↦ η ≫ R.map f) := by
  intro Z
  have h : η = eM.hom ≫ η' ≫ R.map eN.inv := by
    have hh := congrArg (fun f ↦ f ≫ R.map eN.inv) he
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id] at hh
    erw [R.map_id, Category.comp_id] at hh
    exact hh
  rw [h]
  convert eM.symm.homFromEquiv.bijective.comp
    ((hη' Z).comp eN.homFromEquiv.bijective) using 1
  ext f
  change _ = eM.hom ≫ (η' ≫ R.map (eN.inv ≫ f))
  simp only [Functor.map_comp, Category.assoc]

private theorem sequence_map_congr {A : Type*} [Category A] {Y : ℕ → A}
    (u v : ∀ j : ℕ, Y (j + 1) ⟶ Y j) (h : u = v)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (Functor.ofOpSequence u).map f = (Functor.ofOpSequence v).map f := by
  subst v
  rfl

section CoefficientComposite
universe a₀ b₀ r₀
variable {C : Type a₀} [Category.{b₀} C] {J : GrothendieckTopology C}
  {coefficient : ℕ → Sheaf J RingCat.{r₀}} {completed : Sheaf J RingCat.{r₀}}

private abbrev coefficientRes
    (syst : SheafRestrictionTowerData.{a₀, b₀, r₀, r₀} coefficient completed)
    {m n : ℕ} (h : n ≤ m) :
    SheafOfModules.{r₀} (coefficient n) ⥤ SheafOfModules.{r₀} (coefficient m) :=
  SheafOfModules.restrictScalars.{r₀} (syst.quotient h)

variable [hsh : HasSheafify J AddCommGrpCat.{r₀}]
  [hw : J.WEqualsLocallyBijective AddCommGrpCat.{r₀}]
  [hder : ∀ n, HasDerivedCategory (SheafOfModules.{r₀} (coefficient n))]

private abbrev coefficientDerivedRes
    (syst : SheafRestrictionTowerData.{a₀, b₀, r₀, r₀} coefficient completed)
    [hlim : ∀ (m n : ℕ) (h : n ≤ m), PreservesFiniteLimits (coefficientRes syst h)]
    [hcolim : ∀ (m n : ℕ) (h : n ≤ m), PreservesFiniteColimits (coefficientRes syst h)]
    {m n : ℕ} (h : n ≤ m) :
    DerivedCategory (SheafOfModules.{r₀} (coefficient n)) ⥤
      DerivedCategory (SheafOfModules.{r₀} (coefficient m)) :=
  Functor.mapDerivedCategory (coefficientRes syst h)

private def coefficientDerivedComp
    (syst : SheafRestrictionTowerData.{a₀, b₀, r₀, r₀} coefficient completed)
    [hlim : ∀ (m n : ℕ) (h : n ≤ m), PreservesFiniteLimits (coefficientRes syst h)]
    [hcolim : ∀ (m n : ℕ) (h : n ≤ m), PreservesFiniteColimits (coefficientRes syst h)]
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    coefficientDerivedRes (syst := syst) hmn ⋙
        coefficientDerivedRes (syst := syst) hrm ≅
      coefficientDerivedRes (syst := syst) (le_trans hmn hrm) :=
  Functor.mapDerivedCategoryCompIso (coefficientRes syst hmn)
      (coefficientRes syst hrm) ≪≫
      Functor.mapDerivedCategoryNatIso (syst.finiteComp hrm hmn)

attribute [local irreducible] coefficientDerivedComp Functor.mapDerivedCategory

private theorem coefficientComposite_universal
    (syst : SheafRestrictionTowerData.{a₀, b₀, r₀, r₀} coefficient completed)
    [hlim : ∀ (m n : ℕ) (h : n ≤ m), PreservesFiniteLimits (coefficientRes syst h)]
    [hcolim : ∀ (m n : ℕ) (h : n ≤ m), PreservesFiniteColimits (coefficientRes syst h)]
    (P : ∀ j : ℕ, CochainComplex (SheafOfModules.{r₀} (coefficient j)) ℤ)
    (g : ∀ j : ℕ, P (j + 1) ⟶
      ((coefficientRes syst j.le_succ).mapHomologicalComplex (.up ℤ)).obj (P j))
    (hs : ∀ (j : ℕ) (Z : DerivedCategory (SheafOfModules.{r₀} (coefficient j))),
      Function.Bijective (fun f : DerivedCategory.Q.obj (P j) ⟶ Z ↦
        (DerivedCategory.Q.map (g j) ≫
          (coefficientRes syst j.le_succ).mapDerivedCategoryFactors.inv.app (P j)) ≫
          (coefficientDerivedRes (syst := syst) j.le_succ).map f))
    (n k : ℕ) : ∀ Z : DerivedCategory (SheafOfModules.{r₀} (coefficient n)),
    Function.Bijective (fun f : DerivedCategory.Q.obj (P n) ⟶ Z ↦
      (DerivedCategory.Q.map (syst.finiteMap P g n k) ≫
        (coefficientRes syst (Nat.le_add_right n (k + 1))).mapDerivedCategoryFactors.inv.app
          (P n)) ≫
        (coefficientDerivedRes (syst := syst) (Nat.le_add_right n (k + 1))).map f) := by
  induction k with
  | zero => exact hs n
  | succ k ih =>
    have hc := universal_comp
      (coefficientDerivedRes (syst := syst) (Nat.le_add_right n (k + 1)))
      (coefficientDerivedRes (syst := syst) (n + (k + 1)).le_succ)
      (coefficientDerivedRes (syst := syst) (Nat.le_add_right n (k + 2)))
      (coefficientDerivedComp (syst := syst) (n + (k + 1)).le_succ
        (Nat.le_add_right n (k + 1)))
      (DerivedCategory.Q.map (g (n + (k + 1))) ≫
        (coefficientRes syst (n + (k + 1)).le_succ).mapDerivedCategoryFactors.inv.app
          (P (n + (k + 1))))
      (DerivedCategory.Q.map (syst.finiteMap P g n k) ≫
        (coefficientRes syst (Nat.le_add_right n (k + 1))).mapDerivedCategoryFactors.inv.app
          (P n)) (hs (n + (k + 1))) ih
    have he := exact_comp_inv
      (coefficientRes syst (Nat.le_add_right n (k + 1)))
      (coefficientRes syst (n + (k + 1)).le_succ)
      (coefficientRes syst (Nat.le_add_right n (k + 2)))
      (syst.finiteComp (n + (k + 1)).le_succ (Nat.le_add_right n (k + 1)))
      (P n) (P (n + (k + 1))) (syst.finiteMap P g n k)
    intro Z
    have hcomp :
        DerivedCategory.Q.map (syst.finiteMap P g n (k + 1)) ≫
          (coefficientRes syst (Nat.le_add_right n (k + 2))).mapDerivedCategoryFactors.inv.app
            (P n) =
        (DerivedCategory.Q.map (g (n + (k + 1))) ≫
          (coefficientRes syst (n + (k + 1)).le_succ).mapDerivedCategoryFactors.inv.app
            (P (n + (k + 1)))) ≫
          (coefficientDerivedRes (syst := syst) (n + (k + 1)).le_succ).map
            (DerivedCategory.Q.map (syst.finiteMap P g n k) ≫
              (coefficientRes syst (Nat.le_add_right n (k + 1))).mapDerivedCategoryFactors.inv.app
                (P n)) ≫
          (coefficientDerivedComp (syst := syst) (n + (k + 1)).le_succ
            (Nat.le_add_right n (k + 1))).hom.app (DerivedCategory.Q.obj (P n)) := by
      rw [SheafRestrictionTowerData.finiteMap_succ, CategoryTheory.Functor.map_comp,
        Category.assoc, he]
      simp only [Category.assoc]
      unfold coefficientDerivedComp
      rfl
    rw [hcomp]
    exact hc Z

end CoefficientComposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

local instance (priority := 10000) instNormalizedDVRFlatCokernel1
    : EssentiallySmall.{max u (t + 1)} X.ProEt :=
  essentiallySmallSelf.{u} X.ProEt
local instance (priority := 10000) instNormalizedDVRFlatCokernel2
    : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
local instance (priority := 10000) instNormalizedDVRFlatCokernel3 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X

local instance instNormalizedDVRFlatCokernel4
    : HasDerivedCategory (completedIntegralModuleSheaves l E X D hl) :=
  HasDerivedCategory.standard _

/-- Compatible completed coefficients, acting on sheaf morphisms. -/
abbrev normalizedDVRScalars := RingCat.sectionsSubring
  ((completedIntegralCommRingSheafUnrestricted l E X).obj ⋙ forget₂ CommRingCat RingCat)

/-- Commutativity inherited from the completed coefficient sheaf. -/
instance normalizedDVRScalarsCommRing : CommRing (normalizedDVRScalars l E X) :=
  @Subring.toCommRing (∀ U, (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
    _ _

/-- The sectionwise scalar action on completed module sheaves. -/
instance normalizedDVRScalarLinear :
    Linear (normalizedDVRScalars l E X) (completedIntegralModuleSheaves l E X D hl) :=
  SheafOfModules.homLinear (completedIntegralCommRingSheafUnrestricted l E X).obj
    (completedIntegralCoefficientSheafUnrestricted l E X).property

/-- The constant uniformizer viewed as a compatible completed coefficient. -/
def normalizedDVRUniformizer : normalizedDVRScalars l E X :=
  ⟨(PrincipalKoszulStrictReplacement.uniformizer l E X).val,
    (PrincipalKoszulStrictReplacement.uniformizer l E X).property⟩

/-- Canonical composition of finite and completed restrictions. -/
def normalizedDVRFlatRestrictionComp {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E X h ⋙ completedIntegralRestrictScalars l E X D hl m ≅
      completedIntegralRestrictScalars l E X D hl n :=
  normalizedDVRRestrictionCompIso (completedIntegralCoefficientProjection l E X D hl m)
    (normalizedDVRQuotient l E X h) ≪≫
      eqToIso (congrArg (fun f ↦ SheafOfModules.restrictScalars.{max u (t + 1)} f)
        (limit.w (integralCoefficientSheafSystem l E X) (homOfLE h).op))

attribute [local irreducible] normalizedDVRFlatRestrictionComp

local instance instNormalizedDVRFlatCokernel5
    (j : ℕ) : HasDerivedCategory (normalizedDVRModules l E X j) :=
  HasDerivedCategory.standard _

local instance instNormalizedDVRFlatCokernel6 (j : ℕ) :
    (completedIntegralRestrictScalars l E X D hl j).PreservesZeroMorphisms :=
  inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
    (completedIntegralCoefficientProjection l E X D hl j)).PreservesZeroMorphisms

local instance instNormalizedDVRFlatCokernel7 (j : ℕ) :
    (completedIntegralRestrictScalars l E X D hl j).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
    (completedIntegralCoefficientProjection l E X D hl j)).Additive

variable (P : ∀ j : ℕ, CochainComplex (normalizedDVRModules l E X j) ℤ)
  (g : ∀ j : ℕ, P (j + 1) ⟶
    ((normalizedDVRModuleRes l E X j.le_succ).mapHomologicalComplex (.up ℤ)).obj (P j))

/-- Restricted finite representatives, with zero inserted at exponent zero. -/
abbrev normalizedDVRFlatComplex :
    ℕ → CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ
  | 0 => 0
  | j + 1 => ((completedIntegralRestrictScalars l E X D hl j).mapHomologicalComplex
      (.up ℤ)).obj (P j)

/-- Restricted semilinear successor chain maps. -/
def normalizedDVRFlatComplexMap : ∀ j,
    normalizedDVRFlatComplex l E X D hl P (j + 1) ⟶
      normalizedDVRFlatComplex l E X D hl P j
  | 0 => 0
  | j + 1 =>
    ((completedIntegralRestrictScalars l E X D hl (j + 1)).mapHomologicalComplex
      (.up ℤ)).map (g j) ≫
    (Functor.mapHomologicalComplexCompIso
      (normalizedDVRFlatRestrictionComp l E X D hl j.le_succ) (.up ℤ)).hom.app _

/-- The strict completed-coefficient tower of the finite models. -/
def normalizedDVRFlatTower :
    ℕᵒᵖ ⥤ CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ :=
  Functor.ofOpSequence (normalizedDVRFlatComplexMap l E X D hl P g)

private theorem quotient_comp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    normalizedDVRQuotient l E X hrm ≫ normalizedDVRQuotient l E X hmn =
      normalizedDVRQuotient l E X (le_trans hmn hrm) :=
  ((integralCoefficientSheafSystem l E X).map_comp
    (homOfLE hrm).op (homOfLE hmn).op).symm

private def restrictionData :
    SheafRestrictionTowerData.{_, _, _, max u (t + 1)} (integralCoefficientSheaf l E X)
      (completedIntegralCoefficientSheaf l E X D hl) where
  quotient := fun h ↦ normalizedDVRQuotient l E X h
  quotient_comp := quotient_comp l E X
  projection := completedIntegralCoefficientProjection l E X D hl
  projection_comp := fun h ↦
    limit.w (integralCoefficientSheafSystem l E X) (homOfLE h).op
  completedComparison := fun h ↦ normalizedDVRFlatRestrictionComp l E X D hl h
  completedComparison_eq := by
    intro m n h
    unfold normalizedDVRFlatRestrictionComp normalizedDVRRestrictionComp
    rfl

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralCoefficientSheafSystem normalizedDVRQuotient

private def finiteChainComp (n k : ℕ) : P (n + (k + 1)) ⟶
    ((normalizedDVRModuleRes l E X (Nat.le_add_right n (k + 1))).mapHomologicalComplex
      (.up ℤ)).obj (P n) :=
  (restrictionData l E X D hl).finiteMap P g n k

attribute [local irreducible] Functor.mapDerivedCategory

private theorem finiteChainComp_universal
    (T : NormalizedDVRTower l E X D hl)
    (eP : ∀ j : ℕ, DerivedCategory.Q.obj (P j) ≅ T.M j)
    (hrep : ∀ j : ℕ,
      DerivedCategory.Q.map (g j) ≫
        (normalizedDVRModuleRes l E X j.le_succ).mapDerivedCategoryFactors.inv.app (P j) ≫
        (normalizedDVRRes l E X j.le_succ).map (eP j).hom =
      (eP (j + 1)).hom ≫ T.tau j.le_succ)
    (n k : ℕ) : ∀ Z : normalizedDVRDerived l E X n,
    Function.Bijective (fun f : DerivedCategory.Q.obj (P n) ⟶ Z ↦
      (DerivedCategory.Q.map (finiteChainComp l E X D hl P g n k) ≫
        (normalizedDVRModuleRes l E X
          (Nat.le_add_right n (k + 1))).mapDerivedCategoryFactors.inv.app
          (P n)) ≫
        (normalizedDVRRes l E X (Nat.le_add_right n (k + 1))).map f) := by
  have hs (j : ℕ) : ∀ Z : normalizedDVRDerived l E X j,
      Function.Bijective (fun f : DerivedCategory.Q.obj (P j) ⟶ Z ↦
        (DerivedCategory.Q.map (g j) ≫
          (normalizedDVRModuleRes l E X j.le_succ).mapDerivedCategoryFactors.inv.app
            (P j)) ≫ (normalizedDVRRes l E X j.le_succ).map f) := by
    exact universal_iso (normalizedDVRRes l E X j.le_succ)
      (eP (j + 1)) (eP j)
      (DerivedCategory.Q.map (g j) ≫
        (normalizedDVRModuleRes l E X j.le_succ).mapDerivedCategoryFactors.inv.app (P j))
      (T.tau j.le_succ) (by simpa only [Category.assoc] using hrep j)
      (T.normalization j.le_succ)
  let lims (m n : ℕ) (h : n ≤ m) : PreservesFiniteLimits
      (coefficientRes (restrictionData l E X D hl) h) :=
    (normalizedDVRModuleRes_exact l E X h).1
  let colims (m n : ℕ) (h : n ≤ m) : PreservesFiniteColimits
      (coefficientRes (restrictionData l E X D hl) h) :=
    (normalizedDVRModuleRes_exact l E X h).2
  exact coefficientComposite_universal (syst := restrictionData l E X D hl)
    (hlim := lims) (hcolim := colims) (hder := fun _ ↦ HasDerivedCategory.standard _)
    P g hs n k

section TowerCoherence

private theorem flatStep_eq :
    normalizedDVRFlatComplexMap l E X D hl P g = (restrictionData l E X D hl).step P g := by
  rfl

private theorem finiteChainComp_tower (n k : ℕ) :
    (normalizedDVRFlatTower l E X D hl P g).map
      (homOfLE (Nat.succ_le_succ (Nat.le_add_right n (k + 1)))).op =
    ((completedIntegralRestrictScalars l E X D hl (n + (k + 1))).mapHomologicalComplex
      (.up ℤ)).map (finiteChainComp l E X D hl P g n k) ≫
      (Functor.mapHomologicalComplexCompIso
        (normalizedDVRFlatRestrictionComp l E X D hl
          (Nat.le_add_right n (k + 1))) (.up ℤ)).hom.app (P n) := by
  have he := sequence_map_congr (normalizedDVRFlatComplexMap l E X D hl P g)
    ((restrictionData l E X D hl).step P g) (flatStep_eq l E X D hl P g)
    (homOfLE (Nat.succ_le_succ (Nat.le_add_right n (k + 1)))).op
  have ht := (restrictionData l E X D hl).tower_map P g n k
  exact he.trans ht

end TowerCoherence

attribute [local irreducible] finiteChainComp

private theorem zero_cokernel_quasiIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {S : Type*} [CommRing S] [Linear S C]
    (U : ℕᵒᵖ ⥤ CochainComplex C ℤ) (v : S)
    (_hU : ∀ j : ℕ, v ^ j • 𝟙 (U.obj (op j)) = 0)
    (m n : ℕ) (h : n ≤ m)
    (hz : (v ^ n • 𝟙 (U.obj (op m))) ≫ U.map (homOfLE h).op = 0)
    (hn : n = 0 ∨ n = m) (h0 : IsZero (U.obj (op 0))) :
    QuasiIso (cokernel.desc (v ^ n • 𝟙 (U.obj (op m))) (U.map (homOfLE h).op) hz) := by
  rcases hn with rfl | rfl
  · have hf : v ^ 0 • 𝟙 (U.obj (op m)) = 𝟙 _ := by rw [pow_zero, one_smul]
    have hc : IsZero (cokernel (v ^ 0 • 𝟙 (U.obj (op m)))) := by
      rw [hf]
      exact isZero_cokernel_of_epi _
    have : IsIso (cokernel.desc (v ^ 0 • 𝟙 (U.obj (op m)))
        (U.map (homOfLE h).op) hz) := hc.isIso h0 _
    infer_instance
  · let f := cokernel.desc (v ^ n • 𝟙 (U.obj (op n))) (U.map (homOfLE h).op) hz
    have hf : cokernel.π _ ≫ f = 𝟙 _ := by
      rw [cokernel.π_desc]
      exact U.map_id _
    have : IsIso f := ⟨cokernel.π _, by
      apply (cancel_epi (cokernel.π _)).1
      simp only [← Category.assoc, hf, Category.id_comp, Category.comp_id], hf⟩
    infer_instance

/-- Normalization identifies each scalar cokernel with the smaller strict level.
Source: Stacks Tags 03EK, 06YS, 06YY and 05RT; blueprint
lemma-sp-tower-adjunction-foundation--2, strict-model step.
(blueprint: lem-coef-normalized-dvr-flat-cokernel).

Proof: compose the semilinear successor maps to obtain a chain map from P_m to
Res(P_n). The equations hrep transport the successor normalization bijections through
the representative isomorphisms. Universal arrows compose through exact restriction
and its canonical comparison, so the finite chain map is universal for derived
extension to B_n. This calculation is first proved with abstract coefficient maps.
The coefficient quotient B_m -> B_n is surjective and its kernel is generated by
uniformizer^(n+1), by completed-projection divisibility. Tensor its right exact
sequence with each flat term of P_m. The normalized tensor unit then exhibits
termwise extension as the scalar cokernel. Since P_m is K-flat, this extension
computes derived extension. Its universal map and the given transition represent
the same left-adjoint universal arrow, so their comparison is invertible after
localization. Exact restriction preserves this quasi-isomorphism. For equal indices
the scalar vanishes and the transition is identity, so its cokernel descent is an
isomorphism. At exponent zero the scalar is one, its cokernel and the inserted
zero level are zero. These arguments also include zero complexes and empty X. -/
theorem normalizedDVR_flat_cokernel
    (T : NormalizedDVRTower l E X D hl)
    (eP : ∀ j : ℕ, (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj
      (P j) ≅ T.M j)
    (hrep : ∀ j : ℕ,
      DerivedCategory.Q.map (g j) ≫
        (normalizedDVRModuleRes l E X j.le_succ).mapDerivedCategoryFactors.inv.app (P j) ≫
        (normalizedDVRRes l E X j.le_succ).map (eP j).hom =
      (eP (j + 1)).hom ≫ T.tau j.le_succ)
    (hflat : ∀ (j : ℕ) (i : ℤ), exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E X j))
        ((P j).X i)))
    (hkflat : ∀ j : ℕ, CochainComplex.IsKFlatIndependentCoefficients (P j))
    (hzero : ∀ j : ℕ, normalizedDVRUniformizer l E X ^ j •
      𝟙 ((normalizedDVRFlatTower l E X D hl P g).obj (op j)) = 0)
    {m n : ℕ} (h : n ≤ m) :
    QuasiIso (cokernel.desc
      (normalizedDVRUniformizer l E X ^ n •
        𝟙 ((normalizedDVRFlatTower l E X D hl P g).obj (op m)))
      ((normalizedDVRFlatTower l E X D hl P g).map (homOfLE h).op) (by
        rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id
          ((normalizedDVRFlatTower l E X D hl P g).map (homOfLE h).op),
          ← Linear.comp_smul, hzero n, comp_zero])) := by
  have _ := hflat
  by_cases hn : n = 0 ∨ n = m
  · exact zero_cokernel_quasiIso (normalizedDVRFlatTower l E X D hl P g)
      (normalizedDVRUniformizer l E X) hzero m n h _ hn
      (by
        change IsZero (0 : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
        exact isZero_zero _)
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (fun hz ↦ hn (Or.inl hz))
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have hnm : n < m := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hnm)
    have hm : m = n + k + 1 := by omega
    clear hk
    subst m
    simp only [Nat.succ_eq_add_one, Nat.add_assoc] at *
    have hu := finiteChainComp_universal l E X D hl P g T eP hrep n k
    have ht := finiteChainComp_tower l E X D hl P g n k
    change QuasiIso (cokernel.desc
      (normalizedDVRUniformizer l E X ^ (n + 1) •
        𝟙 ((normalizedDVRFlatTower l E X D hl P g).obj (op (n + k + 1 + 1))))
      ((normalizedDVRFlatTower l E X D hl P g).map
        (homOfLE (Nat.succ_le_succ (Nat.le_add_right n (k + 1)))).op) _)
    have hz : (normalizedDVRUniformizer l E X ^ (n + 1) •
        𝟙 ((normalizedDVRFlatTower l E X D hl P g).obj (op (n + k + 1 + 1)))) ≫
      ((normalizedDVRFlatTower l E X D hl P g).map
        (homOfLE (Nat.succ_le_succ (Nat.le_add_right n (k + 1)))).op) = 0 := by
      rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id
        ((normalizedDVRFlatTower l E X D hl P g).map
          (homOfLE (Nat.succ_le_succ (Nat.le_add_right n (k + 1)))).op),
        ← Linear.comp_smul, hzero (n + 1), comp_zero]
    have hq := normalizedDVR_scalar_cokernel_comparison l E X D hl
      (Nat.le_add_right n (k + 1))
      (normalizedDVRFlatRestrictionComp l E X D hl (Nat.le_add_right n (k + 1)))
      (P (n + k + 1)) (P n)
      (finiteChainComp l E X D hl P g n k) (hkflat _) hu (by
        change (normalizedDVRUniformizer l E X ^ (n + 1) •
          𝟙 ((normalizedDVRFlatTower l E X D hl P g).obj (op (n + k + 1 + 1)))) ≫
          (((completedIntegralRestrictScalars l E X D hl (n + k + 1)).mapHomologicalComplex
            (.up ℤ)).map (finiteChainComp l E X D hl P g n k) ≫
            (Functor.mapHomologicalComplexCompIso
              (normalizedDVRFlatRestrictionComp l E X D hl
                (Nat.le_add_right n (k + 1))) (.up ℤ)).hom.app (P n)) = 0
        erw [← ht]
        exact hz)
    convert hq using 1 <;> congr 1

end WeilConjectures
