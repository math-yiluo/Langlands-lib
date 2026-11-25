/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.TensorHomAdjunction
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Native Weil derived tensor and internal Hom under forgetting Frobenius

Source: blueprint main-20261015, prose-10-20, internal-Hom
comparison and transposition of evaluation; native refinement in the DAG proof
(blueprint: def-sf-native-weil-closed-models).

The source is D(ProEtaleWeilSheaf), with constructibility imposed on cohomology.
The data below expose the adjunctions and their representative normalization, so
neither a chosen unrelated comparison nor a cohomology-only comparison suffices.
-/

@[expose] public section

set_option autoImplicit false

universe u a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The ordinary sheaf internal Hom, with precomposition in its source.
Source: Stacks Tag 0A95 and the native comparison proof, step 6
(blueprint: lem-sf-weil-native-closed-forgetful). -/
noncomputable def ordinaryIhomBifunctor (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    (ProEtale.AdicSheaf l Y)ᵒᵖ ⥤ ProEtale.AdicSheaf l Y ⥤ ProEtale.AdicSheaf l Y where
  obj A := ProEtale.AdicSheaf.ihom A.unop
  map f := Mod.ihomMap f.unop
  map_id A := Mod.ihomMap_id A.unop
  map_comp f g := Mod.ihomMap_comp g.unop f.unop

/-- Additivity of ordinary internal Hom in its source.
Source: the product-Hom construction, Stacks Tag 0A95
(blueprint: lem-sf-weil-native-closed-forgetful).
Proof: precomposition by f+g is the sum of precompositions by f and by g;
this is Mod.ihomMap_add, applied to the underlying module morphisms. -/
@[instance] theorem ordinaryIhomBifunctor_additive (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    (ordinaryIhomBifunctor l Y).Additive := by
  constructor
  intro A B f g
  exact Mod.ihomMap_add f.unop g.unop

/-- Additivity of ordinary internal Hom in its target.
Source: the product-Hom construction, Stacks Tag 0A95
(blueprint: lem-sf-weil-native-closed-forgetful).
Proof: postcomposition by f+g is the sum of postcompositions. The sheaf Hom
functor is a right adjoint between additive categories and is additive. -/
@[instance] theorem ordinaryIhomBifunctor_obj_additive (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) (A : (ProEtale.AdicSheaf l Y)ᵒᵖ) :
    ((ordinaryIhomBifunctor l Y).obj A).Additive := by
  exact inferInstanceAs (Mod.ihom A.unop).Additive

/-- The ordinary relative tensor, curried with the right tensor parameter first.
Its data are the existing Mod.tensorLeft and Mod.tensorLeftMap.
Source: Stacks Tag 06YS and native comparison proof, step 5
(blueprint: lem-sf-weil-native-closed-forgetful). -/
noncomputable def ordinaryTensorBifunctor (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    ProEtale.AdicSheaf l Y ⥤ ProEtale.AdicSheaf l Y ⥤ ProEtale.AdicSheaf l Y where
  obj P := Mod.tensorLeft P
  map f := Mod.tensorLeftMap f
  map_id P := Mod.tensorLeftMap_id P
  map_comp f g := Mod.tensorLeftMap_comp f g

/-- Additivity in the first curried tensor parameter.
Source: Stacks Tag 06YS, the underived tensor construction
(blueprint: lem-sf-weil-native-closed-forgetful).
Proof: the relative tensor is the coequalizer of the two module actions. The
induced map for f+g is the sum of the induced maps, by Mod.tensorLeftMap_add. -/
@[instance] theorem ordinaryTensorBifunctor_additive (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) : (ordinaryTensorBifunctor l Y).Additive := by
  constructor
  intro P Q f g
  exact Mod.tensorLeftMap_add f g

/-- Additivity in the second curried tensor parameter.
Source: Stacks Tag 06YS, the underived tensor construction
(blueprint: lem-sf-weil-native-closed-forgetful).
Proof: tensorLeft P is a left adjoint between additive categories, so it is
additive. Equivalently, use the additive coequalizer presentation of tensor. -/
@[instance] theorem ordinaryTensorBifunctor_obj_additive (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) (P : ProEtale.AdicSheaf l Y) :
    ((ordinaryTensorBifunctor l Y).obj P).Additive := by
  exact (Mod.ihomAdjunction P).left_adjoint_additive

/-- The sum-total ordinary relative tensor complex, with its Koszul differential.
Source: Stacks Tag 06YS and native comparison proof, step 5
(blueprint: lem-sf-weil-native-closed-forgetful). -/
noncomputable abbrev ordinaryTensorTotal (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) :=
  CochainComplex.mapBifunctor P Q (ordinaryTensorBifunctor l Y)

/-- The termwise forgetful functor localized at quasi-isomorphisms.
Source: native comparison proof, step 2; Category.lean, WeilComplex.forget
(blueprint: lem-sf-weil-native-closed-forgetful). -/
noncomputable abbrev nativeForget (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :=
  (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory

/-- Biduality is the transpose of evaluation after symmetry, for the specified
closed adjunction. This definition asserts no invertibility.
Source: prose-10-20, evaluation/transposition sentence
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def nativeBidual {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (β : @SymmetricCategory D _ S.monoidal)
    (W K : D) : K ⟶ H.obj (op (H.obj (op K, W)), W) :=
  S.transpose K (H.obj (op K, W)) W
    ((β.toBraidedCategory.braiding K (H.obj (op K, W))).hom ≫ S.evaluation K W)

/-- Product-total representative models, including both-variable naturality.
Source: Stacks Tag 0A95 and native comparison proof, steps 4 and 6
(blueprint: lem-sf-weil-native-closed-forgetful). -/
structure NativeHomRepresentatives
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    [HasDerivedCategory.{b} A] (H₀ : Aᵒᵖ ⥤ A ⥤ A)
    [H₀.Additive] [∀ P, (H₀.obj P).Additive]
    (H : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A) where
  /-- Identification for every source and every K-injective target. -/
  model : ∀ (P I : CochainComplex A ℤ), I.IsKInjective →
    (H.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (CochainComplex.bifunctorHomObj H₀ P I))
  /-- The comparison sends derived maps to precomposition and postcomposition. -/
  naturality : ∀ (P P' I I' : CochainComplex A ℤ)
    (hI : I.IsKInjective) (hI' : I'.IsKInjective) (f : P ⟶ P') (g : I ⟶ I'),
    H.map (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
        (model P I' hI').hom =
      (model P' I hI).hom ≫ DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapLeft (H := H₀) (Y := I) f ≫
          CochainComplex.bifunctorHomMapRight (H := H₀) (K := P) g)

/-- Representative normalization of forgetting internal Hom. The projection
formula fixes the actual product-total comparison. The square then fixes its
localized image, including the canonical localization factorization maps.
Source: native comparison proof, step 6
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeHomRepresentativeCompatibility
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (H₀A : Aᵒᵖ ⥤ A ⥤ A) (H₀B : Bᵒᵖ ⥤ B ⥤ B)
    [H₀A.Additive] [∀ P, (H₀A.obj P).Additive]
    [H₀B.Additive] [∀ P, (H₀B.obj P).Additive]
    (HA : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (HB : (DerivedCategory B)ᵒᵖ × DerivedCategory B ⥤ DerivedCategory B)
    (MA : NativeHomRepresentatives H₀A HA) (MB : NativeHomRepresentatives H₀B HB)
    (U₀ : A ⥤ B) [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
    (η : HA ⋙ U₀.mapDerivedCategory ≅
      U₀.mapDerivedCategory.op.prod U₀.mapDerivedCategory ⋙ HB) : Prop :=
  ∀ (P I : CochainComplex A ℤ) (_hP : P.IsKInjective) (hI : I.IsKInjective),
    ∃ _hUP : CochainComplex.IsKInjective ((U₀.mapHomologicalComplex (.up ℤ)).obj P),
    ∃ hUI : CochainComplex.IsKInjective ((U₀.mapHomologicalComplex (.up ℤ)).obj I),
    ∃ χ : (U₀.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.bifunctorHomObj H₀A P I) ≅
        CochainComplex.bifunctorHomObj H₀B
          ((U₀.mapHomologicalComplex (.up ℤ)).obj P)
          ((U₀.mapHomologicalComplex (.up ℤ)).obj I),
      (∀ (n p q : ℤ) (hpq : p + n = q),
        HEq (χ.hom.f n ≫ CochainComplex.bifunctorHomπ H₀B
            ((U₀.mapHomologicalComplex (.up ℤ)).obj P)
            ((U₀.mapHomologicalComplex (.up ℤ)).obj I) n p q hpq)
          (U₀.map (CochainComplex.bifunctorHomπ H₀A P I n p q hpq))) ∧
      (η.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I)).hom ≫
          HB.map (Prod.mkHom (U₀.mapDerivedCategoryFactors.inv.app P).op
            (U₀.mapDerivedCategoryFactors.hom.app I)) ≫
          (MB.model _ _ hUI).hom =
        U₀.mapDerivedCategory.map (MA.model P I hI).hom ≫
          U₀.mapDerivedCategoryFactors.hom.app
            (CochainComplex.bifunctorHomObj H₀A P I) ≫ DerivedCategory.Q.map χ.hom

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The two-variable derived internal Hom, with its actual product-total models.
The source restriction is the recorded native derivedHom, as a functor, and the
ordinary restriction is derived from the ordinary module-sheaf internal Hom.
Source: native comparison proof, steps 4 and 6; Stacks Tag 0A95
(blueprint: lem-sf-weil-native-closed-forgetful). -/
structure NativeClosedHomModels where
  /-- The native derived internal Hom bifunctor. -/
  weilHom : (DerivedCategory (ProEtaleWeilSheaf k₀ l X))ᵒᵖ ×
    DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤
      DerivedCategory (ProEtaleWeilSheaf k₀ l X)
  /-- The ordinary derived sheaf internal Hom bifunctor. -/
  ordinaryHom :
    (DerivedCategory (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))ᵒᵖ ×
    DerivedCategory (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⥤
    DerivedCategory (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  /-- The native functor agrees with the actual upstream construction. -/
  nativeModel : ∀ L, Prod.sectL _ L ⋙ weilHom ≅ derivedHom k₀ l X L
  /-- The ordinary internal Hom is computed by the same two-resolution recipe. -/
  ordinaryModel : ∀ L, Prod.sectL _ L ⋙ ordinaryHom ≅
    DerivedCategory.bifunctorRHom
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) L
  /-- The native derived Hom is product-total Hom into K-injectives. -/
  weilRepresentatives : NativeHomRepresentatives (ihomBifunctor k₀ l X) weilHom
  /-- The ordinary derived Hom has the ordinary product-total representative model. -/
  ordinaryRepresentatives : NativeHomRepresentatives
    (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ordinaryHom

/-- The comparison obtained by uncurrying mapped evaluation, followed by the
ordinary adjunction. Its arrow is specified, rather than chosen among isomorphisms.
Source: native comparison proof, step 7; Stacks Tags 08J9 and 0A97
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def nativeHomComparison {C : Type a} [Category.{b} C]
    {D : Type a} [Category.{b} D] {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (U : C ⥤ D) (τ : SC.tensor ⋙ U ≅ U.prod U ⋙ SD.tensor) (K L : C) :
    U.obj (HC.obj (op K, L)) ⟶ HD.obj (op (U.obj K), U.obj L) :=
  SD.transpose _ (U.obj K) (U.obj L)
    ((τ.app (HC.obj (op K, L), K)).inv ≫ U.map (SC.evaluation K L))

/-- Preservation of the two symmetries by the tensor comparison.
Source: native comparison proof, step 5
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeSymmetryCompatibility {C : Type a} [Category.{b} C]
    {D : Type a} [Category.{b} D] {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (βC : @SymmetricCategory C _ SC.monoidal)
    (βD : @SymmetricCategory D _ SD.monoidal)
    (U : C ⥤ D) (τ : SC.tensor ⋙ U ≅ U.prod U ⋙ SD.tensor) : Prop :=
  ∀ K L, U.map (βC.toBraidedCategory.braiding K L).hom ≫ (τ.app (L, K)).hom =
    (τ.app (K, L)).hom ≫ (βD.toBraidedCategory.braiding (U.obj K) (U.obj L)).hom

/-- Associativity and unit coherence for the derived tensor comparison.
Source: the canonical derived tensor comparison in native proof step 5
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeTensorCoherence {C : Type a} [Category.{b} C]
    {D : Type a} [Category.{b} D] {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (U : C ⥤ D) (τ : SC.tensor ⋙ U ≅ U.prod U ⋙ SD.tensor)
    (ε : U.obj SC.monoidal.tensorUnit ≅ SD.monoidal.tensorUnit) : Prop :=
  (∀ K L M,
    U.map (SC.monoidal.associator K L M).hom ≫
        (τ.app (K, SC.tensor.obj (L, M))).hom ≫
        SD.tensor.map (Prod.mkHom (𝟙 (U.obj K)) (τ.app (L, M)).hom) =
      (τ.app (SC.tensor.obj (K, L), M)).hom ≫
        SD.tensor.map (Prod.mkHom (τ.app (K, L)).hom (𝟙 (U.obj M))) ≫
        (SD.monoidal.associator (U.obj K) (U.obj L) (U.obj M)).hom) ∧
  (∀ K, U.map (SC.monoidal.leftUnitor K).hom =
    (τ.app (SC.monoidal.tensorUnit, K)).hom ≫
      SD.tensor.map (Prod.mkHom ε.hom (𝟙 (U.obj K))) ≫
      (SD.monoidal.leftUnitor (U.obj K)).hom) ∧
  (∀ K, U.map (SC.monoidal.rightUnitor K).hom =
    (τ.app (K, SC.monoidal.tensorUnit)).hom ≫
      SD.tensor.map (Prod.mkHom (𝟙 (U.obj K)) ε.hom) ≫
      (SD.monoidal.rightUnitor (U.obj K)).hom)

/-- The evaluation square for a specified closed comparison.
Source: native comparison proof, step 7
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeEvaluationCompatibility {C : Type a} [Category.{b} C]
    {D : Type a} [Category.{b} D] {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (U : C ⥤ D) (τ : SC.tensor ⋙ U ≅ U.prod U ⋙ SD.tensor)
    (η : HC ⋙ U ≅ U.op.prod U ⋙ HD) : Prop :=
  ∀ K L, U.map (SC.evaluation K L) =
    (τ.app (HC.obj (op K, L), K)).hom ≫
      SD.tensor.map (Prod.mkHom (η.app (op K, L)).hom (𝟙 (U.obj K))) ≫
      SD.evaluation (U.obj K) (U.obj L)

/-- Naturality of the transpose of evaluation after symmetry.
Source: native comparison proof, step 8
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeBidualNaturality {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (β : @SymmetricCategory D _ S.monoidal) : Prop :=
  ∀ (W K K' : D) (f : K ⟶ K'), f ≫ nativeBidual S β W K' =
    nativeBidual S β W K ≫ H.map
      (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 W))).op (𝟙 W))

/-- The actual equality of the two transposed evaluations under forgetting.
Source: native comparison proof, step 8
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeBidualCompatibility {C : Type a} [Category.{b} C]
    {D : Type a} [Category.{b} D] {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (βC : @SymmetricCategory C _ SC.monoidal)
    (βD : @SymmetricCategory D _ SD.monoidal) (U : C ⥤ D)
    (η : HC ⋙ U ≅ U.op.prod U ⋙ HD) : Prop :=
  ∀ W K, U.map (nativeBidual SC βC W K) ≫
    (η.app (op (HC.obj (op K, W)), W)).hom ≫
      HD.map (Prod.mkHom (η.app (op K, W)).inv.op (𝟙 (U.obj W))) =
    nativeBidual SD βD (U.obj W) (U.obj K)

/-- K-flatness for the actual ordinary total relative tensor.
Source: Stacks Tag 06YS (blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeOrdinaryKFlat (Y : Scheme.{u})
    (P : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) : Prop :=
  ∀ N : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
    N.Acyclic → (ordinaryTensorTotal l Y P N).Acyclic

/-- The signed exchange on the actual ordinary total relative tensor.
Source: Stacks Tag 06YS, Koszul symmetry on bidegrees
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeOrdinarySignedSwap (Y : Scheme.{u})
    (swap : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
      ordinaryTensorTotal l Y P Q ≅ ordinaryTensorTotal l Y Q P) : Prop :=
  ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
    (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
    Mod.tensorπ (Q.X q) (P.X p) ≫
        (HomologicalComplex.ιMapBifunctor P Q (ordinaryTensorBifunctor l Y)
          (.up ℤ) p q n hpq).hom ≫ ((swap P Q).hom.f n).hom =
      (p * q).negOnePow •
        ((β_ (Q.X q).X (P.X p).X).hom ≫ Mod.tensorπ (P.X p) (Q.X q) ≫
          (HomologicalComplex.ιMapBifunctor Q P (ordinaryTensorBifunctor l Y)
            (.up ℤ) q p n hqp).hom)

/-- Componentwise uncurrying fixes the adjunction, not just its right adjoint.
The native Hom differential has the row sign (-1)^p. The total orders the
curried parameter P first and has differential d_P + (-1)^p d_Q, so the
componentwise uncurry is unsigned. The Koszul sign belongs to the signed swap.
Source: Stacks Tags 08J9 and 0A97, native comparison proof, step 7
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeAdjunctionNormalization
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasCountableCoproducts A] [HasDerivedCategory.{b} A]
    (H₀ : Aᵒᵖ ⥤ A ⥤ A) [H₀.Additive] [∀ P, (H₀.obj P).Additive]
    (T : A ⥤ A ⥤ A) [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : ∀ P, T.obj P ⊣ H₀.obj (op P))
    (H : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (R : NativeHomRepresentatives H₀ H) (S : CoefficientClosedStructure H)
    (flat : CochainComplex A ℤ → Prop)
    (model : ∀ P Q : CochainComplex A ℤ, flat P →
      (S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor P Q T))) : Prop :=
  ∀ (P Q I : CochainComplex A ℤ) (hP : flat P) (_hQ : flat Q)
    (hI : I.IsKInjective) (φ : Q ⟶ CochainComplex.bifunctorHomObj H₀ P I),
    ∃ ψ : CochainComplex.mapBifunctor P Q T ⟶ I,
      (∀ (p q n : ℤ) (hpq : p + q = n),
        HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n hpq ≫ ψ.f n =
          (T.obj (P.X p)).map (φ.f q ≫
              CochainComplex.bifunctorHomπ H₀ P I q p n hpq) ≫
            (adj (P.X p)).counit.app (I.X n)) ∧
      (model P Q hP).hom ≫ DerivedCategory.Q.map ψ =
        (S.transpose (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj I)).symm
            (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv)

/-- The ordinary derived tensor and symmetry on total K-flat representatives.
The reversed order reflects Mod.tensorLeft: its value at (P,Q) is Q tensor P.
The final clause fixes the model to the canonical localization tensorator, using
its signed balanced-tensor comparison on every summand. It rules out arbitrary
symmetric rescalings of the model relative to the fixed monoidal structure.
Source: Stacks Tag 06YS and native comparison proof, step 5
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeOrdinaryTensorModels (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤ DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H) (β : @SymmetricCategory _ _ S.monoidal) : Prop :=
  ∃ model : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
    NativeOrdinaryKFlat l Y P →
      (S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q)),
  ∃ swap : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
    ordinaryTensorTotal l Y P Q ≅ ordinaryTensorTotal l Y Q P,
    NativeAdjunctionNormalization (ordinaryIhomBifunctor l Y)
      (ordinaryTensorBifunctor l Y) (fun P ↦ Mod.ihomAdjunction P)
      H R S (NativeOrdinaryKFlat l Y) model ∧
    NativeOrdinarySignedSwap l Y swap ∧
    (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P) (hQ : NativeOrdinaryKFlat l Y Q),
      (β.toBraidedCategory.braiding (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj P)).hom ≫ (model Q P hQ).hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map (swap P Q).hom) ∧
    (∃ κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
        ordinaryTensorTotal l Y P Q ≅ Q ⊗ P,
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
        Mod.tensorπ (Q.X q) (P.X p) ≫
            (HomologicalComplex.ιMapBifunctor P Q (ordinaryTensorBifunctor l Y)
              (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
          (p * q).negOnePow •
            (Mod.tensorObjπ (Q.X q) (P.X p) ≫
              (HomologicalComplex.ιTensorObj Q P q p n hqp).hom)) ∧
      ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P) (_hQ : NativeOrdinaryKFlat l Y Q),
        HEq (model P Q hP).hom
          (Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
            DerivedCategory.Q.map (κ P Q).inv))

/-- Closed structures on the specified native and ordinary Hom models, and
natural derived comparisons. Their compatibility assertions are stated separately
to avoid duplicating large dependent categorical types in structure constructors.
Source: native comparison proof, steps 4--8
(blueprint: lem-sf-weil-native-closed-forgetful). -/
structure NativeClosedComparison where
  /-- Internal Hom has the specified native and ordinary two-resolution models. -/
  homModels : NativeClosedHomModels k₀ l X
  /-- Tensor is the left adjoint of the specified native internal Hom. -/
  weilClosed : CoefficientClosedStructure homModels.weilHom
  /-- The ordinary derived module tensor--Hom adjunction. -/
  ordinaryClosed : CoefficientClosedStructure homModels.ordinaryHom
  /-- The native tensor unit is the coefficient module in degree zero. -/
  weilUnit : weilClosed.monoidal.tensorUnit ≅
    (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X)
  /-- The ordinary tensor unit is the coefficient module in degree zero. -/
  ordinaryUnit : ordinaryClosed.monoidal.tensorUnit ≅
    (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  /-- The native tensor is symmetric. -/
  weilSymmetry : @SymmetricCategory _ _ weilClosed.monoidal
  /-- The ordinary tensor has its usual symmetry. -/
  ordinarySymmetry : @SymmetricCategory _ _ ordinaryClosed.monoidal
  /-- The ordinary tensor and symmetry have their total-complex normalization. -/
  ordinaryTensorModels : NativeOrdinaryTensorModels l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber homModels.ordinaryHom
    homModels.ordinaryRepresentatives ordinaryClosed ordinarySymmetry
  /-- The derived tensor comparison, natural in both arguments. -/
  tensorComparison : weilClosed.tensor ⋙ nativeForget k₀ l X ≅
    (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ ordinaryClosed.tensor
  /-- The invertible derived internal Hom comparison, natural in both arguments. -/
  homComparison : homModels.weilHom ⋙ nativeForget k₀ l X ≅
    (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ homModels.ordinaryHom

/-- The unit comparison induced by forgetting the actual coefficient Weil sheaf.
Source: native comparison proof, steps 1 and 5
(blueprint: lem-sf-weil-native-closed-forgetful). -/
noncomputable def NativeClosedComparison.unitComparison
    (C : NativeClosedComparison k₀ l X) :
    (nativeForget k₀ l X).obj C.weilClosed.monoidal.tensorUnit ≅
      C.ordinaryClosed.monoidal.tensorUnit :=
  (nativeForget k₀ l X).mapIso C.weilUnit ≪≫
    (Functor.mapDerivedCategorySingleFunctor
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
        (adicConstant k₀ l X) ≪≫ C.ordinaryUnit.symm

/-- The comparisons preserve the fixed adjunction, symmetry, evaluation and
biduality; the Hom arrow is the specified transpose of mapped evaluation.
Source: native comparison proof, steps 5--8
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def NativeClosedComparison.Compatible (C : NativeClosedComparison k₀ l X) : Prop :=
  (∀ K L, (C.homComparison.app (op K, L)).hom =
    nativeHomComparison C.weilClosed C.ordinaryClosed (nativeForget k₀ l X)
      C.tensorComparison K L) ∧
  NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
    (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    C.homModels.weilHom C.homModels.ordinaryHom C.homModels.weilRepresentatives
    C.homModels.ordinaryRepresentatives
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
    C.homComparison ∧
  NativeTensorCoherence C.weilClosed C.ordinaryClosed (nativeForget k₀ l X)
    C.tensorComparison C.unitComparison ∧
  NativeSymmetryCompatibility C.weilClosed C.ordinaryClosed C.weilSymmetry
    C.ordinarySymmetry (nativeForget k₀ l X) C.tensorComparison ∧
  NativeEvaluationCompatibility C.weilClosed C.ordinaryClosed (nativeForget k₀ l X)
    C.tensorComparison C.homComparison ∧
  NativeBidualNaturality C.weilClosed C.weilSymmetry ∧
  NativeBidualCompatibility C.weilClosed C.ordinaryClosed C.weilSymmetry
    C.ordinarySymmetry (nativeForget k₀ l X) C.homComparison

end AlgebraicGeometry.ProEtaleWeilSheaf
