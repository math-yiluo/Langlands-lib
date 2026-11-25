/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
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
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.SixFunctors.Integral.IntegralQuotientCompletionExact
import WeilConjectures.SixFunctors.Completed.CompletedCoefficientUnitComplete
import WeilConjectures.CategoryTheory.DerivedCategory.FlatDevissage
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-! # Canonical completeness of bounded projective sheaf tensors

Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50; Definition 3.4.10 and Proposition 3.5.1;
Stacks Project, Tags 099M and 0941
(blueprint: lem-fix-bounded-projective-tensor-complete).

The completion and its quotient augmentation are the existing global-site specialization
of `IntegralOnSlice`. Finite products of the coefficient unit are finite sums in this
abelian category. All splittings are morphisms of module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.IntegralOnSlice.abSheafify
  WeilConjectures.IntegralOnSlice.abLocallyBijective
universe t u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace WeilConjectures
open IntegralOnSlice SheafOfModules

section FiniteRetracts

universe a v r w
variable {A : Type a} [Category.{v} A] [Abelian A]
attribute [local instance] Abelian.hasFiniteBiproducts

private theorem finiteRetract_complete [HasDerivedCategory.{w} A]
    (F : DerivedCategory.{w} A ⥤ DerivedCategory.{w} A) [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated] (η : 𝟭 _ ⟶ F) [NatTrans.CommShift η ℤ]
    (B : A) (hB : IsIso (η.app ((DerivedCategory.singleFunctor A 0).obj B)))
    (P : CochainComplex A ℤ)
    (hb : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k))
    (hP : ∀ k : ℤ, ∃ n : ℕ, ∃ i : P.X k ⟶ ∏ᶜ (fun _ : Fin n ↦ B),
      ∃ p : (∏ᶜ (fun _ : Fin n ↦ B)) ⟶ P.X k, i ≫ p = 𝟙 _) :
    IsIso (η.app (DerivedCategory.Q.obj P)) := by
  let S := DerivedCategory.singleFunctor A 0
  have hfree (n : ℕ) : IsIso (η.app (S.obj (∏ᶜ (fun _ : Fin n ↦ B)))) := by
    have h : η.isoLocus (∏ᶜ fun _ : Fin n ↦ S.obj B) :=
      ObjectProperty.prop_product η.isoLocus (fun _ ↦ hB)
    exact (NatTrans.isIso_app_iff_of_iso η (PreservesProduct.iso S _)).2 h
  have hterm (M : A) (n : ℕ) (i : M ⟶ ∏ᶜ (fun _ : Fin n ↦ B))
      (p : (∏ᶜ (fun _ : Fin n ↦ B)) ⟶ M) (hip : i ≫ p = 𝟙 _) :
      IsIso (η.app (S.obj M)) := by
    have := hfree n
    exact η.isIso_app_of_retract
      ⟨S.map i, S.map p, by rw [← S.map_comp, hip, S.map_id]⟩
  obtain ⟨a, b, hb⟩ := hb
  have : P.IsStrictlyGE a := (P.isStrictlyGE_iff a).2 (fun k hk ↦ hb k (.inl hk))
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 (fun k hk ↦ hb k (.inr hk))
  apply DerivedCategory.isIso_app_Q_obj_of_isStrictlyGE_of_isStrictlyLE_of_prop η
    (fun M ↦ ∃ n : ℕ, ∃ i : M ⟶ ∏ᶜ (fun _ : Fin n ↦ B),
      ∃ p : (∏ᶜ (fun _ : Fin n ↦ B)) ⟶ M, i ≫ p = 𝟙 _) ?_ P a b hP
  rintro M ⟨n, i, p, hip⟩
  exact hterm M n i p hip

private theorem finiteRetract_sum (B : A) {I : Type} [Finite I] (F : I → A)
    (hF : ∀ x, ∃ n : ℕ, ∃ i : F x ⟶ ∏ᶜ (fun _ : Fin n ↦ B),
      ∃ p : (∏ᶜ (fun _ : Fin n ↦ B)) ⟶ F x, i ≫ p = 𝟙 _) :
    ∃ n : ℕ, ∃ i : (⨁ F) ⟶ ∏ᶜ (fun _ : Fin n ↦ B),
      ∃ p : (∏ᶜ (fun _ : Fin n ↦ B)) ⟶ (⨁ F), i ≫ p = 𝟙 _ := by
  classical
  let := Fintype.ofFinite I
  choose n i p hip using hF
  let e : (⨁ fun x ↦ ∏ᶜ (fun _ : Fin (n x) ↦ B)) ≅
      ∏ᶜ (fun _ : Fin (Fintype.card (Σ x, Fin (n x))) ↦ B) :=
    biproduct.mapIso (fun x ↦ (biproduct.isoProduct _).symm) ≪≫
      biproductBiproductIso (fun x ↦ Fin (n x)) (fun _ _ ↦ B) ≪≫
      biproduct.whiskerEquiv (Fintype.equivFin (Σ x, Fin (n x))) (fun _ ↦ Iso.refl B) ≪≫
      biproduct.isoProduct _
  refine ⟨_, biproduct.map i ≫ e.hom, e.inv ≫ biproduct.map p, ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  ext x
  simp [hip]

private theorem finiteRetract_tensor [MonoidalCategory A] [MonoidalPreadditive A]
    (M N : A)
    (hM : ∃ n : ℕ, ∃ i : M ⟶ ∏ᶜ (fun _ : Fin n ↦ 𝟙_ A),
      ∃ p : (∏ᶜ (fun _ : Fin n ↦ 𝟙_ A)) ⟶ M, i ≫ p = 𝟙 _)
    (hN : ∃ n : ℕ, ∃ i : N ⟶ ∏ᶜ (fun _ : Fin n ↦ 𝟙_ A),
      ∃ p : (∏ᶜ (fun _ : Fin n ↦ 𝟙_ A)) ⟶ N, i ≫ p = 𝟙 _) :
    ∃ n : ℕ, ∃ i : M ⊗ N ⟶ ∏ᶜ (fun _ : Fin n ↦ 𝟙_ A),
      ∃ p : (∏ᶜ (fun _ : Fin n ↦ 𝟙_ A)) ⟶ M ⊗ N, i ≫ p = 𝟙 _ := by
  classical
  obtain ⟨r, iM, pM, hiM⟩ := hM
  obtain ⟨s, iN, pN, hiN⟩ := hN
  let B := 𝟙_ A
  let e : (∏ᶜ (fun _ : Fin r ↦ B)) ⊗ (∏ᶜ (fun _ : Fin s ↦ B)) ≅
      ⨁ (fun _ : Fin r ↦ ∏ᶜ (fun _ : Fin s ↦ B)) :=
    ((biproduct.isoProduct _).symm ⊗ᵢ Iso.refl _) ≪≫
      (MonoidalCategory.tensorRight _).mapBiproduct _ ≪≫
      biproduct.mapIso (fun _ ↦ MonoidalCategory.leftUnitor _)
  obtain ⟨n, i, p, hip⟩ := finiteRetract_sum B
    (fun _ : Fin r ↦ ∏ᶜ (fun _ : Fin s ↦ B))
    (fun _ ↦ ⟨s, 𝟙 _, 𝟙 _, Category.id_comp _⟩)
  refine ⟨n, (iM ⊗ₘ iN) ≫ e.hom ≫ i, p ≫ e.inv ≫ (pM ⊗ₘ pN), ?_⟩
  simp only [Category.assoc]
  rw [← Category.assoc i p, hip, Category.id_comp, Iso.hom_inv_id_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom, hiM, hiN,
    MonoidalCategory.id_tensorHom_id]

private theorem finiteRetract_total [MonoidalCategory A] [MonoidalPreadditive A]
    (P Q : CochainComplex A ℤ) [HomologicalComplex.HasTensor P Q]
    (a b : ℤ) (hb : ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k))
    (hP : ∀ k : ℤ, ∃ n : ℕ, ∃ i : P.X k ⟶ ∏ᶜ (fun _ : Fin n ↦ 𝟙_ A),
      ∃ p : (∏ᶜ (fun _ : Fin n ↦ 𝟙_ A)) ⟶ P.X k, i ≫ p = 𝟙 _)
    (hQ : ∀ k : ℤ, ∃ n : ℕ, ∃ i : Q.X k ⟶ ∏ᶜ (fun _ : Fin n ↦ 𝟙_ A),
      ∃ p : (∏ᶜ (fun _ : Fin n ↦ 𝟙_ A)) ⟶ Q.X k, i ≫ p = 𝟙 _) (k : ℤ) :
    ∃ n : ℕ, ∃ i : (HomologicalComplex.tensorObj P Q).X k ⟶
        ∏ᶜ (fun _ : Fin n ↦ 𝟙_ A),
      ∃ p : (∏ᶜ (fun _ : Fin n ↦ 𝟙_ A)) ⟶ (HomologicalComplex.tensorObj P Q).X k,
        i ≫ p = 𝟙 _ := by
  classical
  let I := {pq : ℤ × ℤ // pq.1 + pq.2 = k ∧ pq.1 ∈ Finset.Icc a b}
  have : Finite I := Finite.of_injective
    (fun j : I ↦ (⟨j.1.1, j.2.2⟩ : ↥(Finset.Icc a b))) (by
      intro j j' h
      apply Subtype.ext
      have hp : j.1.1 = j'.1.1 := congrArg Subtype.val h
      apply Prod.ext hp
      have hj := j.2.1
      have hj' := j'.2.1
      omega)
  let F : I → A := fun j ↦ P.X j.1.1 ⊗ Q.X j.1.2
  obtain ⟨n, i, p, hip⟩ := finiteRetract_sum (𝟙_ A) F
    (fun j ↦ finiteRetract_tensor _ _ (hP j.1.1) (hQ j.1.2))
  let back : (⨁ F) ⟶ (HomologicalComplex.tensorObj P Q).X k :=
    biproduct.desc (fun j ↦ HomologicalComplex.ιMapBifunctor P Q (curriedTensor A)
      (.up ℤ) j.1.1 j.1.2 k j.2.1)
  let forth : (HomologicalComplex.tensorObj P Q).X k ⟶ (⨁ F) :=
    HomologicalComplex.mapBifunctorDesc
      (K₁ := P) (K₂ := Q) (F := curriedTensor A) (c := .up ℤ)
      (fun p q h ↦ if hp : p ∈ Finset.Icc a b then
        biproduct.ι F ⟨(p, q), h, hp⟩ else 0)
  have hfb : forth ≫ back = 𝟙 _ := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    dsimp only [forth, back]
    rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    by_cases hp : p ∈ Finset.Icc a b
    · simp only [dite_eq_left hp, biproduct.ι_desc, Category.comp_id]
    · rw [dite_eq_right hp, zero_comp]
      have hz : IsZero (P.X p ⊗ Q.X q) :=
        (tensorRight (Q.X q)).map_isZero (hb p (by
          simp only [Finset.mem_Icc, not_and_or, not_le] at hp
          exact hp))
      exact hz.eq_of_src _ _
  refine ⟨n, forth ≫ i, p ≫ back, ?_⟩
  simp only [Category.assoc, ← Category.assoc i p, hip, Category.id_comp, hfb]

end FiniteRetracts

section FlatRetracts

universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

private theorem finiteRetract_flat
    (M : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (n : ℕ) (i : M ⟶ ∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (p : (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⟶ M)
    (hip : i ≫ p = 𝟙 M) : IsFlatOnSite (J := J) (R := R) M := by
  let := isMonoidal_W_independentCoefficients R
  have : HasCountableCoproducts (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) := by
    have := isGrothendieckAbelian_coefficientUniverse
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
    have : HasColimitsOfSize.{r, r} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
      IsGrothendieckAbelian.hasColimits _
    have : HasColimitsOfSize.{0, 0} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
      hasColimitsOfSizeShrink.{0, 0, r, r} _
    exact ⟨fun J _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete J)⟩
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  have (M : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft M)
  have (M : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have hunit : ObjectProperty.flat
      (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
    ObjectProperty.prop_unit ObjectProperty.flat
  have hfree : ObjectProperty.flat (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
    ObjectProperty.prop_of_isLimit _ (limit.isLimit _) (fun _ ↦ hunit)
  have hM := ObjectProperty.prop_of_retract ObjectProperty.flat
    (show Retract M (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) from
        ⟨i, p, hip⟩) hfree
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M).symm hM.2

end FlatRetracts

/-- The canonical derived quotient completion fixes bounded complexes of finite-free
sheaf retracts and their ordinary total tensor, including its derived representative.
Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50; Stacks, Tags 099M, 0941 and 06YQ
(blueprint: lem-fix-bounded-projective-tensor-complete).

Proof:
1. Tensor the specified inclusions and retractions with any module sheaf. The resulting
   functor is a retract of a finite sum of identities, so is exact. Tensoring two
   splittings gives a splitting off rank r*s; finite sums of these splittings give the
   total tensor's splittings. Support intervals [a,b] and [c,d] add to [a+c,b+d]. The
   Koszul signs make the square of the total differential zero. This uses
   lem-weil-pbc-independent-sheaf-tensor-colimits and def-pc-flat-sheaf-modules.
2. Apply lem-weil-pbc-independent-bounded-flat-kflat to P, Q and their total tensor.
   The representative comparison of lem-weil-pbc-site-derived-tensor-descent identifies
   the latter with the ordinary derived tensor.
3. Before deriving, termwise quotient tensor and restriction preserve homotopies,
   shifts and cones. Use lem-pc-tensor-mapping-cone-iso and lem-pe-roos-cone-calculus.
   On Roos coordinates a degree -1 homotopy h acts as (hv,-hu), which verifies the
   homotopy identity against d(v,u)=(dv,-du-(1-s)v).
4. Resolve by lem-pc-kflat-resolution. Quotient tensor inverts good quasi-isomorphisms
   by lem-pur-derived-change-of-rings, and Roos does so by lem-pe-roos-cone-calculus.
   Apply lem-pur-left-derived-from-kflat-class: the descended completion is additive
   and triangulated. Lem-pe-kflat-scalar-tower-realization identifies its entire strict
   tower, including the quotient maps. Descend the augmentation (quotients,0) using
   lem-weil-pbc-localization-universal-property.
5. The signed cone and shift comparisons preserve this augmentation. Every derived
   triangle comes from a good cone triangle: use lem-pc-right-fraction-representation,
   resolve the roof's middle term, and use lem-pc-tensor-mapping-cone-iso and
   lem-pur-quasi-iso-cone-acyclic for closure of good complexes under cones. Hence the
   unit commutes with shifts and gives triangle morphisms; lem-sf-triangle-morphism-iso
   gives two-out-of-three for its invertibility.
6. For the unit in degree zero, the actual quotient maps are the ordinary limit cone
   by lem-sf-completed-free-cell-ordinary-limit, rank one and degree zero. Its auxiliary
   finite-field datum may have any characteristic different from l, with no condition
   on T. Lem-weil-proetale-surjective-tower-derived-limit identifies its kernel inclusion
   with the mapping-fibre augmentation (quotients,0). This proves invertibility at the
   coefficient unit. Additivity and shifts give the same for finite sums in any degree.
7. Naturality passes invertibility to a retract: for i:F -> B^r and p:B^r -> F, an
   inverse is C(i) followed by the inverse free unit and p. Both composites are identities
   by naturality and i followed by p = identity.
8. Descend through the brutal truncations of a bounded complex. The degreewise split
   sequence from truncation at m+1 to truncation at m to P^m[-m] gives a triangle by
   lem-weil-pbc-complex-ses-triangle. Start above the upper bound and use step 5 and
   step 7 at each degree. Apply this to P and to the bounded total tensor of step 1.
   Zero ranks, the zero complex and arbitrary sheaf-linear differentials are included. -/
theorem bounded_projective_tensor_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : AlgebraicGeometry.Scheme.{t}) [CompactSpace T] [QuasiSeparatedSpace T]
    (_hl : ∀ x : T, IsUnit (l : T.residueField x)) :
    (completion l E T none).Additive ∧
    (∃ (_ : (completion l E T none).CommShift ℤ),
      (completion l E T none).IsTriangulated ∧ NatTrans.CommShift (completionUnit l E T none) ℤ) ∧
    IsIso ((completionUnit l E T none).app
      ((DerivedCategory.singleFunctor (Mod l E T none) 0).obj
        (SheafOfModules.unit (rings l E T none)))) ∧
    ∀ P : Cx l E T none,
      (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k)) →
      (∀ k : ℤ, ∃ r : ℕ,
        ∃ i : P.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit (rings l E T none)),
        ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit (rings l E T none))) ⟶ P.X k,
          i ≫ p = 𝟙 (P.X k)) →
      (∀ k : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (J := topology T none) (R := ring l E T none) (P.X k)) ∧
      CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
        (R := ring l E T none) P ∧
      IsIso ((completionUnit l E T none).app (DerivedCategory.Q.obj P)) ∧
      ∀ Q : Cx l E T none,
        (∃ c d : ℤ, ∀ k : ℤ, k < c ∨ d < k → IsZero (Q.X k)) →
        (∀ k : ℤ, ∃ r : ℕ,
          ∃ i : Q.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit (rings l E T none)),
          ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit (rings l E T none))) ⟶ Q.X k,
            i ≫ p = 𝟙 (Q.X k)) →
        ∀ V : Cx l E T none,
          V = (coefficientTotalTensor.{u, t + 1, t}
            (topology T none) (ring l E T none)).obj (P, Q) →
          (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (V.X k)) ∧
          (∀ k : ℤ, ∃ r : ℕ,
            ∃ i : V.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit (rings l E T none)),
            ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit (rings l E T none))) ⟶ V.X k,
              i ≫ p = 𝟙 (V.X k)) ∧
          (∀ k : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
            (J := topology T none) (R := ring l E T none) (V.X k)) ∧
          CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
            (R := ring l E T none) Q ∧
          CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
            (R := ring l E T none) V ∧
          Nonempty (DerivedCategory.Q.obj V ≅
            (siteDerivedTensorIndependentCoefficients.{t + 1, t, max u (t + 1), (max u (t + 1)) + 1}
              (topology T none) (ring l E T none)).obj
                (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ∧
          IsIso ((completionUnit l E T none).app (DerivedCategory.Q.obj V)) := by
  suffices hcore : (completion l E T none).Additive ∧
      (∃ (_ : (completion l E T none).CommShift ℤ),
        (completion l E T none).IsTriangulated ∧
          NatTrans.CommShift (completionUnit l E T none) ℤ) ∧
      IsIso ((completionUnit l E T none).app
        ((DerivedCategory.singleFunctor (Mod l E T none) 0).obj
          (SheafOfModules.unit (rings l E T none)))) by
    obtain ⟨hadd, ⟨cs, htri, hshift⟩, hunit⟩ := hcore
    let := hadd
    let := cs
    let := htri
    let := hshift
    refine ⟨hadd, ⟨cs, htri, hshift⟩, hunit, ?_⟩
    let : EssentiallySmall.{max u (t + 1)} (Site T none) := essentiallySmallSelf _
    let R := ring l E T none
    let := isMonoidal_W_independentCoefficients R
    let := monoidalCategory R
    let := tensorPreadditive R
    have hflat (P : Cx l E T none)
        (hP : ∀ k : ℤ, ∃ n : ℕ,
          ∃ i : P.X k ⟶ ∏ᶜ (fun _ : Fin n ↦ SheafOfModules.unit (rings l E T none)),
          ∃ p : (∏ᶜ (fun _ : Fin n ↦ SheafOfModules.unit (rings l E T none))) ⟶ P.X k,
            i ≫ p = 𝟙 _) : ∀ k, IsFlatOnSite (J := topology T none) (R := R) (P.X k) := by
      intro k
      obtain ⟨n, i, p, hip⟩ := hP k
      exact finiteRetract_flat R _ n i p hip
    have hkflat (P : Cx l E T none)
        (hb : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k))
        (hf : ∀ k, IsFlatOnSite (J := topology T none) (R := R) (P.X k)) :
        P.IsKFlatIndependentCoefficients (R := R) := by
      obtain ⟨a, b, hb⟩ := hb
      have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 (fun k hk ↦ hb k (.inr hk))
      exact isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P b hf
    intro P hbP hP
    have hfP := hflat P hP
    have hkP := hkflat P hbP hfP
    refine ⟨hfP, hkP, finiteRetract_complete _ _ _ hunit P hbP hP, ?_⟩
    intro Q hbQ hQ V hV
    subst V
    have hfQ := hflat Q hQ
    have hkQ := hkflat Q hbQ hfQ
    obtain ⟨a, b, hb⟩ := hbP
    obtain ⟨c, d, hd⟩ := hbQ
    have : P.IsStrictlyGE a := (P.isStrictlyGE_iff a).2 (fun k hk ↦ hb k (.inl hk))
    have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 (fun k hk ↦ hb k (.inr hk))
    have : Q.IsStrictlyGE c := (Q.isStrictlyGE_iff c).2 (fun k hk ↦ hd k (.inl hk))
    have : Q.IsStrictlyLE d := (Q.isStrictlyLE_iff d).2 (fun k hk ↦ hd k (.inr hk))
    let V := (coefficientTotalTensor.{u, t + 1, t} (topology T none) R).obj (P, Q)
    have hbounds : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (V.X k) := by
      have hge := CochainComplex.isStrictlyGE_tensorObj P Q a c
      have hle := CochainComplex.isStrictlyLE_tensorObj P Q b d
      refine ⟨a + c, b + d, fun k hk ↦ ?_⟩
      rcases hk with hk | hk
      · exact (CochainComplex.isStrictlyGE_iff V (a + c)).1 hge k hk
      · exact (CochainComplex.isStrictlyLE_iff V (b + d)).1 hle k hk
    have hfree : ∀ k : ℤ, ∃ n : ℕ,
        ∃ i : V.X k ⟶ ∏ᶜ (fun _ : Fin n ↦ SheafOfModules.unit (rings l E T none)),
        ∃ p : (∏ᶜ (fun _ : Fin n ↦ SheafOfModules.unit (rings l E T none))) ⟶ V.X k,
          i ≫ p = 𝟙 _ := finiteRetract_total P Q a b hb hP hQ
    have hmodel := KFlatTotalTensorModel.kFlat_total_tensor_model R P Q hkP hkQ hfP hfQ
    exact ⟨hbounds, hfree, hmodel.2.1, hkQ, hmodel.1, hmodel.2.2.2,
      finiteRetract_complete _ _ _ hunit V hbounds hfree⟩
  exact ⟨(integralQuotientCompletion_exact l E T _hl).1,
    (integralQuotientCompletion_exact l E T _hl).2,
    completedCoefficientUnit_completionUnit_isIso l E T _hl⟩

end WeilConjectures
