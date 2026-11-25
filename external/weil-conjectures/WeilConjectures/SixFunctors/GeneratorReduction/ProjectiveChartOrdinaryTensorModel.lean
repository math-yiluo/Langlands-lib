/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Bounded finite-projective models for ordinary tensors on a chart

Source: Stacks Tags 07A2, 07A4; Bhatt--Scholze, Lemma 6.5.5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.IntegralOnSlice.abSheafify
  WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.scalarReductionSourceDerived
  WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme MonoidalCategory Opposite SheafOfModules
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.pullbackTensorCalculus
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section FiniteRetracts

universe a v r w
variable {A : Type a} [Category.{v} A] [Abelian A]
attribute [local instance] Abelian.hasFiniteBiproducts

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
  let : ∀ (I₁ I₂ : Type r), HasColimitsOfShape (Discrete I₂)
      (PresheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
    fun _ _ ↦ PresheafOfModules.hasColimitsOfShape _ _
  let : HasCoproducts.{r} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) := fun I ↦ by
    let : HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
      PresheafOfModules.hasColimitsOfShape _ _
    exact
      SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  let : HasFiniteCoproducts (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
    hasFiniteCoproducts_of_hasCoproducts _
  let := isMonoidal_W_independentCoefficients R
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

private def recordedTensor (W : Scheme.{u}) :
    ProEtaleTensorModel W (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) := by
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W
  let F := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := R))
    (proEtaleFlatRepresentatives W R).ι
    (fun P ↦ (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).mpr
      P.property.1)
  exact ⟨(IntegralSystemRealization.calculus l E W).integralClosed.tensor,
    Functor.isoWhiskerLeft (F.prod F)
      (IntegralSystemRealization.calculus l E W).integralTensorModel.comparison⟩

@[irreducible] private def ordinaryPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IntegralOnSlice.ordinaryDerivedPull.{u, u} l E f ≅
      IntegralSystemRealization.ringedPull l E f := by
  have hmap : (⟨Functor.whiskerRight (sfCompletedCoefficientMap l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ :
        completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y ⟶
          (IntegralOnSlice.ordinaryRingPush.{u, u} f).obj
            (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)) =
      IntegralOnSlice.ordinaryCompletedRingMap.{u, u} l E f := by
    apply (IntegralOnSlice.ordinaryCompletedRingMap_existsUnique.{u, u} l E f).unique
    · intro n
      exact congrArg ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
        ((sfCompletedCoefficientMap_existsUnique l E f).exists.choose_spec n)
    · exact (IntegralOnSlice.ordinaryCompletedRingMap_existsUnique.{u, u} l E f).exists.choose_spec
  have hadj : proEtaleRingDirectImageMap f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f) = sfCompletedCoefficientMap l E f := by
    exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E f)
  let e : proEtaleRingModuleDirectImage f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f) ≅ IntegralOnSlice.ordinaryPush.{u, u} l E f := by
    unfold proEtaleRingModuleDirectImage IntegralOnSlice.ordinaryPush
    rw [hadj]
    exact SheafOfModules.pushforwardCongr hmap
  let a := (proEtaleRingModuleAdjunction f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).ofNatIsoRight e
  let b := a.leftAdjointUniq (IntegralOnSlice.ordinaryAdjunction.{u, u} l E f)
  have := preservesFiniteLimits_of_natIso b
  have := (IntegralOnSlice.ordinaryAdjunction.{u, u} l E f).leftAdjoint_preservesColimits
  have := IntegralOnSlice.ordinaryPull_additive.{u, u} l E f
  let d := Functor.mapDerivedCategoryNatIso b
  let F := IntegralOnSlice.ordinaryPull.{u, u} l E f
  let L : HomotopyCategory (scalarReductionSource.{u, u} l E Y) (.up ℤ) ⥤
      IntegralOnSlice.D.{u, u} l E Y none := DerivedCategory.Qh
  let : L.IsLocalization
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E Y) (.up ℤ)) :=
    inferInstanceAs ((DerivedCategory.Qh (C := scalarReductionSource.{u, u} l E Y)).IsLocalization
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E Y) (.up ℤ)))
  let : F.mapDerivedCategory.IsLeftDerivedFunctor (L := L) F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E Y) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts (L := L) _ F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh
  let : (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E Y) (.up ℤ)) :=
    IntegralOnSlice.ordinaryPull_hasLeftDerived.{u, u} l E f
  let ε := (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerivedCounit
    L (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E Y) (.up ℤ))
  let : (IntegralOnSlice.ordinaryDerivedPull.{u, u} l E f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E Y) (.up ℤ)) := by
    change Functor.IsLeftDerivedFunctor
      ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived
        L (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E Y) (.up ℤ))) ε
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E Y) (.up ℤ))
    dsimp only [ε]
    infer_instance
  let c : IntegralOnSlice.ordinaryDerivedPull.{u, u} l E f ≅ F.mapDerivedCategory :=
    Functor.leftDerivedUnique (L := L) F.mapDerivedCategory
      (IntegralOnSlice.ordinaryDerivedPull.{u, u} l E f)
      ε
      F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E Y) (.up ℤ))
  exact c ≪≫ d.symm

/-- Explicit bounded finite-projective models on a chart give such a model for
the restriction of the recorded ordinary tensor. This is a K-flat comparison and
finite totalization assertion; it makes no assertion of derived completeness.

Source: Stacks Tags 07A2 and 07A4, K-flat total tensor and pullback comparison;
Bhatt--Scholze, proof of Lemma 6.5.5, finite-projective tensor step.
(blueprint: lem-sf-projective-chart-ordinary-tensor-model).

Proof: the two ordinary pullback presentations have the same completed coefficient
map, as their finite quotient projections agree. Uniqueness of adjoints and left
derived functors identifies them. The K-flat normalized pullback/tensor comparison
identifies the restriction of the recorded ordinary tensor with the tensor of the
two restrictions. Bounded complexes of finite-free summands are K-flat. Transport
the two supplied model isomorphisms and compute their derived tensor by signed
direct-sum totalization. Its support is contained in the sum of the two finite
support intervals. Tensor the specified termwise splittings into finite free
modules, distribute over finite sums, and use the unitors. Each total degree has
only finitely many nonzero summands, so summing these splittings gives an actual
splitting into a finite free module. The K-flat representative comparison supplies
the displayed derived isomorphism. The construction uses no completeness result,
no invertibility of ell on the scheme, and covers rank zero and empty support. -/
theorem projectiveChartOrdinaryTensorModel {X T : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T] (f : T ⟶ X)
    (K L : IntegralOnSlice.D.{u, u} l E X none)
    (P Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    (hbP : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k))
    (hbQ : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (Q.X k))
    (hP : (∀ k : ℤ, ∃ r : ℕ,
            ∃ i : P.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)),
            ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T))) ⟶ P.X k,
            i ≫ p = 𝟙 _))
    (hQ : (∀ k : ℤ, ∃ r : ℕ,
            ∃ i : Q.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)),
            ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T))) ⟶ Q.X k,
            i ≫ p = 𝟙 _))
    (eP : Nonempty ((IntegralOnSlice.ordinaryDerivedPull.{u, u} l E f).obj K ≅
      DerivedCategory.Q.obj P))
    (eQ : Nonempty ((IntegralOnSlice.ordinaryDerivedPull.{u, u} l E f).obj L ≅
      DerivedCategory.Q.obj Q)) :
    ∃ V : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ,
      (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (V.X k)) ∧
      (∀ k : ℤ, ∃ r : ℕ,
            ∃ i : V.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)),
            ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T))) ⟶ V.X k,
            i ≫ p = 𝟙 _) ∧
      Nonempty ((IntegralOnSlice.ordinaryDerivedPull.{u, u} l E f).obj
        ((IntegralSystemRealization.calculus l E X).integralClosed.tensor.obj (K, L)) ≅
        DerivedCategory.Q.obj V) := by
  classical
  let R := IntegralOnSlice.ring.{u, u} l E T none
  let := isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := monoidalCategory.{u, u + 1, u + 1} R
  let := tensorPreadditive.{u + 1, u, u + 1} R
  have hflat (M : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
      (hM : ∀ k : ℤ, ∃ r : ℕ,
        ∃ i : M.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)),
        ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T))) ⟶ M.X k,
        i ≫ p = 𝟙 _) :
      ∀ k, IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology T) (R := R) (M.X k) := by
    intro k
    obtain ⟨r, i, p, hip⟩ := hM k
    exact finiteRetract_flat R _ r i p hip
  have hkflat (M : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
      (hb : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (M.X k))
      (hf : ∀ k, IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T) (R := R) (M.X k)) :
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := R) M := by
    obtain ⟨a, b, hb⟩ := hb
    have : M.IsStrictlyLE b := (M.isStrictlyLE_iff b).mpr (fun k hk ↦ hb k (.inr hk))
    exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R M b hf
  have hkP := hkflat P hbP (hflat P hP)
  have hkQ := hkflat Q hbQ (hflat Q hQ)
  obtain ⟨a, b, hb⟩ := hbP
  obtain ⟨c, d, hd⟩ := hbQ
  have : P.IsStrictlyGE a := (P.isStrictlyGE_iff a).mpr (fun k hk ↦ hb k (.inl hk))
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).mpr (fun k hk ↦ hb k (.inr hk))
  have : Q.IsStrictlyGE c := (Q.isStrictlyGE_iff c).mpr (fun k hk ↦ hd k (.inl hk))
  have : Q.IsStrictlyLE d := (Q.isStrictlyLE_iff d).mpr (fun k hk ↦ hd k (.inr hk))
  let V := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology T) R).obj (P, Q)
  have hbounds : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (V.X k) := by
    have hge := CochainComplex.isStrictlyGE_tensorObj P Q a c
    have hle := CochainComplex.isStrictlyLE_tensorObj P Q b d
    refine ⟨a + c, b + d, fun k hk ↦ ?_⟩
    rcases hk with hk | hk
    · exact (CochainComplex.isStrictlyGE_iff V (a + c)).mp hge k hk
    · exact (CochainComplex.isStrictlyLE_iff V (b + d)).mp hle k hk
  refine ⟨V, hbounds, finiteRetract_total P Q a b hb hP hQ, ?_⟩
  obtain ⟨eP⟩ := eP
  obtain ⟨eQ⟩ := eQ
  let TX := (IntegralSystemRealization.calculus l E X).integralClosed.tensor
  let TT := (IntegralSystemRealization.calculus l E T).integralClosed.tensor
  let pi := ordinaryPullIso l E f
  let tp := proEtaleCanonicalTensorComparison f
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).ring T) ((PurCompactSupport.completed l E).pull f)
    (recordedTensor l E X) (recordedTensor l E T)
  let : HasDerivedCategory (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
    integralTowerHasDerivedCategory l E T
  exact ⟨pi.app (TX.obj (K, L)) ≪≫ tp.app (K, L) ≪≫
    TT.mapIso ((pi.app K).symm.prod (pi.app L).symm) ≪≫
    TT.mapIso (eP.prod eQ) ≪≫
    ((IntegralSystemRealization.calculus l E T).integralTensorModel.iso
      (ProEt.topology T) R (IntegralSystemRealization.calculus l E T).integralClosed
      P Q hkP hkQ).symm⟩

end WeilConjectures.GeneratorReduction
