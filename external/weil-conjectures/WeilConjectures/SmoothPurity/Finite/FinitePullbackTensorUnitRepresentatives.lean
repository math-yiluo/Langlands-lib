/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorAssociativityRepresentatives
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorComparisonOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Unit equations on flat K-flat pullback tensor representatives

Source: Stacks Project, Tags 07A4, 06YS and 03EL.
(blueprint: lem-pur-finite-pullback-tensor-unit-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section UnitCoherence
open MonoidalCategory
universe a b c d e g

private theorem tripleNatTrans_ext_resolving
    {B : Type a} [Category.{b} B] {D : Type c} [Category.{d} D]
    {E : Type e} [Category.{g} E] (q : B ⥤ D) (P : ObjectProperty B)
    (res : ∀ X : D, ∃ Y : B, P Y ∧ Nonempty (q.obj Y ≅ X))
    {F G : D × D × D ⥤ E} (a b : F ⟶ G)
    (h : ∀ U V W : B, P U → P V → P W →
      a.app (q.obj U, q.obj V, q.obj W) = b.app (q.obj U, q.obj V, q.obj W)) :
    a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨U, hU, ⟨eU⟩⟩ := res X.1
  obtain ⟨V, hV, ⟨eV⟩⟩ := res X.2.1
  obtain ⟨W, hW, ⟨eW⟩⟩ := res X.2.2
  let e := Iso.prod eU (Iso.prod eV eW)
  apply (cancel_epi (F.map e.hom)).1
  rw [a.naturality, b.naturality, h U V W hU hV hW]

section Paths
variable {D : Type a} [Category.{b} D] [MonoidalCategory D]
  {E : Type c} [Category.{d} E] [MonoidalCategory E]
  (F : D ⥤ E) (μ : tensor D ⋙ F ≅ F.prod F ⋙ tensor E)

private abbrev assocLeftPath :
    leftAssocTensor D ⋙ F ⟶ (F.prod (F.prod F)) ⋙ rightAssocTensor E :=
  Functor.whiskerRight (associatorNatIso D).hom F ≫
    Functor.whiskerLeft ((𝟭 D).prod (tensor D)) μ.hom ≫
      Functor.whiskerRight (NatTrans.prod (𝟙 F) μ.hom) (tensor E)

private abbrev assocRightPath :
    leftAssocTensor D ⋙ F ⟶ (F.prod (F.prod F)) ⋙ rightAssocTensor E := by
  let p₁ := CategoryTheory.Prod.fst D (D × D)
  let p₂ := CategoryTheory.Prod.snd D (D × D) ⋙ CategoryTheory.Prod.fst D D
  let p₃ := CategoryTheory.Prod.snd D (D × D) ⋙ CategoryTheory.Prod.snd D D
  let p₁₂ := p₁.prod' p₂
  exact Functor.whiskerLeft ((p₁₂ ⋙ tensor D).prod' p₃) μ.hom ≫
    Functor.whiskerRight
      (NatTrans.prod' (Functor.whiskerLeft p₁₂ μ.hom) (𝟙 (p₃ ⋙ F))) (tensor E) ≫
    Functor.whiskerLeft (F.prod (F.prod F)) (associatorNatIso E).hom

end Paths

private theorem associativity_of_paths
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (hA : assocLeftPath F μ = assocRightPath F μ) (A B M : C) :
    F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
        F.obj A ◁ (μ.app (B, M)).hom =
      (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
        (α_ (F.obj A) (F.obj B) (F.obj M)).hom := by
  have h := NatTrans.congr_app hA (A, B, M)
  change F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
      (𝟙 (F.obj A) ⊗ₘ (μ.app (B, M)).hom) =
    (μ.app (A ⊗ B, M)).hom ≫ ((μ.app (A, B)).hom ⊗ₘ 𝟙 (F.obj M)) ≫
      (α_ (F.obj A) (F.obj B) (F.obj M)).hom at h
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h ⊢
  simpa only [id_tensorHom, tensorHom_id] using h

private theorem leftUnit_of_rightUnit
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (ha : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          F.obj A ◁ (μ.app (B, M)).hom =
        (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom)
    (hr : (μ.app (𝟙_ C, 𝟙_ C)).hom ≫ F.obj (𝟙_ C) ◁ ε.hom ≫
      (ρ_ (F.obj (𝟙_ C))).hom = F.map (ρ_ (𝟙_ C)).hom) (M : C) :
    (μ.app (𝟙_ C, M)).hom ≫ ε.hom ▷ F.obj M ≫ (λ_ (F.obj M)).hom =
      F.map (λ_ M).hom := by
  let I := 𝟙_ C
  have hnL := μ.hom.naturality (Prod.mkHom (ρ_ I).hom (𝟙 M))
  have hnR := μ.hom.naturality (Prod.mkHom (𝟙 I) (λ_ M).hom)
  change F.map ((ρ_ I).hom ⊗ₘ 𝟙 M) ≫ (μ.app (I, M)).hom =
    (μ.app (I ⊗ I, M)).hom ≫ (F.map (ρ_ I).hom ⊗ₘ F.map (𝟙 M)) at hnL
  change F.map (𝟙 I ⊗ₘ (λ_ M).hom) ≫ (μ.app (I, M)).hom =
    (μ.app (I, I ⊗ M)).hom ≫ (F.map (𝟙 I) ⊗ₘ F.map (λ_ M).hom) at hnR
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at hnL hnR
  simp only [F.map_id, tensorHom_id, id_tensorHom] at hnL hnR
  have h : F.obj I ◁ ((μ.app (I, M)).hom ≫ ε.hom ▷ F.obj M ≫
      (λ_ (F.obj M)).hom) = F.obj I ◁ F.map (λ_ M).hom := by
    apply (cancel_epi (F.map (α_ I I M).hom ≫ (μ.app (I, I ⊗ M)).hom)).mp
    simp only [whiskerLeft_comp, Category.assoc]
    rw [reassoc_of% (ha I I M)]
    rw [← associator_naturality_middle_assoc, triangle]
    simp only [← comp_whiskerRight]
    rw [hr]
    rw [← hnL]
    rw [← triangle, F.map_comp, Category.assoc, hnR]
  have h' := congrArg
    (fun t ↦ t ≫ ε.hom ▷ F.obj M ≫ (λ_ (F.obj M)).hom) h
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h'
  simp only [whisker_exchange_assoc, leftUnitor_naturality] at h'
  apply (cancel_epi (ε.hom ▷ F.obj (I ⊗ M) ≫ (λ_ (F.obj (I ⊗ M))).hom)).mp
  simpa only [Category.assoc] using h'

private theorem rightUnit_of_leftUnit
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (ha : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          F.obj A ◁ (μ.app (B, M)).hom =
        (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom)
    (hl : (μ.app (𝟙_ C, 𝟙_ C)).hom ≫ ε.hom ▷ F.obj (𝟙_ C) ≫
      (λ_ (F.obj (𝟙_ C))).hom = F.map (λ_ (𝟙_ C)).hom) (M : C) :
    (μ.app (M, 𝟙_ C)).hom ≫ F.obj M ◁ ε.hom ≫ (ρ_ (F.obj M)).hom =
      F.map (ρ_ M).hom := by
  let I := 𝟙_ C
  have hnL := μ.hom.naturality (Prod.mkHom (ρ_ M).hom (𝟙 I))
  have hnR := μ.hom.naturality (Prod.mkHom (𝟙 M) (λ_ I).hom)
  change F.map ((ρ_ M).hom ⊗ₘ 𝟙 I) ≫ (μ.app (M, I)).hom =
    (μ.app (M ⊗ I, I)).hom ≫ (F.map (ρ_ M).hom ⊗ₘ F.map (𝟙 I)) at hnL
  change F.map (𝟙 M ⊗ₘ (λ_ I).hom) ≫ (μ.app (M, I)).hom =
    (μ.app (M, I ⊗ I)).hom ≫ (F.map (𝟙 M) ⊗ₘ F.map (λ_ I).hom) at hnR
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at hnL hnR
  simp only [F.map_id, tensorHom_id, id_tensorHom] at hnL hnR
  have h : ((μ.app (M, I)).hom ≫ F.obj M ◁ ε.hom ≫
      (ρ_ (F.obj M)).hom) ▷ F.obj I = F.map (ρ_ M).hom ▷ F.obj I := by
    apply (cancel_epi (μ.app (M ⊗ I, I)).hom).mp
    simp only [comp_whiskerRight]
    rw [← triangle, associator_naturality_middle_assoc]
    dsimp only [Functor.prod_obj]
    rw [← reassoc_of% (ha M I I)]
    simp only [← whiskerLeft_comp]
    rw [hl]
    rw [← hnR, ← F.map_comp_assoc, triangle, hnL]
  have h' := congrArg
    (fun t ↦ t ≫ F.obj M ◁ ε.hom ≫ (ρ_ (F.obj M)).hom) h
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h'
  simp only [← whisker_exchange_assoc, rightUnitor_naturality] at h'
  apply (cancel_epi (F.obj (M ⊗ I) ◁ ε.hom ≫ (ρ_ (F.obj (M ⊗ I))).hom)).mp
  simpa only [Category.assoc] using h'

private theorem unit_from_tensor
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (e : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (ha : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          F.obj A ◁ (μ.app (B, M)).hom =
        (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom) :
    ∃ ε : F.obj (𝟙_ C) ≅ 𝟙_ D,
      (∀ M : C, (μ.app (𝟙_ C, M)).hom ≫ (ε.hom ⊗ₘ 𝟙 (F.obj M)) ≫
        (λ_ (F.obj M)).hom = F.map (λ_ M).hom) ∧
      (∀ M : C, (μ.app (M, 𝟙_ C)).hom ≫ (𝟙 (F.obj M) ⊗ₘ ε.hom) ≫
        (ρ_ (F.obj M)).hom = F.map (ρ_ M).hom) := by
  let I := 𝟙_ C
  let t : tensorLeft (F.obj I) ≅ 𝟭 D := NatIso.ofComponents
    (fun X ↦ whiskerRightIso e X ≪≫ λ_ X) (by
      intro X Y g
      change F.obj I ◁ g ≫ e.hom ▷ Y ≫ (λ_ Y).hom =
        (e.hom ▷ X ≫ (λ_ X).hom) ≫ g
      rw [whisker_exchange_assoc, leftUnitor_naturality]
      simp only [Category.assoc])
  let ff := (Functor.FullyFaithful.id D).ofIso t.symm
  let j : (tensorLeft (F.obj I)).obj (F.obj I) ≅
      (tensorLeft (F.obj I)).obj (𝟙_ D) :=
    (μ.app (I, I)).symm ≪≫ F.mapIso (ρ_ I) ≪≫ (ρ_ (F.obj I)).symm
  let ε := ff.preimageIso j
  have hr : (μ.app (I, I)).hom ≫ F.obj I ◁ ε.hom ≫
      (ρ_ (F.obj I)).hom = F.map (ρ_ I).hom := by
    have he := ff.map_preimage j.hom
    change F.obj I ◁ ε.hom = j.hom at he
    rw [he]
    simp [j]
  have hl := leftUnit_of_rightUnit F μ ε ha hr
  refine ⟨ε, ?_, ?_⟩
  · intro M
    have h := hl M
    dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h ⊢
    simpa only [tensorHom_id] using h
  · intro M
    have h := rightUnit_of_leftUnit F μ ε ha (hl I) M
    dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h ⊢
    simpa only [id_tensorHom] using h

end UnitCoherence

open MonoidalCategory

private theorem finiteTensor_flat_representatives (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) (n : ℕ)
    (M : normalizedDVRDerived l E Y n) :
    ∃ P : CochainComplex (normalizedDVRModules l E Y n) ℤ,
      proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  let q := DerivedCategory.Q (C := normalizedDVRModules l E Y n)
  let K := q.objPreimage M
  obtain ⟨P, a, hP, hflat, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  let : IsIso (q.map a) := Localization.inverts
    (DerivedCategory.Q (C := normalizedDVRModules l E Y n))
    (HomologicalComplex.quasiIso (normalizedDVRModules l E Y n) (ComplexShape.up ℤ)) a ha
  refine ⟨P, ⟨hP, ?_⟩, ⟨asIso (q.map a) ≪≫ q.objObjPreimageIso M⟩⟩
  intro i
  exact (CategoryTheory.exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso
      (integralCoefficientCommRingSheaf l E Y n) (P.X i)).symm (hflat i)

-- Closed adjunctions determine the tensor unit up to the isomorphism needed here.
private def finiteUnit_single (X : Scheme.{u}) (n : ℕ) :
    (finiteIntrinsicClosed l E X n).monoidal.tensorUnit ≅
      (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X n) 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E X n)) := by
  let S := finiteIntrinsicClosed l E X n
  let h := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2}
    (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
  let S₀ := h.choose
  let h₀ := h.choose_spec.choose_spec.choose_spec.some
  let U := S₀.monoidal.tensorUnit
  let e := (S.adjunction U).leftAdjointUniq (S₀.adjunction U)
  exact (S₀.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
    (e.app S.monoidal.tensorUnit).symm ≪≫ S.monoidal.leftUnitor U ≪≫ h₀.unitIso

open SheafOfModules.CanonicalTensorPullbackOfUniverses in
private theorem finitePullbackTensor_module_unit {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    Nonempty ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≅
        SheafOfModules.unit (integralCoefficientSheaf l E X n)) := by
  let R := integralCoefficientCommRingSheaf l E Y n
  let S := integralCoefficientCommRingSheaf l E X n
  let RI := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
  let c : RI ⟶ S := (pullbackTensorCoefficientIso l E f n).hom
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists f R
  have : CategoryTheory.Limits.PreservesFiniteLimits
      (proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  let T := I.modules ⋙ proEtaleRingExtension f R S (pullbackTensorCoefficientIso l E f n)
  have hT : T = proEtaleRingModulePullback f R S
      (pullbackTensorCoefficientIso l E f n) := by
    dsimp only [T]
    rw [hI]
    rfl
  have hobj (M) : T.obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} c (I.modules.obj M) := rfl
  have hmap : ∀ {M N} (g : M ⟶ N), T.map g = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c
        (I.modules.obj M) (I.modules.map g) ≫ eqToHom (hobj N).symm := by
    intro M N g
    rfl
  obtain ⟨k⟩ := (canonicalRingedTensorComparison_existsUnique R S RI
      (proEtaleSheafInverseImage f (Type (u + 1))) I c T hobj
      (proEtaleSheafDirectImage f (Type (u + 1)))
      (proEtaleSheafAdjunction f (Type (u + 1))) hmap).1
  obtain ⟨j, _⟩ := (canonicalRingedTensorComparison_unit R S RI
      (proEtaleSheafInverseImage f (Type (u + 1))) I c T hobj hmap k).exists
  rw [hT] at j
  exact ⟨((pullbackTensorFiniteRealization l E f n).app _).symm ≪≫ j⟩

private theorem finitePullbackTensor_unit_object {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    Nonempty ((finiteDerivedPullback l E n f).obj
      (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit ≅
        (finiteIntrinsicClosed l E X n).monoidal.tensorUnit) := by
  let A := finiteCoefficientRing l E (n + 1)
  let F := sfIntrinsicPullback A f
  let : F.Additive := sfIntrinsicPullback_additive A f
  let : CategoryTheory.Limits.PreservesFiniteLimits F :=
    sfIntrinsicPullback_preservesFiniteLimits A f
  let : CategoryTheory.Limits.PreservesFiniteColimits F :=
    sfIntrinsicPullback_preservesFiniteColimits A f
  obtain ⟨j⟩ := finitePullbackTensor_module_unit l E f n
  exact ⟨(finiteDerivedPullback l E n f).mapIso (finiteUnit_single l E Y n) ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X n) 0).mapIso j ≪≫
    (finiteUnit_single l E X n).symm⟩

/-- Existence of a single unit comparison satisfying both equations on flat K-flats.
Source: Stacks 03EL, ordinary pullback tensor product and its rank-one unit;
07A4, lemma-pullback-tensor-product, total-tensor construction.
(blueprint: lem-pur-finite-pullback-tensor-unit-representatives).
Proof: first identify each intrinsic tensor unit with the coefficient module
in degree zero, using uniqueness of the closed tensor adjoints. Ordinary ringed
pullback preserves this rank-one module; exact pullback commutes with the
single-complex functor. Thus the derived pullback of the intrinsic unit is
isomorphic to the target unit. Extend the existing associativity equation on
flat K-flat triples to all triples by naturality and flat K-flat resolutions.
Tensoring with the image of the unit is fully faithful, since this object is
isomorphic to the target unit. Its full faithfulness determines an isomorphism
epsilon whose right unit equation holds at the source unit. Associativity at
(1,1,M), the triangle identity and cancellation imply the left unit equation
for every M. Associativity at (M,1,1) then implies the right unit equation.
Specialize both equations to the requested localized representatives. -/
theorem finitePullbackTensor_unit_representatives_exists {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ ε : (finiteDerivedPullback l E n f).obj
        (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit ≅
      (finiteIntrinsicClosed l E X n).monoidal.tensorUnit,
      ∀ (P : CochainComplex (normalizedDVRModules l E Y n) ℤ)
        (_hP : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) P),
        let M := DerivedCategory.Q.obj P
        (((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
          (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit M).hom ≫
          (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((finiteIntrinsicClosed l E X n).monoidal.leftUnitor
            ((finiteDerivedPullback l E n f).obj M)).hom =
          (finiteDerivedPullback l E n f).map
            ((finiteIntrinsicClosed l E Y n).monoidal.leftUnitor M).hom) ∧
        (((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M
          (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit).hom ≫
          (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((finiteIntrinsicClosed l E X n).monoidal.rightUnitor
            ((finiteDerivedPullback l E n f).obj M)).hom =
          (finiteDerivedPullback l E n f).map
            ((finiteIntrinsicClosed l E Y n).monoidal.rightUnitor M).hom) := by
  let : MonoidalCategory
      (proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :=
    (finiteIntrinsicClosed l E Y n).monoidal
  let : MonoidalCategory
      (proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))) :=
    (finiteIntrinsicClosed l E X n).monoidal
  let D := proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))
  let F := finiteDerivedPullback l E n f
  let μ := finitePullbackTensorConstructionIso l E f n
  let q : CochainComplex (normalizedDVRModules l E Y n) ℤ ⥤ D := DerivedCategory.Q
  have hA : assocLeftPath F μ = assocRightPath F μ :=
    tripleNatTrans_ext_resolving q
      (proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n))
      (finiteTensor_flat_representatives l E Y n) _ _ (by
        intro A B C hA hB hC
        exact finitePullbackTensor_associativity_representatives l E f n A B C hA hB hC)
  obtain ⟨e⟩ := finitePullbackTensor_unit_object l E f n
  obtain ⟨ε, hL, hR⟩ := unit_from_tensor F μ e (associativity_of_paths F μ hA)
  refine ⟨ε, ?_⟩
  intro P hP
  exact ⟨hL (q.obj P), hR (q.obj P)⟩

end WeilConjectures
