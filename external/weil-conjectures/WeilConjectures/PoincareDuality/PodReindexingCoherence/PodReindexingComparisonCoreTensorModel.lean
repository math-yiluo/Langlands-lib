/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingComparisonCoreTensorData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingTensorPresentationComparison
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Localization.Prod

import all WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData

/-! Tensor model normalization for the core reindexing comparison.
(blueprint: lem-pod-reindexing-comparison-core-tensor-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local instance 1000001] cachedCompose

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] podReindexingCoefficient podReindexingHomModel
  homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientTotalTensor coefficientTensorGenerator SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors
  CoefficientClosedStructure.tensor

set_option allowUnsafeReducibility true in
attribute [local irreducible] podReindexingDerivedFunctor podReindexingDerivedFactors

structure ComparisonCoreTensorModelData {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (tensorChain : ∀ P L : K l E Y s,
      (podReindexingComplexFunctor l E g s).obj ((total l E Y s).obj (P, L)) ≅
        (total l E X s).obj ((podReindexingComplexFunctor l E g s).obj P,
          (podReindexingComplexFunctor l E g s).obj L))
    (tensor : SY.tensor ⋙ podReindexingDerivedFunctor l E g s ≅
      ((podReindexingDerivedFunctor l E g s).prod (podReindexingDerivedFunctor l E g s)) ⋙
        SX.tensor) where
  tensor_model : ∀ (P L : K l E Y s)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) P)
    (hL : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) L),
    ∃ (hFP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := podReindexingRing l E X s) ((podReindexingComplexFunctor l E
        g s).obj P))
      (hFL : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := podReindexingRing l E X s) ((podReindexingComplexFunctor l E
        g s).obj L)),
      (podReindexingDerivedFunctor l E g s).map
        ((@CoefficientTensorModels.comparison.{u, u + 1, u, u + 2} _ _ (ProEt.topology Y)
          _ _ (podReindexingRing l E Y s) (HasDerivedCategory.standard.{u + 1, u + 2} _) SY
            TY).hom.app (⟨P, hP⟩, ⟨L, hL⟩)) ≫
        tensor.hom.app ((podReindexingQ l E Y s).obj P, (podReindexingQ l E Y s).obj L) ≫
        SX.tensor.map (Prod.mkHom ((podReindexingDerivedFactors l E g s).hom.app P)
          ((podReindexingDerivedFactors l E g s).hom.app L)) =
      (podReindexingDerivedFactors l E g s).hom.app ((total l E Y s).obj (P, L)) ≫
        (podReindexingQ l E X s).map (tensorChain P L).hom ≫
        (@CoefficientTensorModels.comparison.{u, u + 1, u, u + 2} _ _ (ProEt.topology X)
          _ _ (podReindexingRing l E X s) (HasDerivedCategory.standard.{u + 1, u + 2} _) SX
            TX).hom.app (⟨_, hFP⟩, ⟨_, hFL⟩)

private theorem whisker_preimageIso {B D A : Type*}
    [Category* B] [Category* D] [Category* A] (L : B ⥤ D)
    (FF : ((Functor.whiskeringLeft B D A).obj L).FullyFaithful)
    {G H : D ⥤ A} (e : L ⋙ G ≅ L ⋙ H) :
    Functor.isoWhiskerLeft L (FF.preimageIso e) = e := by
  apply Iso.ext
  exact FF.map_preimage e.hom

private theorem normalized_tensor_square {D A : Type*} [Category* D] [Category* A]
    (r : D ⥤ A) (F : A × A ⥤ A) {B C : D} {U U' V V' : A}
    (t : B ≅ C) (b : U ≅ U') (c : V ≅ V')
    (g : r.obj B ⟶ F.obj (U', V')) (q : r.obj C ⟶ F.obj (U, V))
    (h : q = r.map t.inv ≫ g ≫ F.map (b.inv, c.inv)) :
    r.map t.hom ≫ q ≫ F.map (b.hom, c.hom) = g := by
  rw [h]
  simp only [← Category.assoc, ← r.map_comp, Iso.hom_inv_id,
    r.map_id, Category.id_comp]
  simp only [Category.assoc, ← F.map_comp, prod_comp, Iso.inv_hom_id,
    ← prod_id', F.map_id, Category.comp_id]

attribute [local irreducible] Localization.fullyFaithfulWhiskeringLeft
  Functor.FullyFaithful.preimageIso

/-- Descend a tensor square before specializing its categories to sheaves. -/
private theorem descend_tensor_square {C D A : Type*}
    [Category* C] [Category* D] [Category* A]
    (L : C ⥤ D) (W : MorphismProperty C) [W.ContainsIdentities] [L.IsLocalization W]
    (r : D ⥤ A) (T : D × D ⥤ D) (T' : A × A ⥤ A)
    (B : C × C ⥤ D) (U : C ⥤ A)
    (m : B ≅ (L.prod L) ⋙ T) (a : L ⋙ r ≅ U)
    (e : B ⋙ r ≅ (U.prod U) ⋙ T') :
    ∃ ρ : T ⋙ r ≅ (r.prod r) ⋙ T', ∀ P Q : C,
      r.map (m.hom.app (P, Q)) ≫ ρ.hom.app (L.obj P, L.obj Q) ≫
          T'.map (X := (r.obj (L.obj P), r.obj (L.obj Q)))
            (Y := (U.obj P, U.obj Q)) (a.hom.app P, a.hom.app Q) =
        e.hom.app (P, Q) := by
  let e₀ : (L.prod L) ⋙ (T ⋙ r) ≅ (L.prod L) ⋙ ((r.prod r) ⋙ T') :=
    Functor.isoWhiskerRight m.symm r ≪≫ e ≪≫
      (Functor.isoWhiskerRight (NatIso.prod a a) T').symm
  let FF := Localization.fullyFaithfulWhiskeringLeft (L.prod L) (W.prod W) A
  let ρ : T ⋙ r ≅ (r.prod r) ⋙ T' := FF.preimageIso e₀
  have hρ : Functor.isoWhiskerLeft (L.prod L) ρ = e₀ :=
    whisker_preimageIso (L.prod L) FF e₀
  refine ⟨ρ, ?_⟩
  intro P Q
  have he := congrArg (fun i ↦ i.hom.app (P, Q)) hρ
  change ρ.hom.app (L.obj P, L.obj Q) = r.map (m.inv.app (P, Q)) ≫
    e.hom.app (P, Q) ≫ T'.map
      (X := (U.obj P, U.obj Q)) (Y := (r.obj (L.obj P), r.obj (L.obj Q)))
      (a.inv.app P, a.inv.app Q) at he
  exact normalized_tensor_square r T' (m.app (P, Q)) (a.app P) (a.app Q)
    (e.hom.app (P, Q)) (ρ.hom.app (L.obj P, L.obj Q)) he

/-- The derived tensor comparison is chosen by descent of the pure-tensor chain
comparison, rather than independently of it.
Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 07A4.
(blueprint: lem-pod-reindexing-comparison-core-tensor-model).

Proof: pure tensors determine the natural chain comparison. Reindexing preserves
K-flatness. Conjugate this chain comparison by the two fixed K-flat tensor models
and the localization factorization. The product of the K-flat localizations is a
localization, so full faithfulness of precomposition descends this isomorphism.
Its preimage equation, after cancelling the three model isomorphisms, is exactly
the tensor model normalization.
-/
theorem comparison_core_tensor_model_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (t : ComparisonCoreTensorData l E g s SX SY TX TY) :
    ∃ tensor : SY.tensor ⋙ podReindexingDerivedFunctor l E g s ≅
        ((podReindexingDerivedFunctor l E g s).prod (podReindexingDerivedFunctor l E g s)) ⋙
          SX.tensor,
      Nonempty (ComparisonCoreTensorModelData l E g s SX SY TX TY t.tensorChain tensor) := by
  let r := podReindexingDerivedFunctor l E g s
  let α := podReindexingDerivedFactors l E g s
  let K := coefficientKFlatInclusion.{u, u + 1, u}
    (ProEt.topology Y) (podReindexingRing l E Y s)
  let KX := coefficientKFlatInclusion.{u, u + 1, u}
    (ProEt.topology X) (podReindexingRing l E X s)
  let F := tensorKFlatReindexing l E g s
  let L := K ⋙ podReindexingQ l E Y s
  let LX := KX ⋙ podReindexingQ l E X s
  let W := (HomologicalComplex.quasiIso (podReindexingModules l E Y s)
    (.up ℤ)).inverseImage K
  have : L.IsLocalization W := RingedDerivedNative.kFlatLocalization.{u + 1, u, u, u + 2}
    (ProEt.topology Y) (podReindexingRing l E Y s)
  let a : L ⋙ r ≅ F ⋙ LX := Functor.isoWhiskerLeft K α
  obtain ⟨e, he⟩ := tensor_presentation_comparison l E g s SX SY TX TY t
  obtain ⟨ρ, hρ⟩ := descend_tensor_square L W r SY.tensor SX.tensor
    (((K.prod K) ⋙ total l E Y s) ⋙ podReindexingQ l E Y s) (F ⋙ LX) TY.comparison a e
  refine ⟨ρ, ⟨⟨?_⟩⟩⟩
  intro P Q hP hQ
  exact ⟨(F.obj ⟨P, hP⟩).property, (F.obj ⟨Q, hQ⟩).property,
    (hρ ⟨P, hP⟩ ⟨Q, hQ⟩).trans (he ⟨P, hP⟩ ⟨Q, hQ⟩)⟩

end WeilConjectures.PodReindexingCoherence
