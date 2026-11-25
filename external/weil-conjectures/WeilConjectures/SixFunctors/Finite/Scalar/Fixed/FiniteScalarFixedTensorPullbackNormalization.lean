/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTensorIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarPullbackRepresentativeFactors
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarComplexTensorPullback
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import all WeilConjectures.AlgebraicGeometry.SectionDerivedRepresentativeSquare
import all Mathlib.Algebra.Homology.Localization

/-! # Fixed-scalar tensor pullback on complexes

Source: Stacks Tags 00YV and 07A6.
(blueprint: lem-sf-finite-scalar-fixed-tensor-pullback-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

namespace WeilConjectures

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

private theorem cancelTensorators
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {S T U V : D} (v : X ⟶ Y) [IsIso v] (w : U ⟶ V) [IsIso w]
    (a : F.obj X ⟶ S) (b : S ⟶ U) (c : F.obj Y ⟶ T) (d : T ⟶ V)
    (h : a ≫ b ≫ w = F.map v ≫ c ≫ d) :
    F.map (inv v) ≫ a ≫ b = c ≫ d ≫ inv w := by
  apply (cancel_epi (F.map v)).mp
  apply (cancel_mono w).mp
  simpa only [Category.assoc, ← F.map_comp_assoc, IsIso.hom_inv_id,
    F.map_id, Category.id_comp, IsIso.inv_hom_id, Category.comp_id] using h

private theorem exact_factors_eq_counit
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (L : C ⥤ D) [L.Additive] [Limits.PreservesFiniteLimits L]
    [Limits.PreservesFiniteColimits L] (Z : CochainComplex C ℤ) :
    L.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj Z) ≫
        L.mapDerivedCategoryFactors.hom.app Z =
      L.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Z) := by
  have h := L.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac
    ((HomotopyCategory.quotient _ _).obj Z)
  rw [CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app] at h
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    CategoryTheory.Functor.mapHomotopyCategoryFactors] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at h
  exact h

private theorem representative_hom_eq
    {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (S : ObjectProperty (CochainComplex C ℤ))
    (hS : ∀ Z, S Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (P Q : CochainComplex C ℤ) (hp : S P) (hq : S Q)
    [IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)] :
    (finiteScalarFixedTensorRepresentativeOfKFlat S hS).hom.app (⟨P, hp⟩, ⟨Q, hq⟩) =
      inv (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  simp only [finiteScalarFixedTensorRepresentativeOfKFlat, Iso.symm_hom, asIso_inv,
    NatIso.isIso_inv_app]

private theorem uncurry_tensor_map
    {C : Type*} [Category C] [MonoidalCategory C]
    {P Q P' Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') :
    (uncurry.obj (curriedTensor C)).map (Prod.mkHom f g) = f ⊗ₘ g := by
  simp only [uncurry_obj_map, curriedTensor_obj_map, curriedTensor_map_app,
    MonoidalCategory.tensorHom_def]

open AlgebraicGeometry.ProEtale.ModuleRingedComparison in
private theorem representative_normalization
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    (S : ObjectProperty (CochainComplex C ℤ))
    (hS : ∀ Z, S Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (T : ObjectProperty (CochainComplex D ℤ))
    (hT : ∀ Z, T Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (L : C ⥤ D) [L.Additive] [L.PreservesKFlatQuasiIso] [L.PreservesFlat]
    [L.IsLeftAdjoint] [L.Monoidal]
    (f : DerivedCategory.Q ⋙ L.leftDerivedFunctor ≅
      L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hf : ∀ Z, f.hom.app Z =
      L.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Z))
    (P Q : CochainComplex C ℤ) (hp : S P) (hq : S Q)
    (hp' : T ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (hq' : T ((L.mapHomologicalComplex (.up ℤ)).obj Q)) :
    L.leftDerivedFunctor.map
        ((finiteScalarFixedTensorRepresentativeOfKFlat S hS).hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      ((L.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)) ≫
      (uncurry.obj (curriedTensor (DerivedCategory D))).map
        (Prod.mkHom (f.hom.app P) (f.hom.app Q)) =
    f.hom.app (CochainComplex.mapBifunctor P Q (curriedTensor C)) ≫
      DerivedCategory.Q.map
        ((finiteScalarComplexTensorPullbackForFunctor L).app (P, Q)) ≫
      (finiteScalarFixedTensorRepresentativeOfKFlat T hT).hom.app
        (⟨(L.mapHomologicalComplex (.up ℤ)).obj P, hp'⟩,
         ⟨(L.mapHomologicalComplex (.up ℤ)).obj Q, hq'⟩) := by
  have hsource := finiteScalarLocalizationTensor_isIso P Q (hS Q hq)
  have htarget := finiteScalarLocalizationTensor_isIso
    ((L.mapHomologicalComplex (.up ℤ)).obj P)
    ((L.mapHomologicalComplex (.up ℤ)).obj Q) (hT _ hq')
  simp only [representative_hom_eq, uncurry_tensor_map, hf,
    finiteScalarComplexTensorPullbackForFunctor_app]
  exact cancelTensorators L.leftDerivedFunctor
    (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)
    (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((L.mapHomologicalComplex (.up ℤ)).obj P)
      ((L.mapHomologicalComplex (.up ℤ)).obj Q)) _ _ _ _
    (DerivedRepresentativeSquare.cochain_tensor_comparison
      L P Q)

/-- The native fixed-coefficient pullback comparison satisfies the representative equation.
Source: Stacks Tag 07A4, the defining left-derived tensor square.
(blueprint: lem-sf-finite-scalar-fixed-tensor-pullback-normalization).

Proof: use the generic complex tensor comparison square and the inverse localization
tensorators. The assumed factor-counit equation identifies its unary factors.
The native pro-etale comparison is the generic left-derived comparison.
-/
theorem finiteScalarTensorPullback_normalizationForCoefficients
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] [ProEtale.UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (S : ObjectProperty (CochainComplex (Sheaf (ProEt.topology Y) B) ℤ))
    (hS : ∀ Z, S Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (T : ObjectProperty (CochainComplex (Sheaf (ProEt.topology X) B) ℤ))
    (hT : ∀ Z, T Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (f : DerivedCategory.Q ⋙ (ProEtale.upperStar B p).leftDerivedFunctor ≅
      (ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hf : ∀ Z, f.hom.app Z =
      (ProEtale.upperStar B p).leftDerivedFunctor.map
          ((DerivedCategory.quotientCompQhIso _).inv.app Z) ≫
        (ProEtale.upperStar B p).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj Z) ≫
        DerivedCategory.Qh.map
          (((ProEtale.upperStar B p).mapHomotopyCategoryFactors _).hom.app Z) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app _)
    (P Q : CochainComplex (Sheaf (ProEt.topology Y) B) ℤ) (hp : S P) (hq : S Q)
    (hp' : T (((ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ)).obj P))
    (hq' : T (((ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ)).obj Q)) :
    (ProEtale.upperStar B p).leftDerivedFunctor.map
        ((finiteScalarRepresentativeTensorIso B Y S hS).hom.app
          (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      ((ProEtale.leftDerivedUpperStarTensorComparison B p).app
        (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
      (uncurry.obj (ProEtale.derivedTensor B X)).map
        (Prod.mkHom (f.hom.app P) (f.hom.app Q)) =
    f.hom.app ((finiteScalarRepresentativeTotalTensor (Sheaf (ProEt.topology Y) B)).obj (P, Q)) ≫
      DerivedCategory.Q.map
        ((finiteScalarFixedComplexTensorPullbackForCoefficients B p).app (P, Q)) ≫
      (finiteScalarRepresentativeTensorIso B X T hT).hom.app
        (⟨((ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ)).obj P, hp'⟩,
         ⟨((ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ)).obj Q, hq'⟩) := by
  unfold finiteScalarFixedComplexTensorPullbackForCoefficients
  simp only [finiteScalarRepresentativeTensorIso_hom_app]
  rw [ProEtale.leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison]
  unfold finiteScalarFixedTensorRepresentativeForCoefficients
  have h₁ (K : CochainComplex (Sheaf (ProEt.topology Y) B) ℤ) :
      (DerivedCategory.quotientCompQhIso _).inv.app K = 𝟙 _ := rfl
  have h₂ (K : CochainComplex (Sheaf (ProEt.topology X) B) ℤ) :
      (DerivedCategory.quotientCompQhIso _).hom.app K = 𝟙 _ := rfl
  have hf₀ (Z : CochainComplex (Sheaf (ProEt.topology Y) B) ℤ) :
      f.hom.app Z = (ProEtale.upperStar B p).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj Z) := by
    rw [hf Z, h₁, h₂, Functor.mapHomotopyCategoryFactors_hom_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  exact representative_normalization S hS T hT (ProEtale.upperStar B p) f hf₀ P Q hp hq hp' hq'

/-- The exact fixed-scalar pullback factors are the left-derived counit on complexes.
Source: the exact-functor left-derived counit formula, Stacks Tag 07A4.
(blueprint: lem-sf-finite-scalar-fixed-tensor-pullback-normalization). -/
theorem finiteScalarFixedPullbackFactors_eq_counit
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (Z : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    (finiteScalarFixedPullbackFactors R p).hom.app Z =
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).leftDerivedFunctor.map
          ((DerivedCategory.quotientCompQhIso _).inv.app Z) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj Z) ≫
        DerivedCategory.Qh.map
          (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomotopyCategoryFactors
            _).hom.app Z) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app _ := by
  have h₁ (K : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
      (DerivedCategory.quotientCompQhIso _).inv.app K = 𝟙 _ := rfl
  have h₂ (K : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
      (DerivedCategory.quotientCompQhIso _).hom.app K = 𝟙 _ := rfl
  rw [h₁, h₂, Functor.mapHomotopyCategoryFactors_hom_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [finiteScalarFixedPullbackFactors, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app] using exact_factors_eq_counit
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) Z

end WeilConjectures
