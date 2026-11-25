/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorComplex
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
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Scalar tensor realization on resolving representatives

Source: Stacks Tags 06YS, 07A4 and 04VK.
(blueprint: lem-sf-finite-scalar-tensor-resolution).
 -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf

universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

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

private theorem acyclicOfIso {C : Type v} [Category.{w} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (e : P ≅ Q) (hP : P.Acyclic) : Q.Acyclic := by
  intro n
  apply (HomologicalComplex.exactAt_iff_isZero_homology Q n).2
  exact ((HomologicalComplex.exactAt_iff_isZero_homology P n).1 (hP n)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e).symm

private theorem scalarAcyclicMapIff
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{w} D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.IsEquivalence]
    (K : CochainComplex C ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic ↔ K.Acyclic := by
  constructor
  · intro h i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (h i)
    have hz' : IsZero (F.obj (K.homology i)) :=
      hz.of_iso ((F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K).symm
    apply (IsZero.iff_id_eq_zero _).2
    apply F.map_injective
    rw [F.map_id, F.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 hz'
  · intro h i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    exact (F.map_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1
      (h i))).of_iso ((F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K)

/-- An exact equivalence with the specified ordinary tensor comparison preserves
acyclic-tensor K-flatness and termwise tensor exactness.
Source: Stacks 06YS and 07A4
(blueprint: lem-sf-finite-scalar-tensor-resolution). -/
theorem finiteScalarRealizationPreservesFlatKFlat
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory (CochainComplex D ℤ)]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (ht : ∀ V W : CochainComplex C ℤ,
      Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj (V ⊗ W) ≅
        (F.mapHomologicalComplex (.up ℤ)).obj V ⊗
          (F.mapHomologicalComplex (.up ℤ)).obj W))
    (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hflat : ∀ n : ℤ, exactFunctor C C (tensorRight (P.X n))) :
    (∀ Z : CochainComplex D ℤ, Z.Acyclic →
      (Z ⊗ (F.mapHomologicalComplex (.up ℤ)).obj P).Acyclic) ∧
      ∀ n : ℤ, exactFunctor D D (tensorRight (F.obj (P.X n))) := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  let E := F.asEquivalence.mapHomologicalComplex (.up ℤ)
  refine ⟨?_, ?_⟩
  · intro Z hZ
    let V := E.inverse.obj Z
    let v : FC.obj V ≅ Z := E.counitIso.app Z
    have hV : V.Acyclic := (scalarAcyclicMapIff F V).1 (acyclicOfIso v.symm hZ)
    have ha : (V ⊗ P).Acyclic := by
      have hk := (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP
      have hh := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1 hk
        ((HomotopyCategory.quotient _ _).obj V)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic V).2 hV)
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 hh.2
    have hb := (scalarAcyclicMapIff F (V ⊗ P)).2 ha
    obtain ⟨c⟩ := ht V P
    exact acyclicOfIso (c ≪≫ (tensorRight (FC.obj P)).mapIso v) hb
  · intro n
    have hC : exactFunctor C C (tensorRight (P.X n)) := hflat n
    have : PreservesFiniteLimits (tensorRight (P.X n)) := hC.1
    have : PreservesFiniteColimits (tensorRight (P.X n)) := hC.2
    have hD : exactFunctor D D (tensorRight (F.obj (P.X n))) := by
      let G := F.asEquivalence.inverse
      let b : tensorRight (P.X n) ⋙ F ≅ F ⋙ tensorRight (F.obj (P.X n)) :=
        NatIso.ofComponents (fun M ↦ e.app (M, P.X n))
          (by
            intro M M' f
            simpa using e.hom.naturality
              (X := (M, P.X n)) (Y := (M', P.X n)) (f, 𝟙 _))
      let a : G ⋙ tensorRight (P.X n) ⋙ F ≅ tensorRight (F.obj (P.X n)) :=
        isoWhiskerLeft G b ≪≫
          isoWhiskerRight F.asEquivalence.counitIso
            (tensorRight (F.obj (P.X n))) ≪≫ Functor.leftUnitor _
      exact (exactFunctor D D).prop_of_iso a (by
        change PreservesFiniteLimits (G ⋙ tensorRight (P.X n) ⋙ F) ∧
          PreservesFiniteColimits (G ⋙ tensorRight (P.X n) ⋙ F)
        exact ⟨inferInstance, inferInstance⟩)
    exact hD

/-- The exact tensor realization preserves flat-term K-flat representatives.
Source: Stacks 06YS and 07A4
(blueprint: lem-sf-finite-scalar-tensor-resolution). -/
theorem finiteScalarPreservesRepresentatives (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R] (P : CochainComplex
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (hP : finiteScalarFlatRepresentatives T R P) :
    proEtaleFlatRepresentatives T (proEtaleConstantRing T R)
      (((sfIntrinsicModuleEquivalence T R).functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  let : MonoidalCategory (proEtaleRingModules T (proEtaleConstantRing T R)) :=
    SheafOfModules.monoidalCategory.{u, u + 1, u + 1} (proEtaleConstantRing T R)
  have h := finiteScalarRealizationPreservesFlatKFlat
    (sfIntrinsicModuleEquivalence T R).functor (finiteScalarOrdinaryTensorIso T R)
    (fun V W ↦ ⟨(finiteScalarTotalTensorIso T R).app (V, W)⟩)
    P hP.1 (fun n ↦ (hP.2 n).2)
  refine ⟨h.1, fun n ↦ ?_⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
      (proEtaleConstantRing T R) _).symm (h.2 n)

/-- Extract K-flatness without unfolding the resolving predicate at specialization.
Source: Stacks 06YS (blueprint: lem-sf-finite-scalar-tensor-resolution). -/
theorem finiteScalarFlatRepresentatives_kFlat (T : Scheme.{u}) (R : Type u)
    [CommRing R] (P : CochainComplex
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (hP : finiteScalarFlatRepresentatives T R P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P := hP.1

/-- Resolving restriction is fully faithful on derived bifunctors.
Source: Stacks 04VK (blueprint: lem-sf-finite-scalar-tensor-resolution). -/
theorem finiteScalarRepresentativesFullyFaithful (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R]
    :
    Nonempty (((whiskeringLeft
      ((finiteScalarFlatRepresentatives T R).FullSubcategory ×
        (finiteScalarFlatRepresentatives T R).FullSubcategory)
      (DerivedCategory (Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} R))) ×
        DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)) ))
      (proEtaleDerivedCategory T R)).obj
      (((finiteScalarFlatRepresentatives T R).ι ⋙ DerivedCategory.Q).prod
        ((finiteScalarFlatRepresentatives T R).ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let C := Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))
  let P := finiteScalarFlatRepresentatives T R
  let H : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun Z ↦ P Z.as
  have hres : ∀ Z : HomotopyCategory C (.up ℤ),
      ∃ (W : H.FullSubcategory) (v : W.obj ⟶ Z), HomotopyCategory.quasiIso C (.up ℤ) v := by
    intro Z
    obtain ⟨W, v, hv, hf, hk⟩ := CochainComplex.exists_quasiIso_flat_kFlat Z.as
    refine ⟨⟨(HomotopyCategory.quotient C (.up ℤ)).obj W, hk, hf⟩,
      (HomotopyCategory.quotient C (.up ℤ)).map v, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff v).2 hv
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex C ℤ) (H := HomotopyCategory C (.up ℤ))
    (D := DerivedCategory C) (proEtaleDerivedCategory T R)
    (HomotopyCategory.quotient C (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso C (.up ℤ)) DerivedCategory.Qh P H (fun _ ↦ Iff.rfl) hres
  exact ⟨ff.ofIso ((whiskeringLeft _ _ (proEtaleDerivedCategory T R)).mapIso
    (NatIso.prod (isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso C))
      (isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso C))))⟩

/-- The localization tensorator is invertible on a K-flat right input.
Source: Stacks 07A4 (blueprint: lem-sf-finite-scalar-tensor-resolution). -/
theorem finiteScalarLocalizationTensor_isIso
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    [HasDerivedCategory.{w} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
    [HasColimitsOfSize.{0, 0} A]
    (P Q : CochainComplex A ℤ)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ)
  change IsIso ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  infer_instance

/-- Invert the localization tensorator on any specified class of K-flat complexes.
Source: Stacks 07A4 (blueprint: lem-sf-finite-scalar-tensor-resolution). -/
@[irreducible] def finiteScalarFixedTensorRepresentativeOfKFlat
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    [HasDerivedCategory.{w} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
    [HasColimitsOfSize.{0, 0} A]
    (P : ObjectProperty (CochainComplex A ℤ))
    (hP : ∀ Q, P Q → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    (P.ι.prod P.ι) ⋙
        uncurry.obj ((curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⋙
        DerivedCategory.Q ≅
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙
        uncurry.obj (curriedTensor (DerivedCategory A)) := by
  let v :
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙
          uncurry.obj (curriedTensor (DerivedCategory A)) ⟶
        (P.ι.prod P.ι) ⋙
          uncurry.obj ((curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⋙
          DerivedCategory.Q :=
    { app := fun Z ↦ Functor.LaxMonoidal.μ DerivedCategory.Q Z.1.obj Z.2.obj
      naturality := by
        intro X Y f
        exact (finiteScalarLaxTensorNatTrans DerivedCategory.Q).naturality
          (Prod.mkHom f.1.hom f.2.hom) }
  have : IsIso v := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    exact finiteScalarLocalizationTensor_isIso Z.1.obj Z.2.obj (hP _ Z.2.property)
  exact (asIso v).symm

/-- Specialize the localization tensorator with exactly the published coefficient API.
Source: Stacks 07A4 (blueprint: lem-sf-finite-scalar-tensor-resolution). -/
@[irreducible] def finiteScalarFixedTensorRepresentativeForCoefficients
    (B : Type u₁) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (T : Scheme.{u})
    (P : ObjectProperty (CochainComplex (Sheaf (ProEt.topology T) B) ℤ))
    (hP : ∀ Q, P Q → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    (P.ι.prod P.ι) ⋙
        uncurry.obj ((curriedTensor (Sheaf (ProEt.topology T) B)).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙
        uncurry.obj (ProEtale.derivedTensor B T) :=
  finiteScalarFixedTensorRepresentativeOfKFlat P hP

end WeilConjectures
