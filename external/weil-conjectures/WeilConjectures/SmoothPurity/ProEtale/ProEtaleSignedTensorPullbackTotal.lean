/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
import all WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Signed total tensor and ordinary pullback

Source: Stacks 07A4 and 0FNG, item-flip-tensor-product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u a b v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Limits
open scoped MonoidalCategory
namespace WeilConjectures
attribute [local implicit_reducible] Functor.map₂HomologicalComplex
attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction SheafOfModules.tensorObjIsoSheafification
  CochainComplex.Monoidal.braiding tensorPullbackTotal tensorPullbackTotalComponent

private theorem ordinarySignedSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M N : proEtaleRingModules Y R) :
    let L := proEtaleRingModulePullback f R S c
    let μ := proEtaleOrdinaryTensorPullback f R S c
    L.map (β_ M N).hom ≫ (μ N M).hom =
      (μ M N).hom ≫ (β_ (L.obj M) (L.obj N)).hom := by
  let L := proEtaleRingModulePullback f R S c
  let μ := proEtaleOrdinaryTensorPullback f R S c
  let adj := proEtaleRingModuleAdjunction f R S c
  have hμ := (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists.choose_spec.2
  have hpure (W : Scheme.{u}) (A : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
      (M N : proEtaleRingModules W A) (U : W.ProEtᵒᵖ)
      (x : M.val.obj U) (y : N.val.obj U) :
      (β_ M N).hom.val.app U (proEtaleTensorPair W A M N U x y) =
        proEtaleTensorPair W A N M U y x := by
    exact CategoryTheory.CochainPullback.moduleTmul_braiding M N U x y
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  have hu := adj.unit.naturality (β_ M N).hom
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← hu]
  apply AlgebraicGeometry.Scheme.tensor_hom_ext Y R
  intro U x y
  change (μ N M).hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U.unop))
      ((adj.unit.app (N ⊗ M)).val.app U
        ((β_ M N).hom.val.app U (proEtaleTensorPair Y R M N U x y))) =
    (β_ (L.obj M) (L.obj N)).hom.val.app
      (Opposite.op ((proEtaleBaseChange f).obj U.unop))
      ((μ M N).hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U.unop))
        ((adj.unit.app (M ⊗ N)).val.app U (proEtaleTensorPair Y R M N U x y)))
  rw [hpure]
  have hl := hμ N M U.unop y x
  have hr := congrArg ((β_ (L.obj M) (L.obj N)).hom.val.app
    (Opposite.op ((proEtaleBaseChange f).obj U.unop))) (hμ M N U.unop x y)
  exact hl.trans ((hpure X S (L.obj M) (L.obj N)
    (Opposite.op ((proEtaleBaseChange f).obj U.unop)) _ _).symm.trans hr.symm)

private theorem totalSignedSquare
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    [Abelian A] [Abelian B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [BraidedCategory A] [BraidedCategory B]
    [∀ X : A, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
    [∀ X : A, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
    [∀ X : B, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
    [∀ X : B, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (μ : ∀ M N : A, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
    (hμ : ∀ {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g))
    (hβ : ∀ M N : A, L.map (β_ M N).hom ≫ (μ N M).hom =
      (μ M N).hom ≫ (β_ (L.obj M) (L.obj N)).hom)
    (P Q : CochainComplex A ℤ) :
    let F := L.mapHomologicalComplex (.up ℤ)
    tensorPullbackTotal L μ hμ P Q ≫ F.map (CochainComplex.Monoidal.braiding P Q).hom =
      (CochainComplex.Monoidal.braiding (F.obj P) (F.obj Q)).hom ≫
        tensorPullbackTotal L μ hμ Q P := by
  let F := L.mapHomologicalComplex (.up ℤ)
  have hβ' (M N : A) : (μ M N).inv ≫ L.map (β_ M N).hom =
      (β_ (L.obj M) (L.obj N)).hom ≫ (μ N M).inv := by
    apply (cancel_mono (μ N M).hom).1
    rw [Category.assoc, hβ, Iso.inv_hom_id_assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [tensorPullbackTotal]
  change _ ≫ tensorPullbackTotalComponent L μ P Q n ≫
      L.map ((CochainComplex.Monoidal.braiding P Q).hom.f n) =
    _ ≫ (CochainComplex.Monoidal.braiding (F.obj P) (F.obj Q)).hom.f n ≫
      tensorPullbackTotalComponent L μ Q P n
  rw [tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc_assoc,
    CochainComplex.Monoidal.ι_braiding_hom_assoc]
  simp only [HomologicalComplex.ιTensorObj]
  unfold tensorPullbackTotalComponent
  simp only [Preadditive.zsmul_comp, Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorDesc]
  rw [← L.map_comp, CochainComplex.Monoidal.ι_braiding_hom, L.map_zsmul]
  simp only [Preadditive.comp_zsmul, L.map_comp, ← Category.assoc, hβ']
  rfl

private theorem signedTotal_native (W : Scheme.{u})
    (A : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (P Q : CochainComplex (proEtaleRingModules W A) ℤ) :
    (pullbackTensorSignedTotal (ProEt.topology W) A P Q).hom =
      (CochainComplex.Monoidal.braiding P Q).hom := by
  rw [pullbackTensorSignedTotal_eq]
  rfl

/-- Ordinary termwise pullback commutes with the signed total exchange.
Source: Stacks 07A4, final displayed total map, and 0FNG, item-flip-tensor-product.
(blueprint: lem-pur-proetale-signed-tensor-pullback-total).
Proof: restrict to the summand of bidegree (p,q). The ordinary pullback comparison
sends the unit section of x tensor y to the tensor of the two unit sections.
Both composites therefore send this generator to (-1)^(p*q) times the flipped
tensor. The ordinary maps are linear, including for negative integer degrees.
The adjunction, tensor sheafification, and coproduct injections detect equality,
so the total chain maps agree. Compose with the two inverse total comparisons
to obtain the displayed equation. No K-flatness or flat terms are required. -/
theorem proEtaleSignedTensorPullbackTotal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    let L := (proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)
    L.map (pullbackTensorSignedTotal (ProEt.topology Y) R P Q).hom ≫
        (proEtaleTensorPullbackTotalIso f R S c Q P).inv =
      (proEtaleTensorPullbackTotalIso f R S c P Q).inv ≫
        (pullbackTensorSignedTotal (ProEt.topology X) S (L.obj P) (L.obj Q)).hom := by
  let L := proEtaleRingModulePullback f R S c
  let F := L.mapHomologicalComplex (.up ℤ)
  let μ := proEtaleOrdinaryTensorPullback f R S c
  have hμ {M M' N N' : proEtaleRingModules Y R} (v : M ⟶ M') (z : N ⟶ N') :
      L.map (v ⊗ₘ z) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map v ⊗ₘ L.map z) := by
    simpa only [proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor,
      MonoidalCategory.tensorHom_def, Category.assoc] using
      proEtaleOrdinaryTensorPullback_naturality f R S c M M' N N' v z
  have h := totalSignedSquare L μ hμ (ordinarySignedSquare f R S c) P Q
  have hn : proEtaleTensorPullbackTotal f R S c P Q ≫
      F.map (pullbackTensorSignedTotal (ProEt.topology Y) R P Q).hom =
    (pullbackTensorSignedTotal (ProEt.topology X) S (F.obj P) (F.obj Q)).hom ≫
      proEtaleTensorPullbackTotal f R S c Q P := by
    simpa only [signedTotal_native, proEtaleTensorPullbackTotal, L, F, μ] using h
  dsimp only
  apply (cancel_epi (proEtaleTensorPullbackTotalIso f R S c P Q).hom).1
  apply (cancel_mono (proEtaleTensorPullbackTotalIso f R S c Q P).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [proEtaleTensorPullbackTotalIso, asIso_hom] using hn

end WeilConjectures
