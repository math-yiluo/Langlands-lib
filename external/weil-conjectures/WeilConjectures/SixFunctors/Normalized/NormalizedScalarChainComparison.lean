/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarHomTensor.PrescribedScalarTensorComparison
import all WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
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

/-! # Normalized scalar comparison on total cochain tensors -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules CategoryTheory.MonoidalCategory CategoryTheory.Functor
open CategoryTheory.ScalarHomTensor
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory

namespace WeilConjectures

universe c₁ v₁ r w

/-- Scalar extension commutes with total tensor, with its unit normalization.
Source: Stacks 03EK and 07A4.
Proof: totalize the inverse ordinary scalar tensor comparison. The left adjunction
makes scalar extension preserve coproducts, so the totalized map is invertible.
Its naturality follows on each summand. Unit naturality and the ordinary pure-tensor
formula identify its inverse on homogeneous generators. Apply the inverse once more
to obtain the stated formula.
(blueprint: lem-sf-normalized-scalar-chain-comparison). -/
theorem normalizedScalarChainComparison
    {C : Type c₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{max c₁ v₁ r} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{max c₁ v₁ r} RingCat.{max c₁ v₁ r})]
    [HasSheafify J AddCommGrpCat.{max c₁ v₁ r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c₁ v₁ r}]
    {R S : Sheaf J CommRingCat.{max c₁ v₁ r}}
    [∀ T : Sheaf J CommRingCat.{max c₁ v₁ r},
      HasDerivedCategory.{w} (scalarModules J T)]
    (c : R ⟶ S) (s : ScalarDerivedPair c) :
    ∃ b : coefficientTotalTensor.{r, c₁, v₁} J R ⋙
        scalarComplex s.extension s.extension_additive ≅
      ((scalarComplex s.extension s.extension_additive).prod
        (scalarComplex s.extension s.extension_additive)) ⋙ coefficientTotalTensor.{r, c₁, v₁} J S,
    ∀ (P Q : CochainComplex (scalarModules J R) ℤ) (p q k : ℤ) (h : p + q = k)
      (V : Cᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      ((b.app (P, Q)).inv.f k).val.app V
          (coefficientTensorGenerator.{r, c₁, v₁} J S
            ((scalarComplex s.extension s.extension_additive).obj P)
            ((scalarComplex s.extension s.extension_additive).obj Q) p q k h V
            (pairUnit.{c₁, v₁, r, w} c s _ V x)
            (pairUnit.{c₁, v₁, r, w} c s _ V y)) =
        pairUnit.{c₁, v₁, r, w} c s _ V
          (coefficientTensorGenerator.{r, c₁, v₁} J R P Q p q k h V x y) := by
  classical
  let A := scalarModules J R
  let B := scalarModules J S
  let := monoidalCategory R
  let := monoidalCategory S
  let := s.extension_additive
  let : MonoidalPreadditive A := cochainModulesPreadditive R
  let : MonoidalPreadditive B := cochainModulesPreadditive S
  obtain ⟨e, he, hgen⟩ :=
    SheafOfModules.ScalarHomOrdinary.scalarOrdinaryTensorComparison_exists
      c s
  let F := scalarComplex.{c₁, v₁, max c₁ v₁ r} (J := J) (R := R) (S := S)
    s.extension s.extension_additive
  let tR := coefficientTotalTensor.{r, c₁, v₁} J R
  let tS := coefficientTotalTensor.{r, c₁, v₁} J S
  let U : B ⥤ A := scalarRestriction.{c₁, v₁, max c₁ v₁ r} c
  have am : s.extension ⊣ U := s.ordinaryAdjunction
  have hiso (P Q : CochainComplex A ℤ) :
      IsIso (tensorPullbackTotal s.extension e he P Q) :=
    tensorPullbackTotal_isIso s.extension e he U am P Q
  let b0 : (F.prod F) ⋙ tS ≅ tR ⋙ F := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (tensorPullbackTotal s.extension e he X.1 X.2)
      (hiso X.1 X.2)) (by
        intro X Y f
        dsimp only [F, tR, tS, scalarComplex, Functor.comp_map, Functor.prod_map]
        simp only [coefficientTotalTensor, Functor.uncurry_obj_map,
          Functor.map₂HomologicalComplex, tensorMap_factor]
        exact tensorPullbackTotal_naturality s.extension e he f.1 f.2)
  let b := b0.symm
  have hg (P Q : CochainComplex A ℤ) (p q k : ℤ) (h : p + q = k)
      (V : Cᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
      ((b.app (P, Q)).hom.f k).val.app V
          ((s.ordinaryAdjunction.unit.app _).val.app V
            (coefficientTensorGenerator.{r, c₁, v₁} J R P Q p q k h V x y)) =
        coefficientTensorGenerator.{r, c₁, v₁} J S (F.obj P) (F.obj Q) p q k h V
          ((s.ordinaryAdjunction.unit.app _).val.app V x)
          ((s.ordinaryAdjunction.unit.app _).val.app V y) := by
    let ι := CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q k h
    let ι' := CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q) (curriedTensor B) p q k h
    let z := (HomologicalComplex.eval B (.up ℤ) k).mapIso (b0.app (P, Q))
    have hz : ι' ≫ z.hom = (e (P.X p) (Q.X q)).inv ≫ s.extension.map ι := by
      change ι' ≫ tensorPullbackTotalComponent s.extension e P Q k = _
      exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
    have hi : s.extension.map ι ≫ z.inv = (e (P.X p) (Q.X q)).hom ≫ ι' := by
      apply (cancel_mono z.hom).mp
      erw [Category.assoc, z.inv_hom_id, Category.comp_id, Category.assoc, hz,
        Iso.hom_inv_id_assoc]
    have hu := congrArg (fun f ↦ f.val.app V
      (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))
      (s.ordinaryAdjunction.unit.naturality ι)
    have hh := congrArg (fun f ↦ f.val.app V
      (((s.ordinaryAdjunction.unit.app _).val.app V)
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) hi
    change z.inv.val.app V
      (((s.ordinaryAdjunction.unit.app _).val.app V)
        (ι.val.app V (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) = _
    change ((s.ordinaryAdjunction.unit.app _).val.app V)
      (ι.val.app V (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) =
      (s.extension.map ι).val.app V (((s.ordinaryAdjunction.unit.app _).val.app V)
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) at hu
    erw [hu]
    exact hh.trans (congrArg (ι'.val.app V) (hgen _ _ V x y))
  refine ⟨b, ?_⟩
  intro P Q p q k h V x y
  dsimp only [pairUnit]
  rw [← hg P Q p q k h V x y]
  exact congrArg (fun f ↦ (f.f k).val.app V
    ((s.ordinaryAdjunction.unit.app _).val.app V
      (coefficientTensorGenerator.{r, c₁, v₁} J R P Q p q k h V x y)))
    (b.app (P, Q)).hom_inv_id

end WeilConjectures
