/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PointDerivedHom.PointDerivedHomModels
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
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
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Sheaf evaluation and tensoring sections at a point

Source: Stacks Project, Tags 0A8X and 08J7.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.PointDerivedHom

variable (k : Type t) [Field k]
  {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)
  (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
  (hobj : ∀ M : ModuleCat.{max u (t + 1)} R,
    L.obj M = extensionObject.{t, u} k B α M)
  (adj : L ⊣ sections.{t, u} k B α)
  (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)

namespace EvaluationConstruction

open CategoryTheory.MonoidalCategory
open SheafOfModules.CochainScalarConstruction
open scoped TensorProduct

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
  PresheafOfModules.sheafification

local instance (priority := 10000) : MonoidalCategory (Modules.{t, u} k B) :=
  SheafOfModules.monoidalCategory B

local instance : HasColimitsOfSize.{0, 0} (Modules.{t, u} k B) :=
  IntegralHom.countableColimits (Spec (.of k)) B

local instance (P Q : CochainComplex (Modules.{t, u} k B) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q
      (IntegralHom.ordinaryTensor.{t, u} (Spec (.of k)) B) (.up ℤ) := by
  infer_instance

variable (P I : CochainComplex (Modules.{t, u} k B) ℤ)

private def value (p j n : ℤ) (hpj : p + j = n)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
    (h : ((sheafHom.{t, u} k B P I).X j).val.obj U)
    (x : (P.X p).val.obj U) : (I.X n).val.obj U :=
  (((homComplexπ.{t + 1, t, max u (t + 1), max u (t + 1)}
    (R := B) P I j p n hpj).val.app U h).app
    (op (Over.mk (𝟙 U.unop)))).hom x

private def term (p j n : ℤ) (hpj : p + j = n) :
    P.X p ⊗ (sheafHom.{t, u} k B P I).X j ⟶ I.X n :=
  let π := homComplexπ.{t + 1, t, max u (t + 1), max u (t + 1)} (R := B) P I j p n hpj
  let a := PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 (ring.{t, u} k B).obj)
  (p * j).negOnePow • ((SheafOfModules.tensorObjIsoSheafification
    (P.X p) ((sheafHom.{t, u} k B P I).X j)).hom ≫
      (a.homEquiv _ (I.X n)).symm (CategoryTheory.IsoTensorHom.tensorHomUncurry.{t + 1, t, u}
        (R := B.obj) (M := (P.X p).val)
        (P := ((sheafHom.{t, u} k B P I).X j).val) (N := (I.X n).val) π.val))

attribute [local irreducible] term

private def degree (n : ℤ) : (total.{t, u} k B P (sheafHom.{t, u} k B P I)).X n ⟶ I.X n :=
  HomologicalComplex.mapBifunctorDesc (fun p j hpj ↦ term k B P I p j n hpj)

attribute [local irreducible] degree

attribute [local irreducible] value

end EvaluationConstruction

namespace SectionsTensorConstruction

open CategoryTheory.MonoidalCategory
open SheafOfModules.CochainScalarConstruction
open scoped TensorProduct

attribute [local irreducible] SheafOfModules.monoidalCategory

local instance (priority := 10000) : MonoidalCategory (Modules.{t, u} k B) :=
  SheafOfModules.monoidalCategory B

local instance : HasColimitsOfSize.{0, 0} (Modules.{t, u} k B) :=
  IntegralHom.countableColimits.{t, u} (Spec (.of k)) B

private def bilin (M N : Modules.{t, u} k B) :
    (sections.{t, u} k B α).obj M →ₗ[R]
      (sections.{t, u} k B α).obj N →ₗ[R]
        (sections.{t, u} k B α).obj (M ⊗ N) where
  toFun x :=
    { toFun := fun y ↦ pure B M N (op (finalObject k)) x y
      map_add' := fun y z ↦ pure_add_right B M N _ x y z
      map_smul' := by
        intro r y
        change pure B M N (op (finalObject k)) x
          (scalar.{t, u} k B α (op (finalObject k)) r •
            (show N.val.obj (op (finalObject k)) from y)) =
          scalar.{t, u} k B α (op (finalObject k)) r • pure B M N (op (finalObject k)) x y
        exact pure_smul_right B M N _ _ x y }
  map_add' x y := by
    ext z
    exact pure_add_left B M N _ x y z
  map_smul' r x := by
    ext y
    change pure B M N (op (finalObject k))
      (scalar.{t, u} k B α (op (finalObject k)) r •
        (show M.val.obj (op (finalObject k)) from x)) y =
      scalar.{t, u} k B α (op (finalObject k)) r • pure B M N (op (finalObject k)) x y
    exact pure_smul_left B M N _ _ x y

private def component (M N : Modules.{t, u} k B) :
    (sections.{t, u} k B α).obj M ⊗ (sections.{t, u} k B α).obj N ⟶
      (sections.{t, u} k B α).obj (M ⊗ N) :=
  ModuleCat.homEquiv.symm (TensorProduct.lift (bilin k B α M N))

private theorem component_natural
    {M M' N N' : Modules.{t, u} k B} (f : M ⟶ M') (g : N ⟶ N') :
    component k B α M N ≫ (sections.{t, u} k B α).map (f ⊗ₘ g) =
      ((sections.{t, u} k B α).map f ⊗ₘ (sections.{t, u} k B α).map g) ≫
        component k B α M' N' := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact pure_map B f g (op (finalObject k)) x y

private def chain (P H : CochainComplex (Modules.{t, u} k B) ℤ) :
    moduleTotal ((sectionComplex.{t, u} k B α).obj P)
      ((sectionComplex.{t, u} k B α).obj H) ⟶
        (sectionComplex.{t, u} k B α).obj (total.{t, u} k B P H) :=
  { f := CategoryTheory.CochainPullback.laxTotalComponent
      (sections.{t, u} k B α) (component k B α) P H
    comm' := fun n m _ ↦ CategoryTheory.CochainPullback.laxTotalComponent_comm
      (sections.{t, u} k B α) (component k B α) (component_natural k B α) P H n m }

private def beta (H : CochainComplex (Modules.{t, u} k B) ℤ) :
    moduleTotal c ((sectionComplex.{t, u} k B α).obj H) ⟶
      (sectionComplex.{t, u} k B α).obj
        (total.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) H) :=
  letI := adj.left_adjoint_additive
  HomologicalComplex.mapBifunctorMap
    ((adj.mapHomologicalComplex (.up ℤ)).unit.app c) (𝟙 _)
      (curriedTensor _) (.up ℤ) ≫ chain k B α _ H

end SectionsTensorConstruction

end WeilConjectures.PointDerivedHom
