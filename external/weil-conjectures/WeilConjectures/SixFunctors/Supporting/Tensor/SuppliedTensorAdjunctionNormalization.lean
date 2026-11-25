/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Normalizing the scalar-extension adjunction for a supplied direct image

Source: Stacks Project, Modules on Sites, Tag 03D7.
(blueprint: lem-sfb-supplied-tensor-adjunction-normalization).
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
open SheafOfModules.GeometricConstruction

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000

/-- The geometric mate bijection restricts to scalar-linear morphisms. -/
private theorem suppliedTensor_mate_linear_iff
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K)
      (base A) (base B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      I.ringUnderlying.inv ≫ f.ringMap)
    (M : SheafOfModules.{u} (base B)) (H : SheafOfModules.{u} (base A))
    (α : (mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) :
    (∃ a : I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map c)).obj H, (mset RI).map a = α) ↔
      ∃ b : M ⟶ f.modules.obj H, (mset B).map b =
        mateIsoEquiv f.adj (I.moduleUnderlying.app M) (f.underlying.app H) α := by
  let _ := f.leftExact
  let _ : PreservesLimits f.direct := f.adj.rightAdjoint_preservesLimits
  let eR := I.ringUnderlying.symm
  let eI := I.moduleUnderlying
  let eP := f.underlying
  have hec : eR.inv ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      f.ringMap := by
    rw [hc]
    simp only [eR, Iso.symm_inv, Iso.hom_inv_id_assoc]
  let E : ∀ M H, ((mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) ≃
      ((mset B).obj M ⟶ (mset B).obj (f.modules.obj H)) :=
    fun M H ↦ mateIsoEquiv f.adj (eI.app M) (eP.app H)
  have hLA : f.inverse.map (madd B M) =
      prodComparison f.inverse ((mset B).obj M) ((mset B).obj M) ≫
        prod.map (eI.inv.app M) (eI.inv.app M) ≫ madd RI (I.modules.obj M) ≫
          eI.hom.app M := by
    apply (cancel_mono (eI.inv.app M)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact binary_of_graph f.inverse (eI.inv.app M) (eI.inv.app M) (eI.inv.app M)
      (madd B M) (madd RI (I.modules.obj M))
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add ((I.modules.obj M).val.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ I.moduleAdd M T x y z hz U t)
  have hLS : f.inverse.map (msmul B M) =
      prodComparison f.inverse (rset B) ((mset B).obj M) ≫
        prod.map eR.inv (eI.inv.app M) ≫ msmul RI (I.modules.obj M) ≫ eI.hom.app M := by
    apply (cancel_mono (eI.inv.app M)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact binary_of_graph f.inverse eR.inv (eI.inv.app M) (eI.inv.app M)
      (msmul B M) (msmul RI (I.modules.obj M))
      (fun U x y ↦ @SMul.smul (B.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @SMul.smul (RI.obj.obj U) ((I.modules.obj M).val.obj U)
        inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T a x z hz U t ↦ I.moduleSMul M T a x z hz U t)
  have hRightAdd := (h4_supplied_operations f H).1
  have hRightSmul := (h4_supplied_operations f H).2
  rw [← hec] at hRightSmul
  have hm : f.adj.homEquiv _ _ (eI.inv.app M ≫ α) = E M H α ≫ eP.hom.app H :=
    mateIsoEquiv_equation f.adj (eI.app M) (eP.app H) α
  have hAdd := binary_mate_iso_iff f.adj (eI.app M) (eI.app M) (eI.app M)
    (eP.hom.app H) (eP.hom.app H) (eP.app H) (madd B M)
    (madd RI (I.modules.obj M)) (madd A H) (madd B (f.modules.obj H))
    hLA hRightAdd α α α (E M H α) (E M H α) (E M H α) hm hm hm
  have hSmul := binary_mate_iso_iff f.adj eR (eI.app M) (eI.app M)
    (f.adj.homEquiv _ _ (eR.inv ≫ (sheafCompose J
      (CategoryTheory.forget CommRingCat.{u})).map c))
    (eP.hom.app H) (eP.app H) (msmul B M) (msmul RI (I.modules.obj M))
    (msmul A H) (msmul B (f.modules.obj H)) hLS hRightSmul
    ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c) α α
    (𝟙 (rset B)) (E M H α) (E M H α)
    (by exact (Category.id_comp _).symm) hm hm
  have hSame := linear_iff (𝟙 B) M (f.modules.obj H)
    (madd B M) (madd B (f.modules.obj H)) (msmul B M) (msmul B (f.modules.obj H))
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (E M H α)
  exact (linear_iff c (I.modules.obj M) H (madd RI (I.modules.obj M)) (madd A H)
    (msmul RI (I.modules.obj M)) (msmul A H)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) α).trans
      ((and_congr hAdd hSmul).trans hSame.symm)

-- Restriction of the geometric Hom bijection compares the additive and scalar operations.
/-- Scalar extension is adjoint to the supplied module direct image, with the underlying
Hom bijection fixed by the canonical insertion.
Source: Stacks Project, Modules on Sites, Tag 03D7.
(blueprint: lem-sfb-supplied-tensor-adjunction-normalization).

Proof: the geometric sheaf Hom bijection identifies additive and scalar-linear maps
on both sides, using the structural ring-map equality and the supplied direct-image
action. Restrict that bijection to module morphisms and compose with the
extension/restriction-of-scalars adjunction. Naturality gives an adjunction.
Its Hom bijection on underlying sheaves is the geometric mate after insertion of
one into the tensor factor: both the scalar-adjunction unit and the given q have
this sectionwise formula. -/
private theorem privateSuppliedTensorAdjunction_normalized
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K)
      (base A) (base B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      I.ringUnderlying.inv ≫ f.ringMap) :
    ∃ am : I.modules ⋙ tensorFunctor c ⊣ f.modules,
      ∀ (M : SheafOfModules.{u} (base B))
        (H : SheafOfModules.{u} (base A))
        (v : (I.modules ⋙ tensorFunctor c).obj M ⟶ H),
        (mset B).map (am.homEquiv M H v) ≫ f.underlying.hom.app H =
          f.adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫ tensorUnit c (I.modules.obj M) ≫
            (mset A).map v) := by
  let eI := I.moduleUnderlying
  let eP := f.underlying
  let E : ∀ M H, ((mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) ≃
      ((mset B).obj M ⟶ (mset B).obj (f.modules.obj H)) :=
    fun M H ↦ mateIsoEquiv f.adj (eI.app M) (eP.app H)
  let B' : ∀ M H, (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map c)).obj H) ≃ (M ⟶ f.modules.obj H) :=
    fun M H ↦ restrictHomEquiv (mset RI) (mset B) (E M H)
      (suppliedTensor_mate_linear_iff f RI I c hc M H)
  have hB M H a : (mset B).map (B' M H a) ≫ eP.hom.app H =
      f.adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) := by
    rw [restrictHomEquiv_map]
    exact (mateIsoEquiv_equation f.adj (eI.app M) (eP.app H) _).symm
  have hBL {M N} (a : M ⟶ N) H b :
      B' M H (I.modules.map a ≫ b) = a ≫ B' N H b := by
    apply (mset B).map_injective
    apply (cancel_mono (eP.hom.app H)).mp
    have hn : eI.inv.app M ≫ (mset RI).map (I.modules.map a) =
        f.inverse.map ((mset B).map a) ≫ eI.inv.app N := (eI.inv.naturality a).symm
    calc
      _ = f.adj.homEquiv _ _ (eI.inv.app M ≫
          (mset RI).map (I.modules.map a ≫ b)) := hB M H _
      _ = (mset B).map a ≫
          f.adj.homEquiv _ _ (eI.inv.app N ≫ (mset RI).map b) := by
        rw [(mset RI).map_comp, ← Category.assoc, hn, Category.assoc,
          f.adj.homEquiv_naturality_left]
      _ = _ := by simp only [Functor.map_comp, Category.assoc, hB]
  have hBR M {H H'} a (b : H ⟶ H') :
      B' M H' (a ≫ (restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).map c)).map b) = B' M H a ≫ f.modules.map b := by
    apply (mset B).map_injective
    apply (cancel_mono (eP.hom.app H')).mp
    have hn : (mset B).map (f.modules.map b) ≫ eP.hom.app H' =
        eP.hom.app H ≫ f.direct.map ((mset A).map b) := eP.hom.naturality b
    calc
      _ = f.adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map
          (a ≫ (restrictScalars ((sheafCompose J
            (forget₂ CommRingCat.{u} RingCat.{u})).map c)).map b)) := hB M H' _
      _ = f.adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) ≫
          f.direct.map ((mset A).map b) := by
        rw [(mset RI).map_comp]
        change f.adj.homEquiv _ _ (eI.inv.app M ≫
          ((mset RI).map a ≫ (mset A).map b)) = _
        rw [← Category.assoc, f.adj.homEquiv_naturality_right]
      _ = ((mset B).map (B' M H a) ≫ eP.hom.app H) ≫
          f.direct.map ((mset A).map b) :=
        congrArg (fun g ↦ g ≫ f.direct.map ((mset A).map b)) (hB M H a).symm
      _ = _ := by simp only [Functor.map_comp, Category.assoc, hn]
  let T := I.modules ⋙ tensorFunctor c
  let E' : ∀ M H, (T.obj M ⟶ H) ≃ (M ⟶ f.modules.obj H) :=
    fun M H ↦ ((tensorAdjunction c).homEquiv (I.modules.obj M) H).trans (B' M H)
  have hEL {M N} (a : M ⟶ N) H (b : T.obj N ⟶ H) :
      E' M H (T.map a ≫ b) = a ≫ E' N H b := by
    exact (congrArg (B' M H)
      ((tensorAdjunction c).homEquiv_naturality_left (I.modules.map a) b)).trans
      (hBL a H _)
  let am : T ⊣ f.modules := Adjunction.mkOfHomEquiv {
    homEquiv := E'
    homEquiv_naturality_left_symm := by
      intro M N H a b
      apply (E' M H).injective
      rw [Equiv.apply_symm_apply, hEL, Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro M H H' a b
      dsimp only [E', Equiv.trans_apply]
      change B' M H' ((tensorAdjunction c).homEquiv (I.modules.obj M) H' (a ≫ b)) = _
      rw [(tensorAdjunction c).homEquiv_naturality_right]
      exact hBR M ((tensorAdjunction c).homEquiv (I.modules.obj M) H a) b }
  refine ⟨am, ?_⟩
  intro M H v
  dsimp only [am]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  change (mset B).map
    (B' M H ((tensorAdjunction c).homEquiv (I.modules.obj M) H v)) ≫
      eP.hom.app H = _
  exact (hB M H _).trans (congrArg (fun a ↦ f.adj.homEquiv _ _ (eI.inv.app M ≫ a))
    (tensorAdjunction_underlying c (I.modules.obj M) H v))

-- Transporting the scalar-extension presentation uses dependent functor equalities.
/-- The scalar-extension normalization is unchanged by a specified presentation of
its objects and maps.
Source: Stacks Project, Modules on Sites, Tag 03D7.
(blueprint: lem-sfb-supplied-tensor-adjunction-normalization).

Proof: identify the supplied pullback with the literal scalar-extension functor
using its object and map equations. Transport the normalized adjunction through
this natural isomorphism. Both insertion maps send a section to one tensor that
section; the object identification therefore carries one insertion to the other. -/
theorem suppliedTensorAdjunction_normalized
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism (RingedTensor.ringSheaf A) (RingedTensor.ringSheaf B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      I.ringUnderlying.inv ≫ f.ringMap)
    (L : SheafOfModules.{u} (RingedTensor.ringSheaf B) ⥤
      SheafOfModules.{u} (RingedTensor.ringSheaf A))
    (hobj : ∀ M, L.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N} (a : M ⟶ N), L.map a = eqToHom (hobj M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparison B A RI f.inverse I c L hobj) :
    ∃ am : L ⊣ f.modules,
      ∀ (M : SheafOfModules.{u} (RingedTensor.ringSheaf B))
        (H : SheafOfModules.{u} (RingedTensor.ringSheaf A)) (v : L.obj M ⟶ H),
        (RingedTensor.underlying B).map (am.homEquiv M H v) ≫ f.underlying.hom.app H =
          f.adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫ k.q M ≫
            (RingedTensor.underlying A).map v) := by
  let _ := f.leftExact
  let T := I.modules ⋙ tensorFunctor c
  obtain ⟨am, ham⟩ := privateSuppliedTensorAdjunction_normalized f RI I c hc
  let e : T ≅ L := NatIso.ofComponents (fun M ↦ (eqToIso (hobj M)).symm) (by
    intro M N a
    change T.map a ≫ eqToHom (hobj N).symm = eqToHom (hobj M).symm ≫ L.map a
    rw [hmap, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rfl)
  refine ⟨am.ofNatIsoLeft e, ?_⟩
  intro M H v
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, ham, (mset A).map_comp]
  have hq : tensorUnit c (I.modules.obj M) ≫ (mset A).map (e.hom.app M) = k.q M := by
    ext W x
    change (e.hom.app M).val.app W ((tensorUnit c (I.modules.obj M)).hom.app W x) = _
    rw [tensorUnit_apply]
    exact (k.q_one M W x).symm
  apply congrArg (f.adj.homEquiv _ _)
  exact congrArg (fun a ↦ I.moduleUnderlying.inv.app M ≫ a)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun a ↦ a ≫ (mset A).map v) hq))
