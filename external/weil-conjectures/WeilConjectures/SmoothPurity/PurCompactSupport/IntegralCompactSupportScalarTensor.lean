/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-! # Normalized scalar tensor comparison for compact support

The self-contained tensor construction formerly in IntegralCompactSupportCoefficientComparison.
Source: Stacks Tags 03EL, 06YY, 07A4.
(blueprint: def-sf-compact-support-scalar-tensor-balancing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings MonoidalCategory TensorProduct
namespace WeilConjectures.PurCompactSupport
attribute [local instance 100000] CategoryTheory.HasSheafify.isRightAdjoint
  CategoryTheory.Limits.HasColimitsOfShape.has_colimit
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
attribute [local irreducible] CategoryTheory.presheafToSheaf CategoryTheory.Functor.leftAdjoint
  SheafOfModules.monoidalCategory SheafOfModules.tensorObjIsoSheafification
  AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
  AlgebraicGeometry.Scheme.completedAdicChange AlgebraicGeometry.Scheme.reductionChange
  CategoryTheory.Localization.Monoidal.tensorBifunctor
  HasDerivedCategory.standard CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HomologicalComplex₂.total
  CategoryTheory.Functor.mapBifunctorHomologicalComplex

-- Use the canonical concrete site instances throughout this proof context.
/-- Canonical smallness of the coefficient site.
Source: the existing integral coefficient site instances.
(blueprint: def-sf-compact-support-scalar-tensor-balancing). -/
theorem coefficientSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance 100000] coefficientSiteSmall

/-- Canonical ring sheafification on the coefficient site.
Source: the existing integral coefficient site instances.
(blueprint: def-sf-compact-support-scalar-tensor-balancing). -/
theorem coefficientRingSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, 0} W

attribute [local instance 100000] coefficientRingSheafify

/-- Canonical abelian sheafification on the coefficient site.
Source: the existing integral coefficient site instances.
(blueprint: def-sf-compact-support-scalar-tensor-balancing). -/
theorem coefficientAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} W

attribute [local instance 100000] coefficientAbSheafify

/-- Canonical local bijectivity criterion on the coefficient site.
Source: the existing integral coefficient site instances.
(blueprint: def-sf-compact-support-scalar-tensor-balancing). -/
theorem coefficientAbLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} W

attribute [local instance 100000] coefficientAbLocallyBijective

/-- Every coefficient sheaf has a model of its actual derived tensor.
Source: Stacks Tag 07A4
(blueprint: def-sf-compact-support-scalar-tensor-balancing).
Proof: choose flat K-flat resolutions of both variables and use the signed direct-sum
total tensor. Quasi-isomorphisms between these representatives are inverted by tensor.
Localization in both variables descends this functor and gives its representative
isomorphism. This is precisely the published ProEtaleTensorModel interface. -/
theorem tensorModel_exists (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    Nonempty (ProEtaleTensorModel W R) := by
  refine ⟨{ tensor := ?_, representative := ?_ }⟩
  · exact @MonoidalCategory.tensor _ _
      (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology W) R)
  · exact NatIso.ofComponents
      (fun P ↦ RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
        (ProEt.topology W) R P.1.obj P.2.obj (Or.inl P.1.property.1))
      (fun f ↦ RingedDerivedNative.tensorIso_naturality.{u + 1, u, 0, u + 2}
        (ProEt.topology W) R _ _ _ _ _ _ f.1.hom f.2.hom)

private theorem tensorPair_eq_pure {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (M N : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    proEtaleTensorPair W R M N U x y =
      SheafOfModules.ScalarHomOrdinary.pure.{u + 1, u, u + 1} R M N U x y := by
  rfl

private theorem tensorPair_map {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    {M M' N N' : pbcModules W R} (v : M ⟶ M') (z : N ⟶ N')
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((((proEtaleOrdinaryTensor W R).map v).app N ≫
        ((proEtaleOrdinaryTensor W R).obj M').map z).val.app U)
        (proEtaleTensorPair W R M N U x y) =
      proEtaleTensorPair W R M' N' U (v.val.app U x) (z.val.app U y) := by
  simpa only [proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor,
    MonoidalCategory.tensorHom_def, ← tensorPair_eq_pure] using
      SheafOfModules.ScalarHomOrdinary.pure_map.{u + 1, u, u + 1} R v z U x y

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem tensorPair_ext {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (M N H : pbcModules W R)
    {v z : ((proEtaleOrdinaryTensor W R).obj M).obj N ⟶ H}
    (h : ∀ U x y, v.val.app U (proEtaleTensorPair W R M N U x y) =
      z.val.app U (proEtaleTensorPair W R M N U x y)) : v = z := by
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext.{u + 1, u, u + 1} R M N H
  intro U x y
  simpa only [tensorPair_eq_pure] using h U x y

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarTensorPair_ext {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M N : pbcModules W R) (H : pbcModules W S)
    {v z : (pbcExtend a).obj (((proEtaleOrdinaryTensor W R).obj M).obj N) ⟶ H}
    (h : ∀ U x y, v.val.app U
        (pbcTensorSection a _ U 1 (proEtaleTensorPair W R M N U x y)) =
      z.val.app U (pbcTensorSection a _ U 1 (proEtaleTensorPair W R M N U x y))) :
    v = z := by
  apply ((pbcScalarAdjunction a).homEquiv _ H).injective
  apply tensorPair_ext R M N ((pbcRestrict a).obj H)
  intro U x y
  change v.val.app U (((pbcScalarAdjunction a).unit.app _).val.app U _) =
    z.val.app U (((pbcScalarAdjunction a).unit.app _).val.app U _)
  have hη (P : pbcModules W R) (V : W.ProEtᵒᵖ) (t : P.val.obj V) :
      ((pbcScalarAdjunction a).unit.app P).val.app V t =
        pbcTensorSection a P V 1 t :=
    (pbcScalarAdjunction_exists a).exists.choose_spec P V t
  erw [hη]
  exact h U x y

private local instance scalarSectionModule {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) : Module (R.obj.obj U) (M.val.obj U) :=
  @ModuleCat.isModule _ _ (M.val.obj U)

private theorem ordinaryTensorPair_smul {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (M N : pbcModules W R) (U : W.ProEtᵒᵖ) (s : R.obj.obj U)
    (x : M.val.obj U) (y : N.val.obj U) :
    proEtaleTensorPair W R M N U (s • x) y =
      s • proEtaleTensorPair W R M N U x y := by
  let η := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
        (M.val ⊗ N.val)).app U
  let v := (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
  change v.hom (η.hom ((s • x) ⊗ₜ[R.obj.obj U] y)) =
    s • v.hom (η.hom (x ⊗ₜ[R.obj.obj U] y))
  have ht : (s • x) ⊗ₜ[R.obj.obj U] y = s • (x ⊗ₜ[R.obj.obj U] y) :=
    (TensorProduct.smul_tmul' s x y).symm
  rw [ht]
  with_unfolding_all
    exact (congrArg v.hom (η.hom.map_smul s (x ⊗ₜ[R.obj.obj U] y))).trans
      (v.hom.map_smul s (η.hom (x ⊗ₜ[R.obj.obj U] y)))

private theorem scalarTensorSection_smul {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    pbcTensorSection a M U s x = s • pbcTensorSection a M U 1 x := by
  unfold pbcTensorSection pbcExtend reductionChange
  with_unfolding_all
    simpa only [mul_one] using completedTensor_smul W a M U s 1 x

/-- The ordinary scalar/tensor comparison is fixed on sheafified pure tensors.
Source: Stacks Tags 03EL, 06YY
(blueprint: def-sf-compact-support-scalar-tensor-balancing).
Proof: send s tensor (m tensor n) to (s tensor m) tensor (1 tensor n).
Balancing makes this a sheafified linear map. Its inverse multiplies the two
S coefficients. These formulas are inverse on tensor generators, commute with
restriction and module maps, and determine the comparison uniquely. -/
theorem scalarOrdinaryTensor_existsUnique {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ∃! μ : ∀ M N : pbcModules W R,
        (pbcExtend a).obj (((proEtaleOrdinaryTensor W R).obj M).obj N) ≅
          ((proEtaleOrdinaryTensor W S).obj ((pbcExtend a).obj M)).obj ((pbcExtend a).obj N),
      ∀ (M N : pbcModules W R) (U : W.ProEtᵒᵖ)
        (s : S.obj.obj U) (m : M.val.obj U) (n : N.val.obj U),
        (μ M N).hom.val.app U
            (pbcTensorSection a _ U s (proEtaleTensorPair W R M N U m n)) =
          proEtaleTensorPair W S _ _ U
            (pbcTensorSection a M U s m) (pbcTensorSection a N U 1 n) := by
  obtain ⟨d⟩ := SheafOfModules.scalarDerivedPair_exists.{u + 1, u, u + 1, u + 2} a
  obtain ⟨μ, _, hμ⟩ :=
    SheafOfModules.ScalarHomOrdinary.scalarOrdinaryTensorComparison_exists a d
  let e := (pbcScalarAdjunction a).leftAdjointUniq d.ordinaryAdjunction
  have he (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      (e.hom.app M).val.app U (pbcTensorSection a M U 1 x) =
        (d.ordinaryAdjunction.unit.app M).val.app U x := by
    have h := congrArg (fun f ↦ f.val.app U x)
      (Adjunction.unit_leftAdjointUniq_hom_app (pbcScalarAdjunction a)
        d.ordinaryAdjunction M)
    change (e.hom.app M).val.app U (((pbcScalarAdjunction a).unit.app M).val.app U x) = _ at h
    erw [(pbcScalarAdjunction_exists a).exists.choose_spec] at h
    exact h
  have hei (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      (e.inv.app M).val.app U ((d.ordinaryAdjunction.unit.app M).val.app U x) =
        pbcTensorSection a M U 1 x := by
    rw [← he]
    exact congrArg (fun f ↦ f.val.app U (pbcTensorSection a M U 1 x)) (e.hom_inv_id_app M)
  let ν := fun M N : pbcModules W R ↦
    e.app _ ≪≫ μ M N ≪≫
      @MonoidalCategory.tensorIso _ _ (SheafOfModules.monoidalCategory S) _ _ _ _
        (e.app M).symm (e.app N).symm
  have hν (M N : pbcModules W R) (U : W.ProEtᵒᵖ)
      (x : M.val.obj U) (y : N.val.obj U) :
      (ν M N).hom.val.app U
        (pbcTensorSection a _ U 1 (proEtaleTensorPair W R M N U x y)) =
      proEtaleTensorPair W S _ _ U
        (pbcTensorSection a M U 1 x) (pbcTensorSection a N U 1 y) := by
    change ((SheafOfModules.monoidalCategory S).tensorHom
      (e.inv.app M) (e.inv.app N)).val.app U
        ((μ M N).hom.val.app U ((e.hom.app _).val.app U _)) = _
    rw [he]
    rw [show proEtaleTensorPair W R M N U x y =
      SheafOfModules.ScalarHomOrdinary.pure R M N U x y from rfl]
    rw [hμ]
    change ((SheafOfModules.monoidalCategory S).tensorHom
      (e.inv.app M) (e.inv.app N)).val.app U
      (proEtaleTensorPair W S _ _ U
        ((d.ordinaryAdjunction.unit.app M).val.app U x)
        ((d.ordinaryAdjunction.unit.app N).val.app U y)) = _
    rw [show (SheafOfModules.monoidalCategory S).tensorHom (e.inv.app M) (e.inv.app N) =
      ((proEtaleOrdinaryTensor W S).map (e.inv.app M)).app _ ≫
        ((proEtaleOrdinaryTensor W S).obj _).map (e.inv.app N) from by
        exact MonoidalCategory.tensorHom_def _ _]
    have hmap := tensorPair_map S (e.inv.app M) (e.inv.app N) U
      ((d.ordinaryAdjunction.unit.app M).val.app U x)
      ((d.ordinaryAdjunction.unit.app N).val.app U y)
    exact hmap.trans (congrArg₂ (proEtaleTensorPair W S _ _ U)
      (hei M U x) (hei N U y))
  refine ⟨ν, ?_, ?_⟩
  · intro M N U s x y
    rw [scalarTensorSection_smul, map_smul]
    calc
      _ = s • proEtaleTensorPair W S _ _ U
          (pbcTensorSection a M U 1 x) (pbcTensorSection a N U 1 y) :=
        congrArg (fun z ↦ s • z) (hν M N U x y)
      _ = _ := by rw [scalarTensorSection_smul a M U s x, ordinaryTensorPair_smul]
  · intro ν' hν'
    funext M N
    apply Iso.ext
    apply scalarTensorPair_ext a M N
    intro U x y
    exact (hν' M N U 1 x y).trans (hν M N U x y).symm

/-- The unique ordinary balancing isomorphism, independently of any integral basis.
Source: Stacks Tags 03EL, 06YY
(blueprint: def-sf-compact-support-scalar-tensor-balancing). -/
def scalarOrdinaryTensor {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ∀ M N : pbcModules W R,
      (pbcExtend a).obj (((proEtaleOrdinaryTensor W R).obj M).obj N) ≅
        ((proEtaleOrdinaryTensor W S).obj ((pbcExtend a).obj M)).obj
          ((pbcExtend a).obj N) :=
  (scalarOrdinaryTensor_existsUnique a).exists.choose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Naturality of ordinary scalar balancing.
Source: Stacks Tag 03EL
(blueprint: def-sf-compact-support-scalar-tensor-balancing).
Proof: both routes send s tensor (m tensor n) to (s tensor v(m)) tensor
(1 tensor z(n)); these sections generate after sheafification. -/
theorem scalarOrdinaryTensor_naturality {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    {M M' N N' : pbcModules W R} (v : M ⟶ M') (z : N ⟶ N') :
    (pbcExtend a).map (((proEtaleOrdinaryTensor W R).map v).app N ≫
        ((proEtaleOrdinaryTensor W R).obj M').map z) ≫
        (scalarOrdinaryTensor a M' N').hom =
      (scalarOrdinaryTensor a M N).hom ≫
        ((proEtaleOrdinaryTensor W S).map ((pbcExtend a).map v)).app
          ((pbcExtend a).obj N) ≫
        ((proEtaleOrdinaryTensor W S).obj ((pbcExtend a).obj M')).map
          ((pbcExtend a).map z) := by
  have hu (P Q : pbcModules W R) (w : P ⟶ Q) (U : W.ProEtᵒᵖ)
      (x : P.val.obj U) :
      ((pbcExtend a).map w).val.app U (pbcTensorSection a P U 1 x) =
        pbcTensorSection a Q U 1 (w.val.app U x) := by
    exact reductionTensor_map W a w U 1 x
  have hμ (P Q : pbcModules W R) (U : W.ProEtᵒᵖ)
      (s : S.obj.obj U) (x : P.val.obj U) (y : Q.val.obj U) :
      (scalarOrdinaryTensor a P Q).hom.val.app U
          (pbcTensorSection a _ U s (proEtaleTensorPair W R P Q U x y)) =
        proEtaleTensorPair W S _ _ U
          (pbcTensorSection a P U s x) (pbcTensorSection a Q U 1 y) :=
    (scalarOrdinaryTensor_existsUnique a).exists.choose_spec P Q U s x y
  apply scalarTensorPair_ext a M N
  intro U x y
  change (scalarOrdinaryTensor a M' N').hom.val.app U
      (((pbcExtend a).map _).val.app U
        (pbcTensorSection a _ U 1 (proEtaleTensorPair W R M N U x y))) =
    ((((proEtaleOrdinaryTensor W S).map ((pbcExtend a).map v)).app
      ((pbcExtend a).obj N) ≫
      ((proEtaleOrdinaryTensor W S).obj ((pbcExtend a).obj M')).map
        ((pbcExtend a).map z)).val.app U)
      ((scalarOrdinaryTensor a M N).hom.val.app U
        (pbcTensorSection a _ U 1 (proEtaleTensorPair W R M N U x y)))
  rw [hu, tensorPair_map, hμ, hμ, tensorPair_map, hu, hu]

attribute [local irreducible] proEtaleFlatRepresentatives

attribute [local irreducible] scalarOrdinaryTensor tensorPullbackTotal
  tensorPullbackTotalComponent

/-- Signed total of the inverse ordinary tensor-balancing maps.
Source: Stacks Tag 07A4
(blueprint: def-sf-compact-support-scalar-tensor-balancing). -/
def scalarTensorTotal {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P Q : CochainComplex (pbcModules W R) ℤ) :
    CochainComplex.mapBifunctor
      (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P)
      (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj Q) (proEtaleOrdinaryTensor W S) ⟶
        ((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor W R)) :=
  letI := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  letI := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} S
  letI := proEtaleTensorPreadditive W R
  letI := proEtaleTensorPreadditive W S
  tensorPullbackTotal (pbcExtend a) (scalarOrdinaryTensor a)
    (fun {_ _ _ _} v z ↦ by
      simpa only [proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor,
        MonoidalCategory.tensorHom_def, Category.assoc] using
          scalarOrdinaryTensor_naturality a v z) P Q

/-- The total map is invertible, since scalar extension is a left adjoint.
Source: Stacks Tag 07A4
(blueprint: def-sf-compact-support-scalar-tensor-balancing).
Proof: tensorPullbackTotal_isIso applies to the scalar adjunction. Each summand
is invertible and the left adjoint preserves the direct sums defining the total. -/
theorem scalarTensorTotal_isIso {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P Q : CochainComplex (pbcModules W R) ℤ) : IsIso (scalarTensorTotal a P Q) := by
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} S
  let := proEtaleTensorPreadditive W R
  let := proEtaleTensorPreadditive W S
  exact tensorPullbackTotal_isIso (pbcExtend a) (scalarOrdinaryTensor a)
    (fun {_ _ _ _} v z ↦ by
      simpa only [proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor,
        MonoidalCategory.tensorHom_def, Category.assoc] using
          scalarOrdinaryTensor_naturality a v z)
    (pbcRestrict a) (pbcScalarAdjunction a) P Q

attribute [local irreducible] scalarTensorTotal

private theorem scalarComplexCounit_isIso {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (pbcModules W R) ℤ) (hp : proEtaleFlatRepresentatives W R P) :
    IsIso (pbcComplexCounit a P) := by
  simp only [proEtaleFlatRepresentatives] at hp
  have := pbcExtensionCounit_isIso a P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1)
  dsimp only [pbcComplexCounit]
  infer_instance

private theorem scalar_preservesFlatRepresentatives {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (pbcModules W R) ℤ) (hp : proEtaleFlatRepresentatives W R P) :
    proEtaleFlatRepresentatives W S
      (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P) := by
  simp only [proEtaleFlatRepresentatives] at hp ⊢
  have hflat (n : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X n)) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X n)) (hp.2 n)
  obtain ⟨hk, hf⟩ :=
    SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients a P
      (pbcExtend a) (reductionChange_obj_eq W a) (reductionChange_map_eq W a)
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1) hflat
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
  intro n
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso S _).symm (hf n)

private theorem tensorTotal_flatRepresentatives {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (P Q : CochainComplex (pbcModules W R) ℤ)
    (hp : proEtaleFlatRepresentatives W R P) (hq : proEtaleFlatRepresentatives W R Q) :
    proEtaleFlatRepresentatives W R
      (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor W R)) := by
  simp only [proEtaleFlatRepresentatives] at hp hq ⊢
  have ht := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model R P Q
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).2 hq.1) hp.2 hq.2
  exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 ht.1, ht.2.1⟩

/-- Existence of the normalized derived scalar/tensor comparison.
Source: Stacks Tags 06YY, 07A4.
The proof descends the signed total comparison through K-flat representatives and
localization; the representative normalization is exactly the displayed equation.
(blueprint: def-sf-compact-support-scalar-tensor-balancing). -/
theorem scalarTensor_exists {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (r : ProEtaleTensorModel W R) (s : ProEtaleTensorModel W S) :
    ∃ μ : r.tensor ⋙ pbcDerivedExtend a ≅
        ((pbcDerivedExtend a).prod (pbcDerivedExtend a)) ⋙ s.tensor,
      ∀ (P Q : CochainComplex (pbcModules W R) ℤ)
        (hp : proEtaleFlatRepresentatives W R P) (hq : proEtaleFlatRepresentatives W R Q),
        ∃ (hp' : proEtaleFlatRepresentatives W S
              (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P))
          (hq' : proEtaleFlatRepresentatives W S
              (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj Q)),
          (pbcDerivedExtend a).map (r.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              s.tensor.map (Prod.mkHom (pbcComplexCounit a P) (pbcComplexCounit a Q)) =
            pbcComplexCounit a (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor W R)) ≫
              DerivedCategory.Q.map
                (@inv _ _ _ _ (scalarTensorTotal a P Q) (scalarTensorTotal_isIso a P Q)) ≫
              s.representative.hom.app (⟨_, hp'⟩, ⟨_, hq'⟩) := by
  classical
  let F := (pbcExtend a).mapHomologicalComplex (.up ℤ)
  let tR := Functor.uncurry.obj ((proEtaleOrdinaryTensor W R).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let tS := Functor.uncurry.obj ((proEtaleOrdinaryTensor W S).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let ε₀ := complexCounitNat (pbcExtend a) (pbcDerivedExtend a) (pbcExtensionCounit a)
  have hε₀ (P : CochainComplex (pbcModules W R) ℤ) :
      ε₀.app P = pbcComplexCounit a P := by
    exact complexCounitNat_app _ _ _ P
  let ε : DerivedCategory.Q ⋙ pbcDerivedExtend a ⟶ F ⋙ DerivedCategory.Q :=
    { app := fun P ↦ pbcComplexCounit a P
      naturality := fun P Q v ↦ by
        have h := ε₀.naturality v
        rw [hε₀ P, hε₀ Q] at h
        exact h }
  have hε (P : CochainComplex (pbcModules W R) ℤ) :
      ε.app P = pbcComplexCounit a P := rfl
  obtain ⟨ff⟩ := tensorRepresentatives_fullyFaithful R S
  let b : (F.prod F) ⋙ tS ≅ tR ⋙ F := NatIso.ofComponents
    (fun Z ↦ @asIso _ _ _ _ (scalarTensorTotal a Z.1 Z.2)
      (scalarTensorTotal_isIso a Z.1 Z.2)) (by
      let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
      let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} S
      intro Z Z' v
      dsimp only [Functor.comp_map, Functor.prod_map, F, tR, tS]
      simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
        SheafOfModules.CanonicalTensorPullbackProof.tensorMap_factor]
      simp only [asIso_hom]
      unfold scalarTensorTotal
      exact SheafOfModules.CanonicalTensorPullbackProof.tensorPullbackTotal_naturality
        (pbcExtend a) (scalarOrdinaryTensor a)
        (fun {_ _ _ _} f g ↦ by
          simpa only [proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor,
            MonoidalCategory.tensorHom_def, Category.assoc] using
              scalarOrdinaryTensor_naturality a f g) v.1 v.2)
  obtain ⟨μ, hμ, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q F (pbcDerivedExtend a) ε
    (proEtaleFlatRepresentatives W R) (proEtaleFlatRepresentatives W S)
    (scalar_preservesFlatRepresentatives a) ff tR tS r.tensor s.tensor
    r.representative s.representative b.symm
    (by intro P hp; rw [hε]; exact scalarComplexCounit_isIso a P hp)
    (by
      intro P Q hp hq
      rw [hε]
      exact scalarComplexCounit_isIso a _ (tensorTotal_flatRepresentatives R P Q hp hq))
  refine ⟨μ, ?_⟩
  intro P Q hp hq
  refine ⟨scalar_preservesFlatRepresentatives a P hp,
    scalar_preservesFlatRepresentatives a Q hq, ?_⟩
  have hb (P Q : CochainComplex (pbcModules W R) ℤ) :
      b.symm.hom.app (P, Q) =
        @inv _ _ _ _ (scalarTensorTotal a P Q) (scalarTensorTotal_isIso a P Q) := by
    rfl
  have hh := hμ P Q hp hq
  simp only [hε, hb] at hh
  dsimp only [tR, Functor.uncurry_obj_obj, Functor.map₂HomologicalComplex] at hh
  exact hh

/-- Uniqueness of a normalized derived scalar/tensor comparison.
Source: Stacks Tags 06YY, 07A4.
The K-flat representative normalization determines each component after localization;
resolving representatives are jointly conservative, so two normalized isomorphisms
are equal by extensionality.
(blueprint: def-sf-compact-support-scalar-tensor-balancing). -/
theorem scalarTensor_unique {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (r : ProEtaleTensorModel W R) (s : ProEtaleTensorModel W S)
    (μ ν : r.tensor ⋙ pbcDerivedExtend a ≅
        ((pbcDerivedExtend a).prod (pbcDerivedExtend a)) ⋙ s.tensor)
    (hμ : ∀ (P Q : CochainComplex (pbcModules W R) ℤ)
        (hp : proEtaleFlatRepresentatives W R P) (hq : proEtaleFlatRepresentatives W R Q),
        ∃ (hp' : proEtaleFlatRepresentatives W S
              (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P))
          (hq' : proEtaleFlatRepresentatives W S
              (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj Q)),
          (pbcDerivedExtend a).map (r.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              s.tensor.map (Prod.mkHom (pbcComplexCounit a P) (pbcComplexCounit a Q)) =
            pbcComplexCounit a (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor W R)) ≫
              DerivedCategory.Q.map
                (@inv _ _ _ _ (scalarTensorTotal a P Q) (scalarTensorTotal_isIso a P Q)) ≫
              s.representative.hom.app (⟨_, hp'⟩, ⟨_, hq'⟩))
    (hν : ∀ (P Q : CochainComplex (pbcModules W R) ℤ)
        (hp : proEtaleFlatRepresentatives W R P) (hq : proEtaleFlatRepresentatives W R Q),
        ∃ (hp' : proEtaleFlatRepresentatives W S
              (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P))
          (hq' : proEtaleFlatRepresentatives W S
              (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj Q)),
          (pbcDerivedExtend a).map (r.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
              ν.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              s.tensor.map (Prod.mkHom (pbcComplexCounit a P) (pbcComplexCounit a Q)) =
            pbcComplexCounit a (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor W R)) ≫
              DerivedCategory.Q.map
                (@inv _ _ _ _ (scalarTensorTotal a P Q) (scalarTensorTotal_isIso a P Q)) ≫
              s.representative.hom.app (⟨_, hp'⟩, ⟨_, hq'⟩)) : μ = ν := by
  obtain ⟨ff⟩ := tensorRepresentatives_fullyFaithful R S
  apply Iso.ext
  apply ff.map_injective
  apply NatTrans.ext
  funext X
  obtain ⟨⟨P, hp⟩, ⟨Q, hq⟩⟩ := X
  obtain ⟨hp', hq', hμ'⟩ := hμ P Q hp hq
  obtain ⟨hp'', hq'', hν'⟩ := hν P Q hp hq
  have := scalarComplexCounit_isIso a P hp
  have := scalarComplexCounit_isIso a Q hq
  have : IsIso (Prod.mkHom (pbcComplexCounit a P) (pbcComplexCounit a Q)) :=
    ⟨⟨Prod.mkHom (inv (pbcComplexCounit a P)) (inv (pbcComplexCounit a Q)),
      by ext <;> simp, by ext <;> simp⟩⟩
  change μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
    ν.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  apply (cancel_epi
    ((pbcDerivedExtend a).map (r.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)))).1
  apply (cancel_mono
    (s.tensor.map (Prod.mkHom (pbcComplexCounit a P) (pbcComplexCounit a Q)))).1
  simpa only [Category.assoc] using hμ'.trans hν'.symm

/-- Tensor balancing on derived categories is uniquely fixed on flat K-flat pairs.
Source: Stacks Tags 06YY, 07A4
(blueprint: def-sf-compact-support-scalar-tensor-balancing).
Proof: base change preserves flat terms and K-flat complexes. On these pairs use
ordinary signed total balancing and the universal derived counits. Tensor descent
extends the map naturally. Every derived pair admits these representatives, and the
counits there are invertible, proving uniqueness and the inverse identities. -/
theorem scalarTensor_existsUnique {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (r : ProEtaleTensorModel W R) (s : ProEtaleTensorModel W S) :
    ∃! μ : r.tensor ⋙ pbcDerivedExtend a ≅
        ((pbcDerivedExtend a).prod (pbcDerivedExtend a)) ⋙ s.tensor,
      ∀ (P Q : CochainComplex (pbcModules W R) ℤ)
        (hp : proEtaleFlatRepresentatives W R P) (hq : proEtaleFlatRepresentatives W R Q),
        ∃ (hp' : proEtaleFlatRepresentatives W S
              (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P))
          (hq' : proEtaleFlatRepresentatives W S
              (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj Q)),
          (pbcDerivedExtend a).map (r.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              s.tensor.map (Prod.mkHom (pbcComplexCounit a P) (pbcComplexCounit a Q)) =
            pbcComplexCounit a (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor W R)) ≫
              DerivedCategory.Q.map
                (@inv _ _ _ _ (scalarTensorTotal a P Q) (scalarTensorTotal_isIso a P Q)) ≫
              s.representative.hom.app (⟨_, hp'⟩, ⟨_, hq'⟩) := by
  obtain ⟨μ, hμ⟩ := scalarTensor_exists a r s
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  exact (scalarTensor_unique a r s μ ν hμ hν).symm

/-- The specified ordinary derived scalar/tensor comparison.
Source: Stacks Tags 06YY, 07A4
(blueprint: def-sf-compact-support-scalar-tensor-balancing). -/
def scalarTensor {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (r : ProEtaleTensorModel W R) (s : ProEtaleTensorModel W S) :
    r.tensor ⋙ pbcDerivedExtend a ≅
      ((pbcDerivedExtend a).prod (pbcDerivedExtend a)) ⋙ s.tensor :=
  (scalarTensor_existsUnique a r s).exists.choose

attribute [local irreducible] scalarTensor

end WeilConjectures.PurCompactSupport
