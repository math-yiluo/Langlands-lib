/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtensionModel
public import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtensionTensor
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonNatural
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization

/-!
# Coefficient compatibility of the specified integral inverse-image comparison

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), pp. 50--51.
The scalar compatibility formula is the agent calculation from the specified
quotient-cone maps (blueprint: lem-weil-isomorphism-comparison-scalar-extension).
The ordinary tensor is expressed in its exact finite-free model. Its completion
comparison is identified with the specified universal derived-tensor comparison.
The models are in `IsomorphismComparisonScalarExtensionModel`, the tensor isomorphism and
the maps α, β in `IsomorphismComparisonScalarExtensionTensor`; this file proves the square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open scoped ChangeOfRings
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

section SharedHelpers

open AlgebraicGeometry

attribute [local irreducible] integralCompletedScalarMap inverseImageCompletedCoefficientMap

private theorem tensorModel_hom_ext (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A B : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) (f g : A ⟶ B)
    (h : ∀ (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U),
      f.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      g.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)))) : f = g := by
  subst A
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x => exact h U a x
  | add z z' hz hz' => simp only [map_add, hz, hz']

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryScalarAdjunction (W : AlgebraicGeometry.Scheme.{u}) :
    ∃ a : integralOrdinaryScalar l E L ι W ⊣
      SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι W)),
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = integralOrdinaryTensorSection l E L ι W M U 1 x := by
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralCompletedScalarMap l E L ι W)
  obtain ⟨a, ha⟩ := h (integralOrdinaryScalar l E L ι W)
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose
  refine ⟨a, ?_⟩
  intro M U x
  have h := ha M ((integralOrdinaryScalar l E L ι W).obj M)
    (eqToHom ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M).symm) U x
  simp only [eqToHom_trans, eqToHom_refl] at h
  rw [Adjunction.homEquiv_id] at h
  exact h

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem tensorSection_smul (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
      a • ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) := by
  subst A
  let k := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app U ≫
      (ModuleCat.restrictScalarsId (S.obj.obj U)).hom.app _
  change k (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) =
    a • k ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)
  have ht : a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      a • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) := by
    change a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      (a * 1) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x
    rw [mul_one]
  rw [ht]
  exact k.hom.map_smul a _

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryTensorSection_smul (W : AlgebraicGeometry.Scheme.{u})
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
    (x : M.val.obj U) :
    integralOrdinaryTensorSection l E L ι W M U a x =
      a • integralOrdinaryTensorSection l E L ι W M U 1 x := by
  exact tensorSection_smul W (integralCompletedScalarMap l E L ι W) M _
    ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M) U a x
end SharedHelpers

section ComparisonSquare

universe r s
open AlgebraicGeometry

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryTensorSection_map (W : Scheme.{u})
    {M N : integralTowerModules l E W} (f : M ⟶ N) (U : W.ProEtᵒᵖ)
    (x : M.val.obj U) :
    (((integralOrdinaryScalar l E L ι W).map f).val.app U)
        (integralOrdinaryTensorSection l E L ι W M U 1 x) =
      integralOrdinaryTensorSection l E L ι W N U 1 (f.val.app U x) := by
  obtain ⟨a, ha⟩ := ordinaryScalarAdjunction l E L ι W
  have h := congrArg (fun k ↦ k.val.app U x) (a.unit.naturality f)
  change ((a.unit.app N).val.app U) (f.val.app U x) =
    (((integralOrdinaryScalar l E L ι W).map f).val.app U)
      ((a.unit.app M).val.app U x) at h
  rw [ha, ha] at h
  exact h.symm

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryTensorSection_restrict (W : Scheme.{u})
    (M : integralTowerModules l E W) {U V : W.ProEtᵒᵖ} (f : U ⟶ V)
    (x : M.val.obj U) :
    (((integralOrdinaryScalar l E L ι W).obj M).val.map f)
        (integralOrdinaryTensorSection l E L ι W M U 1 x) =
      integralOrdinaryTensorSection l E L ι W M V 1 (M.val.map f x) := by
  obtain ⟨a, ha⟩ := ordinaryScalarAdjunction l E L ι W
  have h := PresheafOfModules.naturality_apply (a.unit.app M).val f x
  change (a.unit.app M).val.app V (M.val.map f x) =
    (((integralOrdinaryScalar l E L ι W).obj M).val.map f)
      ((a.unit.app M).val.app U x) at h
  rw [ha, ha] at h
  exact h.symm

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarThetaSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
        (inverseImageReductionTheta l E g n P) ≫
        (scalarPullbackLevel l E L ι g n).app P =
      ((NatIso.mapHomologicalComplex (isomorphismScalarTensor l E L ι g)
        (.up ℤ)).hom.app P) ≫ inverseImageReductionTheta l L g n
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply tensorModel_hom_ext X (integralCompletedScalarMap l E L ι X)
    ((inverseImageIntegralModules l E g).obj (P.X i)) _ _
    ((integralOrdinaryScalarWitness l E L ι X).choose_spec.choose _)
  intro U a x
  let M := ((inverseImageIntegralModules l E g).obj (P.X i))
  let f := (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
    (inverseImageReductionTheta l E g n P) ≫ (scalarPullbackLevel l E L ι g n).app P).f i
  let h := (((NatIso.mapHomologicalComplex (isomorphismScalarTensor l E L ι g)
    (.up ℤ)).hom.app P) ≫ inverseImageReductionTheta l L g n
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)).f i
  change f.val.app U (integralOrdinaryTensorSection l E L ι X M U a x) =
    h.val.app U (integralOrdinaryTensorSection l E L ι X M U a x)
  suffices hf : f.val.app U (integralOrdinaryTensorSection l E L ι X M U 1 x) =
      h.val.app U (integralOrdinaryTensorSection l E L ι X M U 1 x) by
    rw [ordinaryTensorSection_smul]
    simpa only [map_smul] using congrArg (fun z ↦ a • z) hf
  let V := (proEtaleIsoPostcompose g).obj U.unop
  let q := (proEtaleIsoCommaArrow g U.unop).op
  have hθ := (inverseImageReductionTheta_existsUnique l E g n P).exists.choose_spec
    i U.unop x
  have hb := (isomorphismScalarTensor_existsUnique l E L ι g).exists.choose_spec
    (P.X i) U.unop x 1
  simp only [map_one] at hb
  have hθ' := (inverseImageReductionTheta_existsUnique l L g n
    (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)
    ).exists.choose_spec i U.unop
      (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x)
  change (((scalarPullbackLevel l E L ι g n).app P).f i).val.app U
      ((((integralOrdinaryScalar l E L ι X).map
        ((inverseImageReductionTheta l E g n P).f i)).val.app U)
          (integralOrdinaryTensorSection l E L ι X M U 1 x)) =
    ((inverseImageReductionTheta l L g n
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)).f i
      ).val.app U (((isomorphismScalarTensor l E L ι g).hom.app (P.X i)).val.app U
        (integralOrdinaryTensorSection l E L ι X M U 1 x))
  erw [ordinaryTensorSection_map, hθ, hb, hθ']
  erw [← ordinaryTensorSection_restrict]
  have hn := PresheafOfModules.naturality_apply
    (((scalarPullbackLevel l E L ι g n).app P).f i).val q
      (integralOrdinaryTensorSection l E L ι X
        (((integralOperationsPullbackLevel l E g n).obj P).X i)
        (op ((proEtaleBaseChange g).obj V)) 1
          (integralOperationsPullbackGenerator l E g n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
            (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x)))
  erw [hn]
  congr 1
  exact (scalarPullbackLevel_existsUnique l E L ι g n).exists.choose_spec P i V x

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem zero_lift_f
    {A : Type r} [Category.{s} A] [Abelian A]
    {K L M : CochainComplex A ℤ} (φ : K ⟶ L) (α : M ⟶ K)
    (h : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain M L (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ φ) = 0) (i : ℤ) :
    (CochainComplex.mappingCocone.lift φ α 0 h).f i = α.f i ≫
      HomologicalComplex.homotopyCofiber.inlX φ i (i + (-1))
        (by change i + (-1) + 1 = i; omega) := by
  simp only [CochainComplex.mappingCocone.lift,
    CochainComplex.mappingCocone.liftCocycle, CochainComplex.mappingCocone.liftCochain,
    CochainComplex.mappingCone.liftCochain,
    CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.inr, CochainComplex.HomComplex.Cochain.zero_comp,
    add_zero, CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
      _ _ _ _ i _ _ (i + (-1)) (by omega),
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.assoc]
  erw [Category.comp_id]

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem zero_lift_naturality
    {A : Type r} [Category.{s} A] [Abelian A]
    {K L M N : CochainComplex A ℤ} (φ : K ⟶ K) (ψ : L ⟶ L)
    (a : K ⟶ L) (ha : φ ≫ a = a ≫ ψ) (f : M ⟶ N) (α : M ⟶ K) (β : N ⟶ L)
    (hα : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain M K (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ φ) = 0)
    (hβ : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain N L (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (β ≫ ψ) = 0)
    (hn : f ≫ β = α ≫ a) :
    f ≫ CochainComplex.mappingCocone.lift ψ β 0 hβ =
      CochainComplex.mappingCocone.lift φ α 0 hα ≫
        (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom φ ψ
            (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
            (Arrow.homMk a a ha.symm)) := by
  ext i : 1
  dsimp only [HomologicalComplex.comp_f]
  rw [zero_lift_f, zero_lift_f, CochainComplex.shiftFunctor_map_f']
  rw [Category.assoc, HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.inlX_desc_f]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
    Pi.zero_apply, zero_add, add_zero]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
  simpa only [HomologicalComplex.comp_f, Category.assoc, Arrow.homMk_left] using
    congrArg (fun k ↦ k.f i ≫ HomologicalComplex.homotopyCofiber.inlX ψ
      i (i + (-1)) (by change i + (-1) + 1 = i; omega)) hn

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem cocone_hom_ext
    {A : Type*} [Category A] [Abelian A]
    {K L M : CochainComplex A ℤ} (φ : K ⟶ L) (f h : M ⟶ CochainComplex.mappingCocone φ)
    (hf : f ≫ CochainComplex.mappingCocone.fst φ = h ≫ CochainComplex.mappingCocone.fst φ)
    (hs : ∀ i j (hij : i + -1 = j),
      f.f i ≫ (CochainComplex.mappingCocone.snd φ).v i j hij =
        h.f i ≫ (CochainComplex.mappingCocone.snd φ).v i j hij) : f = h := by
  ext i : 1
  have hfi := congrArg (fun z ↦ z.f i) hf
  change f.f i ≫ _ = h.f i ≫ _ at hfi
  have hid := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  have hfid := congrArg (fun z ↦ f.f i ≫ z) hid
  have hhid := congrArg (fun z ↦ h.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc, Category.comp_id] at hfid hhid
  rw [hfi, hs i (i - 1) (by omega)] at hfid
  exact hfid.symm.trans hhid

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem roos_additive_augmentation
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {B : Type*} [Category B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (P : CochainComplex A ℤ) (α : P ⟶ ∏ᶜ fun n ↦ C.obj (op n))
    (hα : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P (∏ᶜ fun n ↦ C.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ scalarRoosBoundary C) = 0)
    (lam : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
      ∏ᶜ fun n ↦ (C ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op n))
    (hlam : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain ((F.mapHomologicalComplex (.up ℤ)).obj P)
          (∏ᶜ fun n ↦ (C ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (lam ≫ scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ))) = 0)
    (hlamn : ∀ n, lam ≫ Pi.π _ n =
      (F.mapHomologicalComplex (.up ℤ)).map (α ≫ Pi.π _ n)) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 hα) ≫
        scalarRoosMap F C =
      CochainComplex.mappingCocone.lift
        (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ))) lam 0 hlam := by
  apply cocone_hom_ext
  · apply Pi.hom_ext
    intro n
    erw [Category.assoc, Category.assoc,
      (scalarRoosMap_existsUnique F C).exists.choose_spec.1 n]
    erw [← CategoryTheory.Functor.map_comp, ← Category.assoc,
      CochainComplex.mappingCocone.lift_fst]
    erw [CochainComplex.mappingCocone.lift_fst]
    exact (hlamn n).symm
  · intro i j hij
    apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval B (.up ℤ) j)
      (fun n ↦ (C ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op n))).hom_ext
    rintro ⟨n⟩
    simp only [HomologicalComplex.comp_f, Category.assoc]
    change ((F.mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 hα)).f i ≫
      (scalarRoosMap F C).f i ≫
      (CochainComplex.mappingCocone.snd
        (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)))).v i j hij ≫
      (Pi.π (fun n ↦ (C ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op n)) n).f j = _
    erw [(scalarRoosMap_existsUnique F C).exists.choose_spec.2 i j hij n]
    change F.map ((CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 hα).f i) ≫
      F.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v i j hij ≫
        (Pi.π (fun n ↦ C.obj (op n)) n).f j) = _
    erw [← CategoryTheory.Functor.map_comp, ← Category.assoc,
      CochainComplex.mappingCocone.lift_f_snd_v]
    simp

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem roos_natural_augmentation
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {B : Type*} [Category B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (C' : ℕᵒᵖ ⥤ CochainComplex B ℤ) (P : CochainComplex A ℤ)
    (P' : CochainComplex B ℤ) (α : P ⟶ ∏ᶜ fun n ↦ C.obj (op n))
    (β : P' ⟶ ∏ᶜ fun n ↦ C'.obj (op n))
    (hα : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P (∏ᶜ fun n ↦ C.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ scalarRoosBoundary C) = 0)
    (hβ : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P' (∏ᶜ fun n ↦ C'.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (β ≫ scalarRoosBoundary C') = 0)
    (b : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ P')
    (d : C ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ C')
    (hf : ∀ n, (F.mapHomologicalComplex (.up ℤ)).map (α ≫ Pi.π _ n) ≫ d.app (op n) =
      b ≫ β ≫ Pi.π _ n) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 hα) ≫
        scalarRoosMap F C ≫ integralOperationsRoosMap d =
      b ≫ CochainComplex.mappingCocone.lift (scalarRoosBoundary C') β 0 hβ := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  let lam : FC.obj P ⟶ ∏ᶜ fun n ↦ (C ⋙ FC).obj (op n) :=
    Pi.lift (fun n ↦ FC.map (α ≫ Pi.π _ n))
  have hlamn (n : ℕ) : lam ≫ Pi.π _ n = FC.map (α ≫ Pi.π _ n) := Pi.lift_comp_π _ n
  have hα₀ : α ≫ scalarRoosBoundary C = 0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa only [CochainComplex.HomComplex.δ_zero, zero_add,
      CochainComplex.HomComplex.Cochain.ofHom_zero] using hα
  have hcompat (n : ℕ) : α ≫ Pi.π _ n =
      α ≫ Pi.π _ (n + 1) ≫ integralOperationsTowerStep C n := by
    have h := congrArg (fun z ↦ z ≫ Pi.π (fun n ↦ C.obj (op n)) n) hα₀
    have h' : α ≫ Pi.π _ n - α ≫ Pi.π _ (n + 1) ≫
        integralOperationsTowerStep C n = 0 := by
      simpa only [scalarRoosBoundary, towerTransitionEndomorphism, towerProductShift,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp, Category.comp_id,
        Category.assoc, Pi.lift_comp_π, Limits.zero_comp] using h
    exact sub_eq_zero.mp h'
  have hlamφ : lam ≫ scalarRoosBoundary (C ⋙ FC) = 0 := by
    apply Pi.hom_ext
    intro n
    have hφ := (towerTransitionEndomorphism_eq_iff
      (K := fun n ↦ (C ⋙ FC).obj (op n))
      (integralOperationsTowerStep (C ⋙ FC)) (scalarRoosBoundary (C ⋙ FC))).mp rfl n
    erw [Category.assoc, hφ, Preadditive.comp_sub, ← Category.assoc, hlamn, hlamn]
    have hc : FC.map (α ≫ Pi.π _ (n + 1)) ≫ FC.map (integralOperationsTowerStep C n) =
        FC.map (α ≫ Pi.π _ n) := by
      rw [← CategoryTheory.Functor.map_comp, Category.assoc, ← hcompat]
    simp only [Limits.zero_comp]
    dsimp only [integralOperationsTowerStep, Functor.comp_map]
    change FC.map (α ≫ Pi.π _ n) -
      FC.map (α ≫ Pi.π _ (n + 1)) ≫ FC.map (integralOperationsTowerStep C n) = 0
    rw [hc, sub_self]
  have hlam : CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain (FC.obj P)
        (∏ᶜ fun n ↦ (C ⋙ FC).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (lam ≫ scalarRoosBoundary (C ⋙ FC)) = 0 := by
    simp [hlamφ]
  have h₁ := roos_additive_augmentation F C P α hα lam hlam hlamn
  have hlamd : lam ≫ Limits.Pi.map (fun n ↦ d.app (op n)) = b ≫ β := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.map_π]
    erw [← Category.assoc, hlamn]
    exact hf n
  have h₂ := zero_lift_naturality (scalarRoosBoundary (C ⋙ FC)) (scalarRoosBoundary C')
    (Limits.Pi.map (fun n ↦ d.app (op n))) (integralOperationsRoos_square d)
    b lam β hlam hβ hlamd.symm
  rw [← Category.assoc, h₁]
  exact h₂.symm

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarRoosSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
        (inverseImageRoosComparisonComplex l E g P) ≫ scalarPullbackChain l E L ι g P =
      ((NatIso.mapHomologicalComplex (isomorphismScalarTensor l E L ι g)
        (.up ℤ)).hom.app P) ≫ inverseImageRoosComparisonComplex l L g
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) := by
  let F := integralOrdinaryScalar l E L ι X
  let FC := F.mapHomologicalComplex (.up ℤ)
  let C := (integralOperationsPullbackTowerFunctor l E g).obj P
  let Q := ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P
  let C' := (integralOperationsPullbackTowerFunctor l L g).obj Q
  let d := (scalarPullbackTower l E L ι g).app P
  let b := ((NatIso.mapHomologicalComplex (isomorphismScalarTensor l E L ι g)
    (.up ℤ)).hom.app P)
  change FC.map (inverseImageRoosComparisonComplex l E g P) ≫
    scalarRoosMap F C ≫ integralOperationsRoosMap d = _
  apply roos_natural_augmentation F C C'
    (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P)
    (((inverseImageIntegralModules l L g).mapHomologicalComplex (.up ℤ)).obj Q)
    (inverseImageReductionProduct l E g P) (inverseImageReductionProduct l L g Q)
    (inverseImageReductionProduct_lift_condition l E g P)
    (inverseImageReductionProduct_lift_condition l L g Q) b d
  intro n
  have h := scalarThetaSquare l E L ι g n P
  have hd := (scalarPullbackTower_existsUnique l E L ι g).exists.choose_spec P n
  erw [inverseImageReductionProduct, Pi.lift_comp_π, hd,
    inverseImageReductionProduct, Pi.lift_comp_π]
  exact h

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem derivedSquare_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    (F₁ : A ⥤ B) (F₂ : B ⥤ D) (G₁ : A ⥤ C) (G₂ : C ⥤ D)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex A ℤ) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
      (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F₁ F₂).inv.app
    (DerivedCategory.Q.obj P))).1
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc,
    ← Functor.mapDerivedCategoryNatIso_fac e P]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem completionSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (GE PE : A ⥤ B) (Gₗ Pₗ : C ⥤ D) (CX TX : B ⥤ D) (CY TY : A ⥤ C)
    (κE : GE ⟶ PE) (κL : Gₗ ⟶ Pₗ) (χX : CX ⟶ TX) (χY : CY ⟶ TY)
    (α : PE ⋙ CX ⟶ CY ⋙ Pₗ) (b : GE ⋙ CX ⟶ CY ⋙ Gₗ) (K : A)
    [IsIso (χX.app (GE.obj K))] [IsIso (χX.app (PE.obj K))]
    (h : CX.map (κE.app K) ≫ α.app K = b.app K ≫ κL.app (CY.obj K)) :
    TX.map (κE.app K) ≫ inv (χX.app (PE.obj K)) ≫ α.app K ≫ Pₗ.map (χY.app K) =
      inv (χX.app (GE.obj K)) ≫ b.app K ≫ Gₗ.map (χY.app K) ≫ κL.app (TY.obj K) := by
  apply (cancel_epi (χX.app (GE.obj K))).1
  simp only [← Category.assoc]
  rw [← χX.naturality (κE.app K)]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, κL.naturality]

attribute [-instance] SheafOfModules.instPreadditive in
attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem goodRepresentative_exists (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules.{u, u} l E W)) :
    ∃ P : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let A : CochainComplex (integralTowerModules.{u, u} l E W) ℤ :=
    DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj A ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let h := CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
    (C := W.ProEt) (J := ProEt.topology W)
    (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) A
  let P := h.choose
  let p := h.choose_spec.choose
  let hp := h.choose_spec.choose_spec
  let : QuasiIso p := hp.2.2.1
  exact ⟨⟨P, hp.1, fun i ↦
    (exactFunctor (integralTowerModules.{u, u} l E W)
      (integralTowerModules.{u, u} l E W)).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (P.X i)).symm
      (hp.2.1 i)⟩,
    ⟨asIso (DerivedCategory.Q.map p) ≪≫ e⟩⟩

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem natTrans_eq_of_representatives
    {A B D : Type*} [Category A] [Category B] [Category D]
    (Q : A ⥤ B) (hQ : ∀ K : B, ∃ P : A, Nonempty (Q.obj P ≅ K))
    {F G : B ⥤ D} (α β : F ⟶ G) (h : ∀ P : A, α.app (Q.obj P) = β.app (Q.obj P)) :
    α = β := by
  ext K
  obtain ⟨P, ⟨e⟩⟩ := hQ K
  apply (cancel_epi (F.map e.hom)).mp
  rw [α.naturality, β.naturality, h P]

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarDerivedSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hstrict : ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
      ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
          (inverseImageRoosComparisonComplex l E g P) ≫ scalarPullbackChain l E L ι g P =
        ((NatIso.mapHomologicalComplex (isomorphismScalarTensor l E L ι g)
          (.up ℤ)).hom.app P) ≫ inverseImageRoosComparisonComplex l L g
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P))
    (K : DerivedCategory (integralTowerModules l E Y)) :
    (integralOrdinaryDerivedScalar l E L ι X).map
        (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
        (scalarPullbackOrdinary l E L ι g).hom.app K =
      (isomorphismScalarTensorDerived l E L ι g).hom.app K ≫
        inverseImagePullbackComparisonDerived l L g hX hY
          ((integralOrdinaryDerivedScalar l E L ι Y).obj K) := by
  obtain ⟨κE, hκE, hresE, -, -⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l E g hX hY
  obtain ⟨κL, hκL, hresL, -, -⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l L g hX hY
  let FX := integralOrdinaryScalar l E L ι X
  let FY := integralOrdinaryScalar l E L ι Y
  let GE := inverseImageIntegralModules l E g
  let Gₗ := inverseImageIntegralModules l L g
  let α := (scalarPullbackOrdinary l E L ι g).hom
  let b := (isomorphismScalarTensorDerived l E L ι g).hom
  let A := Functor.whiskerRight κE FX.mapDerivedCategory ≫ α
  let B := b ≫ Functor.whiskerLeft FY.mapDerivedCategory κL
  have hAB : A = B := by
    apply natTrans_eq_of_representatives (integralOperationsGoodLocalization l E Y)
      (goodRepresentative_exists l E Y) A B
    intro P
    change FX.mapDerivedCategory.map (κE.app (DerivedCategory.Q.obj P.obj)) ≫
        α.app (DerivedCategory.Q.obj P.obj) =
      b.app (DerivedCategory.Q.obj P.obj) ≫
        κL.app (FY.mapDerivedCategory.obj (DerivedCategory.Q.obj P.obj))
    let Q := (FY.mapHomologicalComplex (.up ℤ)).obj P.obj
    let Qgood : (integralOperationsGoodComplex l L Y).FullSubcategory :=
      ⟨Q, scalarGood l E L ι Y P⟩
    have hkE : κE.app (DerivedCategory.Q.obj P.obj) =
        GE.mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj) ≫
            (integralDerivedPullbackComparison l E g).inv.app P := by
      rw [hresE P.obj P (𝟙 _)]
      dsimp only [inverseImagePullbackComparison, GE]
      simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, IsIso.inv_id,
        ObjectProperty.ι_obj, Category.id_comp, NatIso.cancel_natIso_hom_left]
      exact (congrArg (fun t => _ ≫ _ ≫ t)
        ((integralDerivedPullback l E g).map_id (DerivedCategory.Q.obj P.obj))).trans
          ((Category.assoc _ _ _).symm.trans (Category.comp_id _))
    have hkL : κL.app (DerivedCategory.Q.obj Q) =
        Gₗ.mapDerivedCategoryFactors.hom.app Q ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l L g Q) ≫
            (integralDerivedPullbackComparison l L g).inv.app Qgood := by
      rw [hresL Q Qgood (𝟙 _)]
      dsimp only [inverseImagePullbackComparison, Gₗ, Qgood]
      simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, IsIso.inv_id,
        ObjectProperty.ι_obj, Category.id_comp, NatIso.cancel_natIso_hom_left]
      exact (congrArg (fun t => _ ≫ _ ≫ t)
        ((integralDerivedPullback l L g).map_id (DerivedCategory.Q.obj Q))).trans
          ((Category.assoc _ _ _).symm.trans (Category.comp_id _))
    have heκ : FX.mapDerivedCategory.map (κE.app (DerivedCategory.Q.obj P.obj)) ≫
        FX.mapDerivedCategory.map ((integralDerivedPullbackComparison l E g).hom.app P) =
      FX.mapDerivedCategory.map (GE.mapDerivedCategoryFactors.hom.app P.obj) ≫
        FX.mapDerivedCategory.map
          (DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj)) := by
      rw [hkE]
      simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    have hlκ : κL.app (DerivedCategory.Q.obj Q) ≫
        (integralDerivedPullbackComparison l L g).hom.app Qgood =
      Gₗ.mapDerivedCategoryFactors.hom.app Q ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l L g Q) := by
      rw [hkL]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    have hα := (scalarPullbackOrdinary_existsUnique l E L ι g).exists.choose_spec P
    have hf := FX.mapDerivedCategoryFactors.hom.naturality
      (inverseImageRoosComparisonComplex l E g P.obj)
    dsimp only [Functor.comp_map] at hf
    have hb := derivedSquare_factors GE FX FY Gₗ (isomorphismScalarTensor l E L ι g) P.obj
    have hQ := congrArg DerivedCategory.Q.map (hstrict P.obj)
    simp only [CategoryTheory.Functor.map_comp] at hQ
    have hn := κL.naturality (FY.mapDerivedCategoryFactors.hom.app P.obj)
    apply (cancel_mono ((integralDerivedPullback l L g).map
      (FY.mapDerivedCategoryFactors.hom.app P.obj) ≫
      (integralDerivedPullbackComparison l L g).hom.app Qgood)).1
    simp only [Category.assoc]
    erw [← hα]
    erw [← Category.assoc, ← Category.assoc, heκ]
    simp only [Category.assoc]
    erw [reassoc_of% hf]
    have hQ' := congrArg (fun z ↦
      FX.mapDerivedCategory.map (GE.mapDerivedCategoryFactors.hom.app P.obj) ≫
        FX.mapDerivedCategoryFactors.hom.app ((GE.mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
          z) hQ
    refine hQ'.trans ?_
    calc
      _ = b.app (DerivedCategory.Q.obj P.obj) ≫
          Gₗ.mapDerivedCategory.map (FY.mapDerivedCategoryFactors.hom.app P.obj) ≫
          Gₗ.mapDerivedCategoryFactors.hom.app Q ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l L g Q) := by
        dsimp only [b, isomorphismScalarTensorDerived, Functor.mapDerivedCategorySquareIso,
          FX, FY, GE, Gₗ, Q] at hb ⊢
        simpa only [Category.assoc] using! congrArg
          (fun z ↦ z ≫ DerivedCategory.Q.map (inverseImageRoosComparisonComplex l L g Q)) hb
      _ = b.app (DerivedCategory.Q.obj P.obj) ≫
          Gₗ.mapDerivedCategory.map (FY.mapDerivedCategoryFactors.hom.app P.obj) ≫
          κL.app (DerivedCategory.Q.obj Q) ≫
          (integralDerivedPullbackComparison l L g).hom.app Qgood :=
        congrArg (fun z ↦ b.app (DerivedCategory.Q.obj P.obj) ≫
          Gₗ.mapDerivedCategory.map (FY.mapDerivedCategoryFactors.hom.app P.obj) ≫ z) hlκ.symm
      _ = _ := by
        dsimp only [Gₗ, Q, FY, inverseImageIntegralDerived, Functor.comp_obj] at hn ⊢
        simpa only [Category.assoc] using! congrArg
          (fun z ↦ b.app (DerivedCategory.Q.obj P.obj) ≫ z ≫
            (integralDerivedPullbackComparison l L g).hom.app Qgood) hn
  have h := congr_app hAB K
  change FX.mapDerivedCategory.map (κE.app K) ≫ α.app K =
    b.app K ≫ κL.app (FY.mapDerivedCategory.obj K) at h
  rw [hκE, hκL] at h
  exact h

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarCompletedSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hOrd : ∀ K : DerivedCategory (integralTowerModules l E Y),
      (integralOrdinaryDerivedScalar l E L ι X).map
          (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
          (scalarPullbackOrdinary l E L ι g).hom.app K =
        (isomorphismScalarTensorDerived l E L ι g).hom.app K ≫
          inverseImagePullbackComparisonDerived l L g hX hY
            ((integralOrdinaryDerivedScalar l E L ι Y).obj K))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).map
        (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
      isomorphismComparisonScalarAlpha l E L ι g hX hY K hK =
    isomorphismComparisonScalarBeta l E L ι g hX hY K hK ≫
      inverseImagePullbackComparisonDerived l L g hX hY
        ((integralScalarExtension l E L ι Y).obj K) := by
  obtain ⟨κE, hκE, _, _, _⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l E g hX hY
  obtain ⟨κL, hκL, _, _, _⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l L g hX hY
  have hc := isomorphismComparisonInputs_constructible l E g hX hY K hK
  let : IsIso ((scalarCompletion l E L ι X).app
      ((inverseImageIntegralDerived l E g).obj K)) :=
    (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.2 _ hc.1.1
  let : IsIso ((scalarCompletion l E L ι X).app
      ((integralDerivedPullback l E g).obj K)) :=
    (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.2 _ hc.2.1
  have h := completionSquare
    (inverseImageIntegralDerived l E g) (integralDerivedPullback l E g)
    (inverseImageIntegralDerived l L g) (integralDerivedPullback l L g)
    (integralOrdinaryDerivedScalar l E L ι X) (integralScalarExtension l E L ι X)
    (integralOrdinaryDerivedScalar l E L ι Y) (integralScalarExtension l E L ι Y)
    κE κL (scalarCompletion l E L ι X) (scalarCompletion l E L ι Y)
    (scalarPullbackOrdinary l E L ι g).hom
    (isomorphismScalarTensorDerived l E L ι g).hom K
    (by simpa only [hκE, hκL] using hOrd K)
  rw [hκE, hκL] at h
  simpa only [isomorphismComparisonScalarAlpha, isomorphismComparisonScalarBeta,
    scalarPullbackCompleted, scalarCompletionIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom, asIso_inv, Category.assoc] using h

end ComparisonSquare

/-- The specified integral comparison commutes with finite coefficient extension.
Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), pp. 50--51; the compatibility
itself is the agent calculation of the specified quotient-cone maps
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: the ordinary tensor unit and the finite scalar-pullback generator formula
prove the square at every finite level. Product extensionality and the two actual
Roos cocone coordinates give the strict augmentation square, with zero shifted
coordinate. On good representatives its localization is the ordinary derived square,
by the normalizations of the specified comparison and scalarPullbackOrdinary.
Naturality and good representative isomorphisms give that square on every derived
object. Finally precompose with the specified completion comparison chi on G_E K.
Naturality of chi and kappa reduces to the ordinary square. Constructibility makes
this completion comparison invertible, so it cancels to give the stated identity. -/
theorem isomorphismComparison_scalarExtension
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).map
        (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
      isomorphismComparisonScalarAlpha l E L ι g hX hY K hK =
    isomorphismComparisonScalarBeta l E L ι g hX hY K hK ≫
      inverseImagePullbackComparisonDerived l L g hX hY
        ((integralScalarExtension l E L ι Y).obj K) := by
  exact scalarCompletedSquare l E L ι g hX hY
    (scalarDerivedSquare l E L ι g hX hY (scalarRoosSquare l E L ι g)) K hK

end WeilConjectures
