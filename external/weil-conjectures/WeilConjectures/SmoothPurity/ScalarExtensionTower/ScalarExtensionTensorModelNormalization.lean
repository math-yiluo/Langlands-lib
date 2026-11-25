/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.SmoothPurity.Coefficient.CoefficientTensorModelComparison
import WeilConjectures.SmoothPurity.Supporting.CoherentReferenceQuotientComparison
import WeilConjectures.SmoothPurity.ScalarExtensionTower.StrictQuotientTensorGenerator
import WeilConjectures.SmoothPurity.Supporting.Tensor.ReferenceTensorModelFactors

/-! # Normalization of the completed tensor realization

The realization is constructed from the existing normalized tensor descent,
the adjunction comparison of reductions, and the closed tensor comparison.
Only its equation on coherent strict quotient presentations remains to prove.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  pullbackTensorCalculus

attribute [local irreducible] coefficientTotalTensor
attribute [local implicit_reducible] tensor pullbackTensorSystemModel
  pullbackTensorConstantLimit integralOperationsRoos

private theorem roosUnit_eq (W : Scheme.{u})
    (I : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    pullbackTensorRoosUnit l E W I = integralComparisonLimitToRoos l E W I := by
  apply (integralComparisonLimitToRoos_existsUnique l E W I).unique
  · constructor
    · intro n
      have hf := CochainComplex.mappingCocone.lift_fst
        (scalarRoosBoundary I.asFunctor) (pullbackTensorRoosAugmentation l E W I) 0
        (pullbackTensorRoosAugmentation_condition l E W I)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f ↦ f ≫ CategoryTheory.Limits.Pi.π
          (fun m ↦ I.asFunctor.obj (Opposite.op m)) n) hf).trans
            (CategoryTheory.Limits.Pi.lift_comp_π _ n))
    · intro i j h
      exact CochainComplex.mappingCocone.lift_f_snd_v
        (scalarRoosBoundary I.asFunctor) (pullbackTensorRoosAugmentation l E W I) 0
        (pullbackTensorRoosAugmentation_condition l E W I) i j h
  · exact (integralComparisonLimitToRoos_existsUnique l E W I).exists.choose_spec

private theorem roosBridge_eq (W : Scheme.{u})
    (ρ : IntegralComparisonRoosModel.{u, u} l E W) (C : Complex l E W) :
    pullbackTensorLimitRoos l E W C = integralComparisonRoosBridge l E W ρ C := by
  have he : pullbackTensorRoosModel l E W = ρ.comparison := by
    apply (pullbackTensorRoosModel_existsUnique l E W).unique
    · exact (pullbackTensorRoosModel_existsUnique l E W).exists.choose_spec
    · intro I hI
      rw [ρ.computes]
      rw [roosUnit_eq]
      rfl
  unfold pullbackTensorLimitRoos integralComparisonRoosBridge
  rw [he]

private theorem normalizedTensorComposite
    {𝒞 𝒟 𝒜 : Type*} [Category 𝒞] [Category 𝒟] [Category 𝒜]
    (L : 𝒞 ⥤ 𝒜) (H : 𝒟 ⥤ 𝒜)
    {A₀ A₁ A₂ A₃ B₀ B₁ : 𝒞} {Y₀ Y₁ Y₂ : 𝒟} {I : 𝒜}
    (α : I ⟶ L.obj A₀) (x : A₀ ⟶ A₁) (e : A₁ ⟶ A₂) (s : A₂ ⟶ A₃)
    (a : A₀ ⟶ B₀) (b : B₀ ⟶ B₁) (t : B₁ ⟶ A₃)
    (r₀ : L.obj B₁ ⟶ H.obj Y₀) (r : L.obj A₃ ⟶ H.obj Y₁)
    (v : Y₀ ⟶ Y₁) (q : Y₁ ⟶ Y₂) (q₀ : Y₀ ⟶ Y₂) (f : I ⟶ H.obj Y₂)
    (hm : x ≫ e ≫ s = a ≫ b ≫ t)
    (hr : L.map t ≫ r = r₀ ≫ H.map v) (hq : v ≫ q = q₀)
    (hf : α ≫ L.map a ≫ L.map b ≫ r₀ ≫ H.map q₀ = f) :
    (α ≫ L.map x) ≫ L.map e ≫ L.map s ≫ r ≫ H.map q = f := by
  rw [Category.assoc, ← L.map_comp_assoc, ← L.map_comp_assoc]
  simp only [Category.assoc]
  rw [hm, L.map_comp, L.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hr, ← H.map_comp, hq]
  exact hf

private theorem normalizedTensorComparisonSquare
    {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F G : 𝒞 ⥤ 𝒟)
    (δ : F ⟶ G) {A B C D : 𝒞} {Z : 𝒟}
    (j : A ⟶ B) (e : B ⟶ C) (a : A ⟶ D) (b : D ⟶ C)
    (s : G.obj C ⟶ Z) (s' : F.obj C ⟶ Z) (r : F.obj D ⟶ Z)
    (hp : j ≫ e = a ≫ b) (hs : δ.app C ≫ s = s') (hr : F.map b ≫ s' = r) :
    F.map j ≫ δ.app B ≫ G.map e ≫ s = F.map a ≫ r := by
  rw [← δ.naturality_assoc e, hs, ← F.map_comp_assoc, hp, F.map_comp,
    Category.assoc, hr]

/-- Transport the uniquely strict-Roos-normalized tensor to the specified calculus.
The comparison of reductions is fixed by their adjunctions to the same limit;
the comparison of tensors preserves their common tensor-Hom transpose.
Source: Stacks 06YY, 07A4, 0941; realization step 8 of scalar tower coherence.
(blueprint: stage3-pur-scalar-tensor-model-normalization) -/
def tensorModelRealization (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) :
    integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
      S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W := by
  let T := pullbackTensorCalculus l E W
  let a := T.adjunction.leftAdjointUniq S.adjunction
  exact pullbackTensorIntegralTensorModel l E W ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (NatIso.prod a a) T.systemClosed.tensor ≪≫
        Functor.isoWhiskerLeft (S.reduction.prod S.reduction)
          (CoefficientClosedStructure.comparison T.systemClosed S.systemClosed))
      (coefficientSequenceLimit l E W)

private theorem tensorModelRealization_hom (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (K N : DerivedCategory (integralTowerModules l E W)) :
    let T := pullbackTensorCalculus l E W
    let j := T.adjunction.leftAdjointUniq S.adjunction
    (tensorModelRealization l E W S).hom.app (K, N) =
      (pullbackTensorIntegralTensorModel l E W).hom.app (K, N) ≫
        (coefficientSequenceLimit l E W).map
          (T.systemClosed.tensor.map (Prod.mkHom (j.hom.app K) (j.hom.app N)) ≫
            (CoefficientClosedStructure.comparison T.systemClosed S.systemClosed).hom.app
              (S.reduction.obj K, S.reduction.obj N)) := rfl

attribute [local irreducible] tensorModelRealization pullbackTensorReferenceTensorModel

-- The normalization composes several derived-category naturality equations.
/-- The constructed tensor realization has the prescribed strict quotient formula
and Roos equation on every pair of whole-system coherent presentations.
Source: Stacks 03EL, 06YY, 07A4, 0941; steps 4 and 8 of
lem-pur-scalar-extension-tower-coherence.
(blueprint: stage3-pur-scalar-tensor-model-normalization)

Proof: choose the flat-term K-flat representatives P,Q. The two finite quotient
presentations identify C,D with their actual reductions. Tensor their chain
isomorphisms, and use the finite total-tensor evaluation comparison to obtain q
with all horizontal transitions. On a homogeneous generator its value is the
tensor of the two prescribed quotient sections, which is the displayed formula.
The two whole-system coherence conditions identify the adjunction transposes of
eC,eD with the strict tensor-unit maps. Their tensor therefore gives the same
whole-tower morphism as this q. Apply the normalized Roos bridge. Naturality of
the bridge and the universal tensor-model isomorphism give the FiveStepEquation.
The unit equation for the left-adjoint comparison identifies the transported
reduction with the same quotient augmentation; the closed tensor comparison
preserves the tensor-Hom transpose. Finally the defining normalization of
pullbackTensorIntegralTensorModel identifies the reference realization on P,Q
with integralCompletedTensorComparison. This proves the
equation for the constructed realization, without asserting that arbitrary
realizations are normalized or that finite derived evaluations are faithful.
Zero complexes, the first quotient, and empty schemes use the same formulas. -/
theorem tensorModelRealization_normalized (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W) :
    IsTensorModelNormalized l E W S ρ (tensorModelRealization l E W S) := by
  intro P Q C D eC eD κC κD hC hD _hpresC _hpresD hcC hcD
  obtain ⟨a, ha, hκa⟩ := coherentReferenceQuotientComparison l E W S P C eC κC hcC
  obtain ⟨b, hb, hκb⟩ := coherentReferenceQuotientComparison l E W S Q D eD κD hcD
  let T := pullbackTensorCalculus l E W
  let L := coefficientSequenceLimit l E W
  let R := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let U := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let H : (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) ⥤
      DerivedCategory (integralTowerModules l E W) :=
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  let δ := CoefficientClosedStructure.comparison T.systemClosed S.systemClosed
  let j := T.adjunction.leftAdjointUniq S.adjunction
  let t := (tensor l E W).mapIso (a.prod b)
  let q := U.mapIso t.symm ≪≫ pullbackTensorTensorTower l E W P.obj Q.obj
  refine ⟨q, strictQuotientTensorGenerator l E W P.obj Q.obj C D a b κC κD hκa hκb, ?_⟩
  have ht : T.systemClosed.tensor.map
      (Prod.mkHom (DerivedCategory.Q.map a.hom) (DerivedCategory.Q.map b.hom)) ≫
        (T.systemTensorModel.iso _ _ _ C D hC hD).inv =
      (pullbackTensorSystemModel l E W (R.obj P.obj) (R.obj Q.obj)
        (pullbackTensorReductionGood l E W P) (pullbackTensorReductionGood l E W Q)).inv ≫
          DerivedCategory.Q.map t.hom := by
    exact T.systemTensorModel.comparison.inv.naturality
      (Prod.mkHom
        (ObjectProperty.homMk (X := ⟨R.obj P.obj, pullbackTensorReductionGood l E W P⟩)
          (Y := ⟨C, hC⟩) a.hom)
        (ObjectProperty.homMk (X := ⟨R.obj Q.obj, pullbackTensorReductionGood l E W Q⟩)
          (Y := ⟨D, hD⟩) b.hom))
  have hm : T.systemClosed.tensor.map
      (Prod.mkHom (j.hom.app (DerivedCategory.Q.obj P.obj))
        (j.hom.app (DerivedCategory.Q.obj Q.obj))) ≫
      δ.hom.app (S.reduction.obj (DerivedCategory.Q.obj P.obj),
        S.reduction.obj (DerivedCategory.Q.obj Q.obj)) ≫
      S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom) ≫
      (S.systemTensorModel.iso _ _ _ C D hC hD).inv =
    T.systemClosed.tensor.map
      (Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app P)
        ((pullbackTensorReductionModel l E W).hom.app Q)) ≫
      (pullbackTensorSystemModel l E W (R.obj P.obj) (R.obj Q.obj)
        (pullbackTensorReductionGood l E W P) (pullbackTensorReductionGood l E W Q)).inv ≫
        DerivedCategory.Q.map t.hom := by
    have hpair : Prod.mkHom (j.hom.app (DerivedCategory.Q.obj P.obj))
        (j.hom.app (DerivedCategory.Q.obj Q.obj)) ≫ Prod.mkHom eC.hom eD.hom =
      Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app P)
        ((pullbackTensorReductionModel l E W).hom.app Q) ≫
      Prod.mkHom (DerivedCategory.Q.map a.hom) (DerivedCategory.Q.map b.hom) := by
      exact Prod.ext ha.symm hb.symm
    exact normalizedTensorComparisonSquare T.systemClosed.tensor S.systemClosed.tensor
      δ.hom _ _ _ _ _ _ _ hpair (coefficientTensorModelComparison l E W S T C D hC hD) ht
  let η := Functor.isoWhiskerRight
      (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
        (coefficientConstantTowerLimit l E W) ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)) ρ.comparison
  have hr := η.hom.naturality t.hom
  change L.map (DerivedCategory.Q.map t.hom) ≫
      (integralComparisonRoosBridge l E W ρ ((tensor l E W).obj (C, D))).hom =
    (integralComparisonRoosBridge l E W ρ ((tensor l E W).obj (R.obj P.obj, R.obj Q.obj))).hom ≫
      H.map (U.map t.hom) at hr
  have hq : U.map t.hom ≫ q.hom =
      (pullbackTensorTensorTower l E W P.obj Q.obj).hom := by
    exact (U.mapIso t).hom_inv_id_assoc _
  have he := (pullbackTensorIntegralTensorModel_existsUnique l E W).exists.choose_spec P Q
  change (pullbackTensorIntegralTensorModel l E W).app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
    (integralCompletedTensorComparison l E W).app (P, Q) ≪≫
      (pullbackTensorReferenceTensorModel l E W P Q).symm at he
  have hreference : (pullbackTensorIntegralTensorModel l E W).hom.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (pullbackTensorReferenceTensorModel l E W P Q).hom =
      (integralCompletedTensorComparison l E W).hom.app (P, Q) := by
    rw [← Iso.app_hom, he]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Iso.app_hom]
  rw [pullbackTensorReferenceTensorModel_hom] at hreference
  have hr' : L.map (DerivedCategory.Q.map t.hom) ≫
      (integralComparisonRoosBridge l E W ρ ((tensor l E W).obj (C, D))).hom =
    (pullbackTensorLimitRoos l E W
      ((tensor l E W).obj (R.obj P.obj, R.obj Q.obj))).hom ≫
      H.map (U.map t.hom) := by
    exact hr.trans (congrArg (fun f ↦ f ≫ H.map (U.map t.hom))
      (congrArg Iso.hom (roosBridge_eq l E W ρ
        ((tensor l E W).obj (R.obj P.obj, R.obj Q.obj)))).symm)
  have hfinal := normalizedTensorComposite L H
    ((pullbackTensorIntegralTensorModel l E W).hom.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
    (T.systemClosed.tensor.map
      (Prod.mkHom (j.hom.app (DerivedCategory.Q.obj P.obj))
        (j.hom.app (DerivedCategory.Q.obj Q.obj))) ≫
      δ.hom.app (S.reduction.obj (DerivedCategory.Q.obj P.obj),
        S.reduction.obj (DerivedCategory.Q.obj Q.obj)))
    (S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom))
    (S.systemTensorModel.iso _ _ _ C D hC hD).inv
    (T.systemClosed.tensor.map
      (Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app P)
        ((pullbackTensorReductionModel l E W).hom.app Q)))
    (pullbackTensorSystemModel l E W (R.obj P.obj) (R.obj Q.obj)
      (pullbackTensorReductionGood l E W P) (pullbackTensorReductionGood l E W Q)).inv
    (DerivedCategory.Q.map t.hom)
    (pullbackTensorLimitRoos l E W
      ((tensor l E W).obj (R.obj P.obj, R.obj Q.obj))).hom
    (integralComparisonRoosBridge l E W ρ ((tensor l E W).obj (C, D))).hom
    (U.map t.hom) q.hom (pullbackTensorTensorTower l E W P.obj Q.obj).hom
    ((integralCompletedTensorComparison l E W).hom.app (P, Q))
    ((Category.assoc _ _ _).trans hm) hr' hq hreference
  apply heq_of_eq
  simpa only [tensorModelRealization_hom, L, H, T, j, δ, Functor.comp_map,
    Functor.comp_obj] using hfinal

end WeilConjectures.ScalarExtensionTower
