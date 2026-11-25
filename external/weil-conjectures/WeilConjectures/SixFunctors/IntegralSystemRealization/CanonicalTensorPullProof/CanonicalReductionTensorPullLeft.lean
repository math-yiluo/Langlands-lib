/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.CanonicalTensorPullProof.CanonicalReductionTensorPullModels

/-! # Normalizing one side of the reduction tensor square

Source: lem-sf-canonical-reduction-tensor-pull, resolution and normalization steps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization.CanonicalTensorPullProof
attribute [local irreducible] pullbackTensorCalculus
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

-- The representative equations compare independently specified derived models.
/-- The left derived path is the localization of its ordinary cochain path.
Source: the representative normalizations in lem-sf-canonical-reduction-tensor-pull.
(blueprint: lem-sf-canonical-reduction-tensor-pull-left).

Proof: apply naturality to the tensor representative and the reduction model.
Use the defining representative square for the system tensor on the left, and
for the ringed tensor on the right. The realization model identifies the input
and total-tensor reduction/pullback maps. Pasting these naturality and model
squares gives the displayed factorization. Every change of representative used
here is an isomorphism; no finite evaluation or conservativity is invoked. -/
theorem left_on_representatives
    (o : Operations l E) (m : RealizationModel l E o) (d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (P Q : (good l E V).FullSubcategory) :
    pre l E o m d f P Q ≫
        (leftPath l E o m d f).app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        post l E o m d f P Q = leftNormal l E o m d f P Q := by
  let F := ringedPull l E f
  let R := (calculus l E V).reduction
  let R' := (calculus l E U).reduction
  let S := pull l E f
  let B := (calculus l E U).systemClosed.tensor
  let Fc := (integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)
  let RV := (pullbackTensorOrdinaryReduction l E V).mapHomologicalComplex (.up ℤ)
  let Sc := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
  let T : (good l E V).FullSubcategory :=
    ⟨(total l E V).obj (P.obj, Q.obj), total_good l E V P Q⟩
  let FT : (good l E U).FullSubcategory := ⟨Fc.obj T.obj, pull_good l E f T⟩
  let eV (X : (good l E V).FullSubcategory) :=
    (pullbackTensorReductionModel l E V).hom.app X
  let eU (X : (good l E U).FullSubcategory) :=
    (pullbackTensorReductionModel l E U).hom.app X
  let p (X : CochainComplex (integralTowerModules l E V) ℤ) :=
    (integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app X
  let s (X : CochainComplex (coefficientSequenceModules l E V) ℤ) :=
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app X
  let δ (X : CochainComplex (integralTowerModules l E V) ℤ) :=
    DerivedCategory.Q.map (m.ordinary.reductionPullComplex l E f X)
  let ψV := DerivedCategory.Q.map (tensorReductionStrictMap l E V P.obj Q.obj)
  let c := DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app
    (RV.obj P.obj, RV.obj Q.obj))
  let hP := pullbackTensorReductionGood l E V P
  let hQ := pullbackTensorReductionGood l E V Q
  let hSP := pullbackTensorSequenceGood l E f (RV.obj P.obj) hP
  let hSQ := pullbackTensorSequenceGood l E f (RV.obj Q.obj) hQ
  let zV := (pullbackTensorSystemModel l E V _ _ hP hQ).hom
  let zS := (pullbackTensorSystemModel l E U _ _ hSP hSQ).hom
  have hp : proEtaleFlatRepresentatives V ((PurCompactSupport.completed l E).ring V)
      P.obj := ⟨P.property.1, P.property.2⟩
  have hq : proEtaleFlatRepresentatives V ((PurCompactSupport.completed l E).ring V)
      Q.obj := ⟨Q.property.1, Q.property.2⟩
  let rV := (d.tensor V).ordinary.representative.hom.app (⟨P.obj, hp⟩, ⟨Q.obj, hq⟩)
  have hμV := mu_model l E d V ⟨P.obj, hp⟩ ⟨Q.obj, hq⟩
  change R.map rV ≫ (mu l E d V).app _ ≫
    (calculus l E V).systemClosed.tensor.map (Prod.mkHom (eV P) (eV Q)) =
    eV T ≫ ψV ≫ zV at hμV
  have hsys := (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec
    (RV.obj P.obj) (RV.obj Q.obj) hP hQ
  change S.map zV ≫ (pullbackTensorSystemComparison l E f).hom.app _ ≫
    B.map (Prod.mkHom (s (RV.obj P.obj)) (s (RV.obj Q.obj))) =
    s _ ≫ c ≫ zS at hsys
  have hδT := m.model f T (pull_good l E f T)
  change (m.reductionPull f).hom.app _ ≫ S.map (eV T) ≫ s _ =
    R'.map (p T.obj) ≫ eU FT ≫ δ T.obj at hδT
  change _ = R'.map (p T.obj) ≫ eU FT ≫ δ T.obj ≫
    DerivedCategory.Q.map (Sc.map (tensorReductionStrictMap l E V P.obj Q.obj)) ≫ c ≫ zS
  have hn := (m.reductionPull f).hom.naturality rV
  change R'.map (F.map rV) ≫ (m.reductionPull f).hom.app _ =
    (m.reductionPull f).hom.app _ ≫ S.map (R.map rV) at hn
  have hσ := (pullbackTensorSystemComparison l E f).hom.naturality
    (Prod.mkHom (eV P) (eV Q))
  change S.map ((calculus l E V).systemClosed.tensor.map
      (Prod.mkHom (eV P) (eV Q))) ≫
      (pullbackTensorSystemComparison l E f).hom.app _ =
    (pullbackTensorSystemComparison l E f).hom.app _ ≫
      B.map (Prod.mkHom (S.map (eV P)) (S.map (eV Q))) at hσ
  have hs := (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.naturality
    (tensorReductionStrictMap l E V P.obj Q.obj)
  change S.map ψV ≫ s _ = s _ ≫
    DerivedCategory.Q.map (Sc.map (tensorReductionStrictMap l E V P.obj Q.obj)) at hs
  have hμ := congrArg S.map hμV
  simp only [Functor.map_comp] at hμ
  change R'.map (F.map rV) ≫
    ((m.reductionPull f).hom.app _ ≫ S.map ((mu l E d V).app _) ≫
      (pullbackTensorSystemComparison l E f).hom.app _) ≫
        B.map (Prod.mkHom (S.map (eV P) ≫ s (RV.obj P.obj))
          (S.map (eV Q) ≫ s (RV.obj Q.obj))) = _
  erw [map_pair_comp]
  simp only [Category.assoc]
  exact paste_left hn hσ hμ hsys hs hδT

end WeilConjectures.IntegralSystemRealization.CanonicalTensorPullProof
