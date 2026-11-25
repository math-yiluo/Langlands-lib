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

-- Normalize the two model equations before substituting the coefficient functors.
private theorem map_pair_factorization {C D : Type*} [Category C] [Category D]
    (B : C × C ⥤ D) {P₀ P₁ P₂ P₃ P₄ Q₀ Q₁ Q₂ Q₃ Q₄ : C}
    {aP : P₀ ⟶ P₁} {bP : P₁ ⟶ P₄}
    {pP : P₀ ⟶ P₂} {eP : P₂ ⟶ P₃} {dP : P₃ ⟶ P₄}
    {aQ : Q₀ ⟶ Q₁} {bQ : Q₁ ⟶ Q₄}
    {pQ : Q₀ ⟶ Q₂} {eQ : Q₂ ⟶ Q₃} {dQ : Q₃ ⟶ Q₄}
    (hP : aP ≫ bP = pP ≫ eP ≫ dP) (hQ : aQ ≫ bQ = pQ ≫ eQ ≫ dQ) :
    B.map (Prod.mkHom aP aQ) ≫ B.map (Prod.mkHom bP bQ) =
      B.map (Prod.mkHom pP pQ) ≫ B.map (Prod.mkHom eP eQ) ≫
        B.map (Prod.mkHom dP dQ) := by
  rw [← map_pair_comp, hP, hQ, map_pair_comp, map_pair_comp]

-- The representative equations compare independently specified derived models.
/-- The right derived path is the localization of its ordinary cochain path.
Source: the representative normalizations in lem-sf-canonical-reduction-tensor-pull.
(blueprint: lem-sf-canonical-reduction-tensor-pull-right).

Proof: apply naturality to the tensor representative and the reduction model.
Use the defining representative square for the system tensor on the left, and
for the ringed tensor on the right. The realization model identifies the input
and total-tensor reduction/pullback maps. Pasting these naturality and model
squares gives the displayed factorization. Every change of representative used
here is an isomorphism; no finite evaluation or conservativity is invoked. -/
theorem right_on_representatives
    (o : Operations l E) (m : RealizationModel l E o) (d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (P Q : (good l E V).FullSubcategory) :
    pre l E o m d f P Q ≫
        (rightPath l E o m d f).app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        post l E o m d f P Q = rightNormal l E o m d f P Q := by
  let F := ringedPull l E f
  let R := (calculus l E V).reduction
  let R' := (calculus l E U).reduction
  let S := pull l E f
  let B := (calculus l E U).systemClosed.tensor
  let Fc := (integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)
  let RV := (pullbackTensorOrdinaryReduction l E V).mapHomologicalComplex (.up ℤ)
  let RU := (pullbackTensorOrdinaryReduction l E U).mapHomologicalComplex (.up ℤ)
  let FP : (good l E U).FullSubcategory := ⟨Fc.obj P.obj, pull_good l E f P⟩
  let FQ : (good l E U).FullSubcategory := ⟨Fc.obj Q.obj, pull_good l E f Q⟩
  let T : (good l E V).FullSubcategory :=
    ⟨(total l E V).obj (P.obj, Q.obj), total_good l E V P Q⟩
  let FT : (good l E U).FullSubcategory := ⟨Fc.obj T.obj, pull_good l E f T⟩
  let TF : (good l E U).FullSubcategory :=
    ⟨(total l E U).obj (FP.obj, FQ.obj), total_good l E U FP FQ⟩
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
  let ψU := DerivedCategory.Q.map (tensorReductionStrictMap l E U FP.obj FQ.obj)
  let β := (proEtaleTensorPullbackTotalIso f
    ((PurCompactSupport.completed l E).ring V) ((PurCompactSupport.completed l E).ring U)
    ((PurCompactSupport.completed l E).pull f) P.obj Q.obj).inv
  let b := DerivedCategory.Q.map β
  let hP := pullbackTensorReductionGood l E V P
  let hQ := pullbackTensorReductionGood l E V Q
  let hFP := pullbackTensorReductionGood l E U FP
  let hFQ := pullbackTensorReductionGood l E U FQ
  let hSP := pullbackTensorSequenceGood l E f (RV.obj P.obj) hP
  let hSQ := pullbackTensorSequenceGood l E f (RV.obj Q.obj) hQ
  let zF := (pullbackTensorSystemModel l E U _ _ hFP hFQ).hom
  let zS := (pullbackTensorSystemModel l E U _ _ hSP hSQ).hom
  have hp : proEtaleFlatRepresentatives V ((PurCompactSupport.completed l E).ring V)
      P.obj := ⟨P.property.1, P.property.2⟩
  have hq : proEtaleFlatRepresentatives V ((PurCompactSupport.completed l E).ring V)
      Q.obj := ⟨Q.property.1, Q.property.2⟩
  let rV := (d.tensor V).ordinary.representative.hom.app (⟨P.obj, hp⟩, ⟨Q.obj, hq⟩)
  obtain ⟨hp', hq', hring⟩ := (proEtaleCanonicalTensorPullback f
    ((PurCompactSupport.completed l E).ring V) ((PurCompactSupport.completed l E).ring U)
    ((PurCompactSupport.completed l E).pull f)
    (d.tensor V).ordinary (d.tensor U).ordinary).2.exists.choose_spec P.obj Q.obj hp hq
  let rU := (d.tensor U).ordinary.representative.hom.app
    (⟨FP.obj, hp'⟩, ⟨FQ.obj, hq'⟩)
  change F.map rV ≫ (ringedTensorPull l E d f).hom.app _ ≫
    (d.tensor U).ordinary.tensor.map (Prod.mkHom (p P.obj) (p Q.obj)) =
    p T.obj ≫ b ≫ rU at hring
  have hμU := mu_model l E d U ⟨FP.obj, hp'⟩ ⟨FQ.obj, hq'⟩
  change R'.map rU ≫ (mu l E d U).app _ ≫
    B.map (Prod.mkHom (eU FP) (eU FQ)) = eU TF ≫ ψU ≫ zF at hμU
  have hδP := m.model f P (pull_good l E f P)
  have hδQ := m.model f Q (pull_good l E f Q)
  change (m.reductionPull f).hom.app _ ≫ S.map (eV P) ≫ s _ =
    R'.map (p P.obj) ≫ eU FP ≫ δ P.obj at hδP
  change (m.reductionPull f).hom.app _ ≫ S.map (eV Q) ≫ s _ =
    R'.map (p Q.obj) ≫ eU FQ ≫ δ Q.obj at hδQ
  have he := (pullbackTensorReductionModel l E U).hom.naturality
    (ObjectProperty.homMk (X := FT) (Y := TF) β)
  change R'.map b ≫ eU TF = eU FT ≫ DerivedCategory.Q.map (RU.map β) at he
  have hz := sys_naturality l E U _ _ _ _ hFP hFQ hSP hSQ
    (m.ordinary.reductionPullComplex l E f P.obj)
    (m.ordinary.reductionPullComplex l E f Q.obj)
  change DerivedCategory.Q.map ((sysTotal l E U).map
      (Prod.mkHom (m.ordinary.reductionPullComplex l E f P.obj)
        (m.ordinary.reductionPullComplex l E f Q.obj))) ≫ zS =
    zF ≫ B.map (Prod.mkHom (δ P.obj) (δ Q.obj)) at hz
  change _ = R'.map (p T.obj) ≫ eU FT ≫ DerivedCategory.Q.map (RU.map β) ≫ ψU ≫
    DerivedCategory.Q.map ((sysTotal l E U).map
      (Prod.mkHom (m.ordinary.reductionPullComplex l E f P.obj)
        (m.ordinary.reductionPullComplex l E f Q.obj))) ≫ zS
  have hμ := (mu l E d U).naturality (Prod.mkHom (p P.obj) (p Q.obj))
  change R'.map ((d.tensor U).ordinary.tensor.map
      (Prod.mkHom (p P.obj) (p Q.obj))) ≫ (mu l E d U).app _ =
    (mu l E d U).app _ ≫ B.map
      (Prod.mkHom (R'.map (p P.obj)) (R'.map (p Q.obj))) at hμ
  have hr := congrArg R'.map hring
  simp only [Functor.map_comp] at hr
  change R'.map (F.map rV) ≫
    (R'.map ((ringedTensorPull l E d f).hom.app _) ≫ (mu l E d U).app _ ≫
      B.map (Prod.mkHom ((m.reductionPull f).hom.app _) ((m.reductionPull f).hom.app _))) ≫
        B.map (Prod.mkHom (S.map (eV P) ≫ s (RV.obj P.obj))
          (S.map (eV Q) ≫ s (RV.obj Q.obj))) = _
  simp only [Category.assoc]
  refine (congrArg (fun t ↦ R'.map (F.map rV) ≫
    R'.map ((ringedTensorPull l E d f).hom.app _) ≫ (mu l E d U).app _ ≫ t)
      (map_pair_factorization B hδP hδQ)).trans ?_
  exact paste_right hμ hr hμU he hz

end WeilConjectures.IntegralSystemRealization.CanonicalTensorPullProof
