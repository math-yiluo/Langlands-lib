/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleCoherentTotalTensorPullbackComparison
import WeilConjectures.SmoothPurity.Ringed.RingedDerivedTensorComparisonAssociativity
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatRepresentatives
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatDiagrams
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-! # Associativity on flat K-flat pullback tensor representatives

Source: Stacks Project, Tags 07A4, 06YS and 03EL.
(blueprint: lem-pur-finite-pullback-tensor-associativity-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory.MonoidalCategory
open CategoryTheory.RingedForgetTensorTransposition
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
  finiteIntrinsicClosed finiteIntrinsicTensorModels
  proEtaleTensorPullbackTotalIso proEtaleTensorPullbackTotal
  SheafOfModules.monoidalCategory coefficientTensorGenerator
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  finiteIntrinsicDerivedTensor coefficientTotalTensor coefficientKFlatInclusion
  coefficientFiniteInternalHom FinitePullbackTensorRep.totalTensor
  CoefficientClosedStructure.tensor
attribute [local semireducible] FinitePullbackTensorRep.pull
attribute [local implicit_reducible] FinitePullbackTensorRep.pull

attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived FinitePullbackTensorRep.ordinary_additive
  FinitePullbackTensorRep.ordinary_limits FinitePullbackTensorRep.ordinary_colimits
attribute [local implicit_reducible] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived

private theorem canonical_representative_square {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y n) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y n) Q)
    (hFP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n)
      ((FinitePullbackTensorRep.pull l E f n).obj P))
    (hFQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n)
      ((FinitePullbackTensorRep.pull l E f n).obj Q))
    {γ : (FinitePullbackTensorRep.pull l E f n).obj
        ((coefficientTotalTensor.{u, u+1, u} (ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q)) ⟶
      (coefficientTotalTensor.{u, u+1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
          (((FinitePullbackTensorRep.pull l E f n).obj P),
            ((FinitePullbackTensorRep.pull l E f n).obj Q))}
    (hγ : γ = (proEtaleTensorPullbackTotalIso f (integralCoefficientCommRingSheaf l E Y n)
          (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
          P Q).inv) :
    (finiteDerivedPullback l E n f).map
        ((finiteIntrinsicTensorModels l E Y n).iso (ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n) (finiteIntrinsicClosed l E Y n)
          P Q hP hQ).hom ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
      (finiteIntrinsicClosed l E X n).tensor.map (Prod.mkHom
        ((FinitePullbackTensorRep.factors l E f n).hom.app P)
        ((FinitePullbackTensorRep.factors l E f n).hom.app Q)) =
    (FinitePullbackTensorRep.factors l E f n).hom.app
        ((coefficientTotalTensor.{u, u+1, u} (ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q)) ≫
      DerivedCategory.Q.map γ ≫
      ((finiteIntrinsicTensorModels l E X n).iso (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n) (finiteIntrinsicClosed l E X n)
        ((FinitePullbackTensorRep.pull l E f n).obj P)
        ((FinitePullbackTensorRep.pull l E f n).obj Q) hFP hFQ).hom := by
  rw [hγ]
  have h := finitePullbackTensor_ringed_kflat_square l E f n P Q hP hQ hFP hFQ
  dsimp only [FinitePullbackTensorRep.tensor, finiteIntrinsicDerivedTensor] at h
  simp only [comparison_eq] at h
  exact h

-- The four model squares involve several concrete derived-category instances.
/-- Associativity for the canonical comparison on localized flat K-flat triples.
Source: Stacks 07A4, lemma-pullback-tensor-product, its total-tensor construction;
06YS and 07A2 for the flat K-flat total-tensor representatives.
(blueprint: lem-pur-finite-pullback-tensor-associativity-representatives).
Proof: total tensors of flat K-flat complexes are again flat K-flat. Apply the
representative normalization square to (A,B), (B,C) and their total tensors.
On each tridegree summand, ordinary pullback tensor comparison sends the
pullback of (x tensor y) tensor z to f*x tensor (f*y tensor f*z) along both
routes. The ordinary associator only changes parentheses, so this equality
has no extra Koszul sign. It respects the signed total differential.
Tensor generators, sheafification and the total coproduct injections determine
the chain maps. Apply the derived quotient to their equality and insert the
specified finite tensor-model comparisons and unit-normalized realization.
The representative associators and the natural comparison isomorphisms cancel
the intermediate conjugations, giving precisely the displayed equation.
This calculation only treats the displayed flat K-flat triples. -/
theorem finitePullbackTensor_associativity_representatives {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (A B C : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hA : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) A)
    (hB : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) B)
    (hC : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) C) :
    let M := DerivedCategory.Q.obj A
    let N := DerivedCategory.Q.obj B
    let P := DerivedCategory.Q.obj C
    (finiteDerivedPullback l E n f).map
      ((finiteIntrinsicClosed l E Y n).monoidal.associator M N P).hom ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M
        ((finiteIntrinsicDerivedTensor l E Y n).obj (N,P))).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (𝟙 _) ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) N P).hom) =
    ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
      ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) P).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M N).hom (𝟙 _)) ≫
      ((finiteIntrinsicClosed l E X n).monoidal.associator
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)
        ((finiteDerivedPullback l E n f).obj P)).hom := by
  let R := integralCoefficientCommRingSheaf l E Y n
  let R' := integralCoefficientCommRingSheaf l E X n
  let S := finiteIntrinsicClosed l E Y n
  let SU := finiteIntrinsicClosed l E X n
  let T := finiteIntrinsicTensorModels l E Y n
  let TU := finiteIntrinsicTensorModels l E X n
  let F := (proEtaleRingModulePullback f R R'
    (pullbackTensorCoefficientIso l E f n)).mapHomologicalComplex (.up ℤ)
  let r := finiteDerivedPullback l E n f
  let t := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y) R
  let ρ := @finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY
  obtain ⟨e, he, hc⟩ := proEtaleCoherentTotalTensorPullbackComparison f R R'
    (pullbackTensorCoefficientIso l E f n)
  have hρ : ∀ (L M L' M' : proEtaleDerivedCategory Y
      (finiteCoefficientRing l E (n + 1))) (v : L ⟶ L') (w : M ⟶ M'),
      r.map (S.tensor.map (v, w)) ≫ (ρ L' M').hom =
        (ρ L M).hom ≫ SU.tensor.map (r.map v, r.map w) := by
    intro L M L' M' v w
    have h := (finitePullbackTensorConstructionIso l E f n).hom.naturality
      (Prod.mkHom v w)
    dsimp only [Functor.comp_map, Functor.prod_map] at h
    simpa only [constructionIso_app, r, S, SU, ρ,
      finiteIntrinsicDerivedTensor, Prod.mkHom, Functor.comp_obj,
      Functor.prod_obj] using h
  have hflat (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ)
      (hP : proEtaleFlatRepresentatives Y R P)
      (hQ : proEtaleFlatRepresentatives Y R Q) :
      proEtaleFlatRepresentatives Y R (t.obj (P, Q)) := by
    have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      R P Q hP.1 hQ.1 hP.2 hQ.2
    exact ⟨h.1, h.2.1⟩
  have hF (P : CochainComplex (normalizedDVRModules l E Y n) ℤ)
      (hP : proEtaleFlatRepresentatives Y R P) :
      proEtaleFlatRepresentatives X R' (F.obj P) := by
    dsimp only [F, FinitePullbackTensorRep.pull]
    exact (proEtaleCanonicalTensorPullback f R R' (pullbackTensorCoefficientIso l E f n)
      (pullbackTensorFiniteModel l E Y n) (pullbackTensorFiniteModel l E X n)).1 P hP
  have hAB := hflat A B hA hB
  have hBC := hflat B C hB hC
  have hFA := (hF A hA).1
  have hFB := (hF B hB).1
  have hFC := (hF C hC).1
  have hFAB := (hF _ hAB).1
  have hFBC := (hF _ hBC).1
  have coherent (W : Scheme.{u}) :
      ∃ β : @SymmetricCategory (normalizedDVRDerived l E W n) _
          (finiteIntrinsicClosed l E W n).monoidal,
        Nonempty (RingedDerivedTensorCoherence.{u+1, u, u} (ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n)
          (finiteIntrinsicTensorModels l E W n) β) := by
    delta finiteIntrinsicClosed finiteIntrinsicTensorModels
    exact (coefficientDerivedSystemEvaluationCalculus l E W).choose.finite_tensor_coherence n
  obtain ⟨β, ⟨K⟩⟩ := coherent Y
  obtain ⟨βU, ⟨KU⟩⟩ := coherent X
  exact ringedDerivedTensorComparison_associativity.{u+1, u, u, u+2, u+1, u, u, u+2}
    (ProEt.topology Y) R S T (ProEt.topology X) R' SU TU
    (proEtaleRingModulePullback f R R' (pullbackTensorCoefficientIso l E f n))
    r (FinitePullbackTensorRep.factors l E f n) ρ hρ e.symm hc K KU
    (fun P Q hP hQ hFP hFQ ↦
      canonical_representative_square l E f n P Q hP hQ hFP hFQ (he P Q))
    A B C hA.1 hB.1 hC.1 hFA hFB hFC hFAB hFBC

end WeilConjectures
