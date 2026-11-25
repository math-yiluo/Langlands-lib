/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismStrictQuotientModels
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison

/-! # Inverse image and the strict quotient Roos cocone

Source: Stacks 03CZ, 03EK, 06YY, 08TC and 0941; the strict quotient-cone argument
of `lem-trf-isomorphism-multiplication-cone-descent`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local instance 3000] integralTowerHasDerivedCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralOperationsGoodComplex coefficientSequenceLimit TrfCompletionRoosNormalized
  integralDerivedPullback integralDerivedPullbackComparison integralPullbackDescent
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategory DerivedCategory.Q
  integralOperationsRoosMap

-- The existing exactness proof constructs this equivalence internally; retain it here
-- so that the general projection-normalized Roos comparison can be applied.
private theorem quotientModuleEquivalence {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj RY ⟶ RX)
    [IsIso c] : (isoSectionwiseModuleInverseImage g c).IsEquivalence := by
  let F := proEtaleIsoPostcompose g
  let G := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt :=
    CategoryTheory.Equivalence.mk F G e.2.1.some.symm e.2.2.1.some
  have : E.functor.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous g
  have : E.inverse.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    proEtaleIsoPostcompose_isContinuous (inv g)
  let adj := E.toAdjunction
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{max u (t + 1)})
    (ProEt.topology X) (ProEt.topology Y)
  let φ := inv c
  let ψ : RY ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj RX :=
    shAdj.unit.app RY ≫ (G.sheafPushforwardContinuous _ _ _).map c
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    have h : ψ ≫ (G.sheafPushforwardContinuous RingCat _ _).map φ =
        shAdj.unit.app RY := by
      dsimp only [ψ]
      rw [Category.assoc, ← Functor.map_comp]
      rw [show c ≫ φ = 𝟙 ((isoSectionwiseInverseImage g RingCat).obj RY) by simp [φ]]
      exact (congrArg (shAdj.unit.app RY ≫ ·)
        ((G.sheafPushforwardContinuous RingCat _ _).map_id
          ((isoSectionwiseInverseImage g RingCat).obj RY))).trans (Category.comp_id _)
    exact (congrArg (fun f ↦ f.hom) h).symm
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (E.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((E.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((E.functor.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c := congrArg (fun h ↦ φ ≫ h ≫ c) ht
        _ = _ := by simp [φ]
    exact congrArg (fun f ↦ f.hom) hh
  let EM := SheafOfModules.pushforwardPushforwardEquivalence E φ ψ H₁ H₂
  exact EM.isEquivalence_functor

private theorem quotientDifferenceSquare
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (scalarRoosBoundary C) ≫
        piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n)) =
      piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n)) ≫
        scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  change G.map (scalarRoosBoundary C) ≫ piComparison G (fun n : ℕ ↦ C.obj (op n)) =
    piComparison G (fun n : ℕ ↦ C.obj (op n)) ≫ scalarRoosBoundary (C ⋙ G)
  apply Pi.hom_ext
  intro n
  have hC := (towerTransitionEndomorphism_eq_iff
    (integralOperationsTowerStep C) (scalarRoosBoundary C)).mp rfl n
  have hG := (towerTransitionEndomorphism_eq_iff
    (integralOperationsTowerStep (C ⋙ G)) (scalarRoosBoundary (C ⋙ G))).mp rfl n
  simp only [Category.assoc]
  rw [piComparison_comp_π, ← G.map_comp, hC, G.map_sub, G.map_comp]
  dsimp only [Functor.comp_obj] at hG
  erw [hG]
  simp only [Preadditive.comp_sub, ← Category.assoc, piComparison_comp_π]
  rfl

private def quotientRoosIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [F.IsEquivalence] :
    integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ⋙
        integralOperationsRoosFunctor :=
  NatIso.ofComponents (fun C ↦
    @asIso _ _ _ _ (scalarRoosMap F C) (podReindexingRoosComparison F C))
    (by
      intro C C' a
      exact podReindexingRoosNaturality F a)

private theorem quotientRoosSecond
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (i j : ℤ) (hij : i + -1 = j) :
    (scalarRoosMap F C).f i ≫
        (CochainComplex.mappingCocone.snd
          (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)))).v i j hij =
      F.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v i j hij) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ C.obj (op n))).f j := by
  subst j
  exact (podReindexingRoosCoordinates F C).2 i

attribute [local irreducible] trfQuotientTowerFunctor

/-- Exact inverse image commutes with the actual strict Roos cocone by the diagonal
canonical product comparison, naturally in good complexes.
Source: Stacks 0941 (lemma-derived-limit-is-ok), 08TC, and steps 1 and 5 of
lem-trf-isomorphism-multiplication-cone-descent.
(blueprint: lem-trf-isomorphism-quotient-roos-comparison).

Proof in words: inverse image under a site equivalence, with action transported through
the inverse completed coefficient isomorphism, preserves sectionwise products. Its
product comparison is therefore invertible in every degree. Project onto the nth factor:
both composites with the tower shift are inverse image of the (n+1)st projection followed
by the nth transition. Product extensionality and additivity give the difference square.
On the cocone take this same product comparison in both coordinates, with zero mixed
entries. The difference square and its chain-map equation imply that the diagonal map
commutes with d(b,a)=(-db-(1-s)a,da). The inverse diagonal map satisfies the same
calculation, so it is an isomorphism. Product projection identities and cocone coordinate
extensionality show naturality in every chain map. The two resulting projection
equations are exactly the displayed formulas, with the shifted coordinate in degree p.
This works for the zero complex as well and uses no boundedness or completeness. -/
theorem isomorphismQuotientRoosComparison
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    (∀ Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
      IsIso (trfQuotientProductComparison l E g Q.obj)) ∧
    (∀ Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (trfInverseImageComplex l E g).map (trfQuotientDifference l E Y Q.obj) ≫
            trfQuotientProductComparison l E g Q.obj =
          trfQuotientProductComparison l E g Q.obj ≫ trfInverseQuotientDifference l E g Q.obj) ∧
    ∃ (eta : (integralOperationsGoodComplex l E Y).ι ⋙
          trfQuotientTowerFunctor l E Y ⋙ integralOperationsRoosFunctor ⋙
            trfInverseImageComplex l E g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ trfQuotientTowerFunctor l E Y ⋙
          trfInverseImageTower l E g ⋙ integralOperationsRoosFunctor),
      (∀ Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        eta.hom.app Q ≫ CochainComplex.mappingCocone.fst
            (trfInverseQuotientDifference l E g Q.obj) =
          (trfInverseImageComplex l E g).map
              (CochainComplex.mappingCocone.fst (trfQuotientDifference l E Y Q.obj)) ≫
            trfQuotientProductComparison l E g Q.obj) ∧
      -- Equality on the shifted b coordinate; together these specify a diagonal map.
      (∀ (Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (p : ℤ),
        (eta.hom.app Q).f (p + 1) ≫
            (CochainComplex.mappingCocone.snd
              (trfInverseQuotientDifference l E g Q.obj)).v (p + 1) p
                (add_neg_cancel_right p 1) =
          (inverseImageIntegralModules l E g).map
              ((CochainComplex.mappingCocone.snd
                (trfQuotientDifference l E Y Q.obj)).v (p + 1) p
                  (add_neg_cancel_right p 1)) ≫
            (trfQuotientProductComparison l E g Q.obj).f p) := by
  let F := inverseImageIntegralModules l E g
  let G := trfInverseImageComplex l E g
  let : F.IsEquivalence := quotientModuleEquivalence g _
  let : G.IsEquivalence :=
    (F.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  refine ⟨?_, ?_, ?_⟩
  · intro Q
    change IsIso (piComparison G _)
    infer_instance
  · intro Q
    let C := (trfQuotientTowerFunctor l E Y).obj Q.obj
    change G.map (scalarRoosBoundary C) ≫ piComparison G (fun n : ℕ ↦ C.obj (op n)) =
      piComparison G (fun n : ℕ ↦ C.obj (op n)) ≫ scalarRoosBoundary (C ⋙ G)
    exact quotientDifferenceSquare F C
  · let eta := Functor.isoWhiskerLeft
        ((integralOperationsGoodComplex l E Y).ι ⋙ trfQuotientTowerFunctor l E Y)
        (quotientRoosIso F)
    refine ⟨eta, ?_, ?_⟩
    · intro Q
      exact (podReindexingRoosCoordinates F
        ((trfQuotientTowerFunctor l E Y).obj Q.obj)).1
    · intro Q p
      exact quotientRoosSecond F ((trfQuotientTowerFunctor l E Y).obj Q.obj)
        (p + 1) p (add_neg_cancel_right p 1)

end WeilConjectures
