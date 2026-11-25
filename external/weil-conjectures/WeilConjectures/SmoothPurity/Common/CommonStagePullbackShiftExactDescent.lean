/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
import all WeilConjectures.SmoothPurity.Sf.SfFrameworkCommonStageDescent

/-! # Exact descent of normalized pullback shifts

Source: the Weil-structures paragraph of the current blueprint.
(blueprint: lem-sf-common-stage-pullback-shift-exact-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
set_option allowUnsafeReducibility true in
attribute [local reducible] StageSystem.instCategoryPairCategory
  StageSystem.PairCategory.categoryStruct
attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive
  GeneralAlgebraicallyClosedCoefficients.stageTransition
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive
  GeneralAlgebraicallyClosedCoefficients.stageShift
attribute [local instance 5000] sfRationalConstructiblePretriangulated
  sfRationalConstructibleTriangulated sfRationalConstructibleShiftAdditive
  sfRationalConstructibleZero sfRationalConstructibleShift sfRationalLocalizationCommShift
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.preadditive
  GeneralAlgebraicallyClosedCoefficients.stagePretriangulated
  GeneralAlgebraicallyClosedCoefficients.transitionIso_commShift
  GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift
  GeneralAlgebraicallyClosedCoefficients.stageShiftAdditive
  GeneralAlgebraicallyClosedCoefficients.inclusion_exact
  GeneralAlgebraicallyClosedCoefficients.hasShift
  GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
  GeneralAlgebraicallyClosedCoefficients.shiftAdditive
  GeneralAlgebraicallyClosedCoefficients.zero_exists
  GeneralAlgebraicallyClosedCoefficients.pretriangulated
  GeneralAlgebraicallyClosedCoefficients.isTriangulated
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Pair
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  generalAlgebraicallyClosedConstructibleCategory

private theorem normalized_conjugate_heq
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B : C} {V W : D} (h : A = B) (h' : V = W)
    (i : A ⟶ B) (j : F.obj B ⟶ V) (k : V ⟶ W)
    (hi : HEq i (𝟙 B)) (hk : HEq k (𝟙 V)) :
    HEq (F.map i ≫ j ≫ k) j := by
  subst A
  subst W
  rw [eq_of_heq hi, eq_of_heq hk, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem exact_comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
    [Pretriangulated C] [Pretriangulated D] [Pretriangulated E]
    (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] : (F ⋙ G).IsTriangulated := inferInstance

private theorem pair_pullback_exact
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X Y : Scheme.{u})
    (M : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    [∀ E, (M.Φ E).CommShift ℤ] [∀ E, (M.Φ E).IsTriangulated]
    [∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j),
      NatTrans.CommShift
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).hom ℤ]
    [∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j),
      NatTrans.CommShift
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).transIso h).hom ℤ]
    (hc : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j),
      NatTrans.CommShift (M.β h).hom ℤ) :
    letI := pairCommShift M hc
    M.functor.IsTriangulated := by
  let := pairCommShift M hc
  constructor
  intro U hU
  obtain ⟨E, V, hV, ⟨e⟩⟩ :=
    (GeneralAlgebraicallyClosedCoefficients.distinguished_iff U).1 hU
  let : NatTrans.CommShift (M.ιCompFunctorIso E).hom ℤ := pairRestrictionShift M hc E
  let : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι E).IsTriangulated :=
    GeneralAlgebraicallyClosedCoefficients.inclusion_exact E
  let : (M.Φ E ⋙ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι E).IsTriangulated :=
    exact_comp (M.Φ E) ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι E)
  have : ((GeneralAlgebraicallyClosedCoefficients.inclusion E :
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E ⥤ _) ⋙ M.functor).IsTriangulated :=
    Functor.isTriangulated_of_iso (M.ιCompFunctorIso E).symm
  exact CategoryTheory.Pretriangulated.isomorphic_distinguished _
    (((GeneralAlgebraicallyClosedCoefficients.inclusion E :
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E ⥤ _) ⋙ M.functor).map_distinguished
      V hV) _
    (M.functor.mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso
        (GeneralAlgebraicallyClosedCoefficients.inclusion E :
          GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E ⥤ _) M.functor).symm.app V)

/-- Exact, transition-compatible finite-stage pullbacks induce an exact common-stage
pullback with the same normalized shift components.
Source: current blueprint Weil-structures paragraph and normalized common-stage descent.
(blueprint: lem-sf-common-stage-pullback-shift-exact-descent).
Proof: the coherent transition comparisons define the stage-system morphism. Its pair
shift is obtained by restricting to each stage and using transition compatibility.
Every distinguished triangle is isomorphic to the inclusion of a distinguished triangle
at one finite stage. The restriction isomorphism identifies its image with the exact
finite-stage pullback, proving exactness. Transport along normalized descent identifies
the resulting functor with the prescribed common-stage pullback. -/
theorem commonStagePullbackShiftExactDescent
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (r : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).CommShift ℤ)
    (hr : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      let := r E
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).IsTriangulated)
    (hc : ∀ {E L : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ L),
      let := r E
      let := r L
      let := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
      let := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω Y E L h
      NatTrans.CommShift (commonStagePullbackTransition l Ω f h).hom ℤ) :
    ∃ s : (commonStageDerivedPullback l Ω f).CommShift ℤ,
      (∀ (E : AlgebraicallyClosedCoefficients.Index l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) (n : ℤ),
        HEq (((commonStageDerivedPullback l Ω f).commShiftIso (self := s) n).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := X) E).obj K))
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := Y) E).map
            (((rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).commShiftIso
              (self := r E) n).hom.app K))) ∧
      (fun [_cs : (commonStageDerivedPullback l Ω f).CommShift ℤ] ↦
        (commonStageDerivedPullback l Ω f).IsTriangulated) (_cs := s) := by
  let : HasShift (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).PairCategory ℤ :=
    GeneralAlgebraicallyClosedCoefficients.hasShift
  let : HasShift (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).PairCategory ℤ :=
    GeneralAlgebraicallyClosedCoefficients.hasShift
  let : ∀ E, ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι E).CommShift ℤ :=
    fun E ↦ GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E
  let : ∀ E, ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι E).CommShift ℤ :=
    fun E ↦ GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E
  obtain ⟨hcoh, hM⟩ := commonStagePullbackNormalizedDescent l Ω f
  let M : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y) :=
    ⟨fun E ↦ rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f,
      commonStagePullbackTransition l Ω f, hcoh⟩
  let : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j),
      NatTrans.CommShift
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).hom ℤ :=
    fun {_ _} h ↦ GeneralAlgebraicallyClosedCoefficients.transitionIso_commShift _ _ h
  let : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j),
      NatTrans.CommShift
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).transIso h).hom ℤ :=
    fun {_ _} h ↦ GeneralAlgebraicallyClosedCoefficients.transitionIso_commShift _ _ h
  have hD : ∃ s : M.functor.CommShift ℤ,
      (∀ (E : AlgebraicallyClosedCoefficients.Index l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) (n : ℤ),
        HEq ((M.functor.commShiftIso (self := s) n).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := X) E).obj K))
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := Y) E).map
            (((rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).commShiftIso
              (self := r E) n).hom.app K))) ∧
      (fun [_cs : M.functor.CommShift ℤ] ↦ M.functor.IsTriangulated) (_cs := s) := by
    let := r
    let := hr
    let s := pairCommShift M hc
    let := s
    refine ⟨s, ?_, ?_⟩
    · intro E K n
      change HEq ((pairShiftIso M hc n).hom.app ⟨E, K⟩) _
      rw [pairShiftIso_hom_app]
      apply normalized_conjugate_heq M.functor
        (framework_shift_obj n E K) (framework_shift_obj n E ((M.Φ E).obj K)).symm
      · rw [framework_inclusion_shift_inv]
        exact eqToHom_heq_id_cod _ _ _
      · rw [framework_inclusion_shift_hom]
        exact eqToHom_heq_id_dom _ _ _
    · let : ∀ E, (M.Φ E).CommShift ℤ := r
      let : ∀ E, (M.Φ E).IsTriangulated := hr
      exact pair_pullback_exact l Ω X Y M hc
  change commonStageDerivedPullback l Ω f = M.functor at hM
  rw [hM]
  exact hD

end WeilConjectures
