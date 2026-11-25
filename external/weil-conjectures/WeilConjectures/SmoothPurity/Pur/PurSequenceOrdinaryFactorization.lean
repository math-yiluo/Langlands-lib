/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
import all WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTransitionComparison
import WeilConjectures.SmoothPurity.Pur.PurSequenceConstantRingFactorization
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The ordinary quotient projection and its constant-ring factorization

Source: Stacks Project, Tags 03D7 and 0940
(blueprint: lem-pur-sequence-ordinary-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u c v r
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
namespace WeilConjectures

open SemilinearSections

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private def coefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l E W :=
  NatTrans.ofOpSequence (fun n ↦ completedIntegralCommRingProjectionUnrestricted l E W n)
    (by
      intro n
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map,
        coefficientSequenceCommRingSystem, Functor.ofOpSequence_obj]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map_injective
      change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app V =
        (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app V ≫
          (integralCoefficientSheafTransition l E W n).hom.app V
      have h := congrArg (fun k ↦ k.hom.app V)
        (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
      simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h.symm)

attribute [local irreducible] CategoryTheory.constantSheaf
  completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted normalizedDVRQuotient
  completedIntegralCommRingProjectionUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence scalarReductionExtension
  coefficientFiniteDerivedExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory

private abbrev baseTopology := Scheme.ProEt.topology W
private abbrev finiteRings := fun n ↦ integralCoefficientCommRingSheaf l E W n
private abbrev finiteMaps := coefficientSequenceCommRingTransition l E W

private def completionCone :
    Cone (rings (baseTopology W) (finiteRings l E W) (finiteMaps l E W)) :=
  ⟨completedIntegralCommRingSheafUnrestricted l E W, coefficientCone l E W⟩

open SemilinearSections

private abbrev ordinaryGeometry :=
  seqSetProjection (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W)

private theorem evaluation_eq (n : ℕ) :
    evaluation (baseTopology W) (finiteRings l E W) (finiteMaps l E W) n =
      coefficientSequenceEvaluation l E W n := by
  rfl

private theorem restriction_eq :
    seqRestriction (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
      (completionCone l E W) = coefficientSequenceRestriction l E W := by
  unfold coefficientSequenceRestriction
  apply (coefficientSequenceRestriction_exists l E W).unique ?_
    (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  refine ⟨?_, ?_, ?_⟩
  · intro M n
    rw [seqRestrictionObjEq, evaluation_eq]
    rfl
  · intro M m n h V
    rfl
  · intro M N f n V
    rfl

private def ordinaryExtension :
    scalarReductionSource l E W ⥤ coefficientSequenceModules l E W :=
  seqExtension (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W)

private def ordinaryAdjunction :
    ordinaryExtension l E W ⊣ (ordinaryGeometry l E W).π.modules :=
  seqModuleAdjunction (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W)

private abbrev levelAdjunction (n : ℕ) :=
  (seqScalar (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W) n).ordinaryAdj

private theorem finiteRestriction_eq (n : ℕ) :
    scalarReductionRestriction l E W n =
      res ((completionCone l E W).π.app (op n)) := by
  rfl

private def ordinaryTensor (n : ℕ) :
    ordinaryExtension l E W ⋙ coefficientSequenceEvaluation l E W n ≅
      scalarReductionExtension l E W n :=
  eqToIso (congrArg (fun T ↦ ordinaryExtension l E W ⋙ T)
    (evaluation_eq l E W n).symm) ≪≫
  seqOrdinaryEvaluation (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W) n ≪≫
    (seqScalar (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
      (completionCone l E W) n).ordinaryAdj.leftAdjointUniq
      (Eq.mp (congrArg (fun G ↦ scalarReductionExtension l E W n ⊣ G)
        (finiteRestriction_eq l E W n)) (purSequenceFiniteAdjunction l E W n))

private def ordinaryProjectionNat (n : ℕ) :
    (ordinaryGeometry l E W).π.modules ⟶
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  Functor.whiskerLeft
    (seqRestriction (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
      (completionCone l E W)) (lim.π (op n)) ≫
    (Functor.isoWhiskerRight
      (seqEvaluationIso (baseTopology W) (finiteRings l E W) (finiteMaps l E W) n).symm
      (scalarReductionRestriction l E W n)).hom

private abbrev ordinaryProjection (N : coefficientSequenceModules l E W) (n : ℕ) :=
  (ordinaryProjectionNat l E W n).app N

private theorem ordinary_unit (M : scalarReductionSource l E W) (n : ℕ) :
    (ordinaryAdjunction l E W).unit.app M ≫
      ordinaryProjection l E W ((ordinaryExtension l E W).obj M) n ≫
        (scalarReductionRestriction l E W n).map ((ordinaryTensor l E W n).hom.app M) =
      (purSequenceFiniteAdjunction l E W n).unit.app M := by
  simp only [ordinaryTensor, eqToIso_refl, Iso.refl_trans, Iso.trans_hom,
    NatTrans.comp_app, Functor.map_comp, ordinaryProjection, ordinaryProjectionNat,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, lim.π_app]
  have h := unit_evaluation (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W) M n
  have h' := congrArg (· ≫ (scalarReductionRestriction l E W n).map
    (((levelAdjunction l E W n).leftAdjointUniq
      (purSequenceFiniteAdjunction l E W n)).hom.app M)) h
  have hu := h'.trans (Adjunction.unit_leftAdjointUniq_hom_app
    (levelAdjunction l E W n) (purSequenceFiniteAdjunction l E W n) M)
  simp only [Category.assoc] at hu ⊢
  exact hu

private theorem ab_function_heq {A B A' B' : AddCommGrpCat.{r}}
    (a : A = A') (b : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : eqToHom a.symm ≫ f ≫ eqToHom b = g) :
    HEq (fun x : A ↦ f x) (fun x : A' ↦ g x) := by
  subst a
  subst b
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact heq_of_eq (congrArg (fun k ↦ fun x ↦ k x) h)

private theorem module_forget_function_eq {R : Type*} [Ring R]
    {M N : ModuleCat.{r} R} (f : M ⟶ N) :
    (fun x : M ↦ ((forget₂ (ModuleCat.{r} R) AddCommGrpCat.{r}).map f) x) =
      (fun x : M ↦ f x) := rfl

private theorem presheaf_function_eq {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat} (N : PresheafOfModules.{r} R)
    {V V' : Cᵒᵖ} (f : V ⟶ V') :
    (fun x : N.obj V ↦ N.presheaf.map f x) = (fun x : N.obj V ↦ N.map f x) := rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual horizontal map, retaining the two literal section carriers.
Source: Stacks 0941 (blueprint: lem-pur-sequence-ordinary-factorization).
Proof: remove the source and target additive-group transports in the defining
transition equation. Forgetting linearity does not change the underlying function. -/
private theorem coefficientSequenceTransition_function_heq (N : coefficientSequenceModules l E W)
    {m n : ℕ} (h : n ≤ m) (V : W.ProEtᵒᵖ) :
    HEq (fun x : ((coefficientSequenceEvaluation l E W m).obj N).val.obj V ↦
      ((coefficientSequenceTransition l E W h).app N).val.app V x)
      (fun x : N.val.obj (op (m, V.unop)) ↦
        N.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) := by
  have hc := (coefficientSequenceTransition_exists l E W h).exists.choose_spec N V
  have he := ab_function_heq
    (coefficientSequenceEvaluationAb_eq l E W N m V)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W N h V) _ _ hc
  exact (heq_of_eq (module_forget_function_eq _)).symm.trans
    (he.trans (heq_of_eq (presheaf_function_eq N.val _)))

attribute [local irreducible] coefficientOrdinaryQuotientComponent coefficientOrdinaryQuotient
  coefficientQuotientNatTrans

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinaryTensor_eq (n : ℕ) :
    ordinaryTensor l E W n =
      eqToIso (congrArg (fun T ↦ ordinaryExtension l E W ⋙ T)
        (evaluation_eq l E W n).symm) ≪≫
      seqOrdinaryEvaluation (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
        (completionCone l E W) n ≪≫
        (seqScalar (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
          (completionCone l E W) n).ordinaryAdj.leftAdjointUniq
          (Eq.mp (congrArg (fun G ↦ scalarReductionExtension l E W n ⊣ G)
            (finiteRestriction_eq l E W n)) (purSequenceFiniteAdjunction l E W n)) := by
  rfl

private theorem quotient_mate_nat_eq {m n : ℕ} (h : n ≤ m) :
    coefficientOrdinaryQuotient l E W h =
      coefficientQuotientNatTrans (purSequenceFiniteAdjunction l E W m)
        (purSequenceFiniteAdjunction l E W n) (normalizedDVRModuleRes l E W h)
        (eqToIso (coefficientRestrictionComp l E W h)) := by
  unfold coefficientOrdinaryQuotient
  apply (coefficientOrdinaryQuotient_exists l E W h).unique
    (coefficientOrdinaryQuotient_exists l E W h).choose_spec.1
  intro M
  unfold coefficientOrdinaryQuotientComponent purSequenceFiniteAdjunction
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinary_transition_model
    (M : scalarReductionSource l E W) (m n : ℕ) (h : n ≤ m) :
    HEq
      ((coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M) ≫
        (normalizedDVRModuleRes l E W h).map ((ordinaryTensor l E W n).hom.app M))
      ((ordinaryTensor l E W m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M) := by
  exact generic_ordinary_transition_comparisons (baseTopology W) (finiteRings l E W)
    (finiteMaps l E W) (completionCone l E W) M m n h
    (scalarReductionRestriction l E W m) (finiteRestriction_eq l E W m)
    (purSequenceFiniteAdjunction l E W m)
    (scalarReductionRestriction l E W n) (finiteRestriction_eq l E W n)
    (purSequenceFiniteAdjunction l E W n)
    (normalizedDVRQuotient l E W h) (normalizedDVRModuleRes l E W h) rfl
    (coefficientRestrictionComp l E W h)
    (ordinaryExtension l E W ⋙ coefficientSequenceEvaluation l E W m)
    (ordinaryExtension l E W ⋙ coefficientSequenceEvaluation l E W n)
    (congrArg (fun T ↦ ordinaryExtension l E W ⋙ T) (evaluation_eq l E W m).symm)
    (congrArg (fun T ↦ ordinaryExtension l E W ⋙ T) (evaluation_eq l E W n).symm)
    ((coefficientSequenceEvaluation l E W m).obj ((ordinaryExtension l E W).obj M))
    ((coefficientSequenceEvaluation l E W n).obj ((ordinaryExtension l E W).obj M))
    (Functor.comp_obj (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W m) M).symm
    (Functor.comp_obj (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W n) M).symm
    ((coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M))
    (fun V ↦ coefficientSequenceTransition_function_heq l E W
      ((ordinaryExtension l E W).obj M) h V)
    (ordinaryTensor l E W m) (ordinaryTensor l E W n)
    (ordinaryTensor_eq l E W m) (ordinaryTensor_eq l E W n)
    (evaluatedIsoHom (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W m)
      (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W m)
      (ordinaryTensor l E W m) M)
    (evaluatedIsoHom (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W n)
      (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W n)
      (ordinaryTensor l E W n) M)
    (evaluatedIsoHom_heq (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W m)
      (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W m)
      (ordinaryTensor l E W m) M)
    (evaluatedIsoHom_heq (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W n)
      (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W n)
      (ordinaryTensor l E W n) M)
    (coefficientOrdinaryQuotient l E W h)
    (quotient_mate_nat_eq l E W h)
    ((coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M) ≫
      (normalizedDVRModuleRes l E W h).map ((ordinaryTensor l E W n).hom.app M))
    ((ordinaryTensor l E W m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M)
    (evaluatedIsoHom_precomp_heq (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W n)
      (D' := normalizedDVRModules l E W m) (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W n) (ordinaryTensor l E W n) M
      (normalizedDVRModuleRes l E W h)
      ((coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M)))
    (evaluatedIsoHom_compRight_heq (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W m)
      (D' := scalarReductionTarget l E W n) (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W m) (ordinaryTensor l E W m) M
      (scalarReductionExtension l E W n) (normalizedDVRModuleRes l E W h)
      (coefficientOrdinaryQuotient l E W h))

private theorem ordinary_transition (M : scalarReductionSource l E W)
    (m n : ℕ) (h : n ≤ m) :
    (coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M) ≫
      (normalizedDVRModuleRes l E W h).map ((ordinaryTensor l E W n).hom.app M) =
        (ordinaryTensor l E W m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M := by
  exact evaluatedIsoHom_transition_eq (A := scalarReductionSource l E W)
    (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W m)
    (D' := normalizedDVRModules l E W n) (ordinaryExtension l E W)
    (coefficientSequenceEvaluation l E W m) (coefficientSequenceEvaluation l E W n)
    (ordinaryTensor l E W m) (ordinaryTensor l E W n) M
    (normalizedDVRModuleRes l E W h)
    ((coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M))
    (coefficientOrdinaryQuotient l E W h) (ordinary_transition_model l E W M m n h)

private def ordinaryLimit : (ordinaryGeometry l E W).π.modules ≅
    coefficientSequenceRestriction l E W ⋙
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) :=
  Functor.isoWhiskerRight (eqToIso (restriction_eq l E W)) lim

private theorem ordinaryProjection_limit (N : coefficientSequenceModules l E W) (n : ℕ) :
    ordinaryProjection l E W N n = (ordinaryLimit l E W).hom.app N ≫
      limit.π ((coefficientSequenceRestriction l E W).obj N) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app N := by
  dsimp only [ordinaryProjection, ordinaryProjectionNat, ordinaryLimit,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, lim.π_app]
  erw [limMap_π_assoc]
  apply congrArg (fun f ↦ limit.π
    ((seqRestriction (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
      (completionCone l E W)).obj N) (op n) ≫ f)
  rw [evaluation_comparison_eq]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans]

private theorem ordinary_transpose (M : scalarReductionSource l E W)
    (N : coefficientSequenceModules l E W)
    (h : M ⟶ (ordinaryGeometry l E W).π.modules.obj N) (n : ℕ) :
    (purSequenceFiniteAdjunction l E W n).homEquiv M
      ((coefficientSequenceEvaluation l E W n).obj N)
      ((ordinaryTensor l E W n).inv.app M ≫
        (coefficientSequenceEvaluation l E W n).map
          (((ordinaryAdjunction l E W).homEquiv M N).symm h)) =
      h ≫ ordinaryProjection l E W N n :=
  transpose_of_unit (ordinaryAdjunction l E W) (purSequenceFiniteAdjunction l E W n)
    (ordinaryTensor l E W n) (ordinaryProjectionNat l E W n)
    (fun M ↦ ordinary_unit l E W M n) M N h

private theorem ordinaryAdjoints_exist : Nonempty (PurSequenceOrdinaryAdjoints l E W) := by
  refine ⟨{
    p := (ordinaryGeometry l E W).π
    constant := (ordinaryGeometry l E W).inverseUnderlying
    quotient := ?_
    pullback := ordinaryExtension l E W
    pullback_additive := seqExtension_additive (baseTopology W) (finiteRings l E W)
      (finiteMaps l E W) (completionCone l E W)
    adjunction := ordinaryAdjunction l E W
    limit := ordinaryLimit l E W
    tensor := ordinaryTensor l E W
    tensor_transition := ordinary_transition l E W
    projection := ordinaryProjection l E W
    projection_limit := ordinaryProjection_limit l E W
    transpose := ordinary_transpose l E W
  }⟩
  intro n V x
  rfl

/-- The ordinary quotient projection factors through the constant completed ring.
Source: Stacks 0940 (constant/limit ringed projection) and 03D7 (module adjunction)
(blueprint: lem-pur-sequence-ordinary-factorization).

Proof: form the cone of the completed-ring projections to the quotient tower and
apply the sequence-site constant/limit construction. Its module pullback is the
strict system of scalar extensions. Compare each scalar adjunction with the
recorded finite adjunction by uniqueness of left adjoints. The comparison preserves
their units, hence their quotient mates and tensor transitions. Projection to each
coordinate of the limit gives the displayed transpose equation. Factor the ring
map through the constant completed ring: the first geometric morphism is identity
on sheaves and restricts scalars, and the second is the constant/limit morphism
with identity structural map. Constant-ring sequence modules are towers of base
modules, with identity section identifications. These identifications give the
three composition comparisons, the structural-map equation, the restriction and
limit comparisons. Scalar restriction preserves kernels and sheafified cokernels,
so it preserves finite limits and finite colimits. Every construction uses actual
section restrictions; no surjectivity or flatness of a quotient map is used. -/
theorem purSequenceOrdinaryFactorization :
    ∃ O : PurSequenceOrdinaryAdjoints l E W,
      Nonempty (PurSequenceRingedFactorization l E W O) := by
  obtain ⟨O⟩ := ordinaryAdjoints_exist l E W
  exact ⟨O, purSequenceConstantRingFactorization l E W O⟩

end WeilConjectures

-- Restore the incoming instance registration after using compact local sheaf instances.
attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
