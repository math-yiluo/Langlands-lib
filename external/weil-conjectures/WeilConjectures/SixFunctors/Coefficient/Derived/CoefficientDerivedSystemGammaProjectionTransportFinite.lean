/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData

/-! # Finite enriched transport before sections

This is the unsectioned finite fiber/base-change identity used by the final gamma
projection transport calculation
(blueprint: lem-coef-derived-system-gamma-projection-transport-final).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

section AbstractTransport

variable {A B C : Type*} [Category A] [Category B] [Category C]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
  (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
  (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
  (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)

-- Pull an internal-Hom map along a scalar adjunct before forming the enriched adjunct.
private theorem enriched_target_adjunct
    (hc : CoefficientEvaluationCompatible SA SB F μ)
    (P X : A) (N : B) (f : F.obj X ⟶ N) :
    HA.map (Prod.mkHom (𝟙 (op P)) (adj.homEquiv X N f)) ≫
        coefficientEnrichedAdjunctionMap SA SB F adj μ P N =
      adj.homEquiv _ _ (coefficientBaseChangeHom SA SB F μ P X ≫
        HB.map (Prod.mkHom (𝟙 (op (F.obj P))) f)) := by
  unfold coefficientEnrichedAdjunctionMap
  have hn := hc.naturality P X P (G.obj N) (𝟙 P) (adj.homEquiv X N f)
  simp only [op_id, F.map_id, adj.homEquiv_unit] at hn
  simp only [adj.homEquiv_unit]
  rw [← Category.assoc, ← adj.unit_naturality, Category.assoc, ← G.map_comp]
  rw [← Category.assoc (F.map _) (coefficientBaseChangeHom SA SB F μ P (G.obj N)), hn]
  have hf : F.map (adj.homEquiv X N f) ≫ adj.counit.app N = f := by
    have h := (adj.homEquiv X N).symm_apply_apply f
    rw [adj.homEquiv_counit] at h
    exact h
  rw [adj.homEquiv_unit] at hf
  simp only [Category.assoc, ← HB.map_comp, prod_comp,
    Category.id_comp, hf]

-- A unit-compatible projection carries adjuncts to evaluated scalar adjuncts.
private theorem adjunct_projection
    (V : B ⥤ C) (L : A ⥤ C) (R : C ⥤ A) (a : L ⊣ R)
    (ρ : F ⋙ V ≅ L) (π : G ⟶ V ⋙ R)
    (hu : ∀ X, adj.unit.app X ≫ π.app (F.obj X) =
      a.unit.app X ≫ R.map (ρ.inv.app X))
    (X : A) (Y : B) (Z : C) (f : F.obj X ⟶ Y) (g : V.obj Y ⟶ Z) :
    adj.homEquiv X Y f ≫ π.app Y ≫ R.map g =
      a.homEquiv X Z (ρ.inv.app X ≫ V.map f ≫ g) := by
  rw [adj.homEquiv_unit, Category.assoc,
    ← Category.assoc (G.map f) (π.app Y), π.naturality f]
  dsimp only [Functor.comp_map]
  simp only [Category.assoc]
  rw [← Category.assoc (adj.unit.app X) (π.app (F.obj X)), hu]
  simp only [a.homEquiv_unit, Functor.map_comp, Category.assoc]

end AbstractTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/--
The finite enriched uncurrying and evaluation transport, before applying derived
sections.  It is the strict internal-Hom equation whose image under integral sections,
followed by the scalar-section comparison, is the final gamma projection composite.
Source: Stacks 07A6, 08JA, 0D6E and 0941.
Proof: use the enriched uncurrying identity, the fiber evaluation comparison, and
naturality of reduction evaluation in the first variable.
(blueprint: lem-coef-derived-system-gamma-projection-transport-final)
-/
theorem coefficientDerivedSystemGammaProjectionTransport_finite
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ) :
    coefficientEnrichedAdjunctionMap S.integralClosed S.systemClosed S.reduction
        S.adjunction S.reductionTensor P N ≫
      (coefficientSequenceProjection l E W n).app
        ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N)) ≫
      (coefficientFiniteDerivedRestriction l E W n).map
        (S.fiberHom (S.reduction.obj P) N (S.reduction_normalized P) hN n).hom =
    (coefficientIntegralInternalHom l E W).map
        (Prod.mkHom (𝟙 (op P)) ((coefficientSequenceProjection l E W n).app N)) ≫
      coefficientEnrichedAdjunctionMap S.integralClosed (S.finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n)
        (coefficientFiniteAdjunction l E W n) (S.finiteTensor n) P
        ((coefficientSequenceDerivedEvaluation l E W n).obj N) ≫
      (coefficientFiniteDerivedRestriction l E W n).map
        ((coefficientFiniteInternalHom l E W n).map
          (Prod.mkHom ((S.reductionEvaluation n).hom.app P).op
            (𝟙 ((coefficientSequenceDerivedEvaluation l E W n).obj N)))) := by
  have _ := D
  let V := coefficientSequenceDerivedEvaluation l E W n
  let L := coefficientFiniteDerivedExtension l E W n
  let R := coefficientFiniteDerivedRestriction l E W n
  let a := coefficientFiniteAdjunction l E W n
  let HA := coefficientIntegralInternalHom l E W
  let HB := coefficientSequenceInternalHom l E W
  let HC := coefficientFiniteInternalHom l E W n
  let X := (coefficientSequenceLimit l E W).obj N
  let k := (S.reductionEvaluation n).inv.app X ≫ V.map (S.adjunction.counit.app N)
  have hk : a.homEquiv X (V.obj N) k =
      (coefficientSequenceProjection l E W n).app N := S.counit_projection N n
  have ht := enriched_target_adjunct S.integralClosed (S.finiteClosed n) L a
    (S.finiteTensor n) (S.finite_compatible n) P X (V.obj N) k
  rw [hk] at ht
  -- Move the system counit through the internal-Hom fiber comparison.
  have hf := S.fiber_naturality
    (S.reduction.obj P) (S.reduction.obj X) (S.reduction.obj P) N
    (S.reduction_normalized P) (S.reduction_normalized X)
    (S.reduction_normalized P) hN (𝟙 _) (S.adjunction.counit.app N) n
  simp only [op_id] at hf
  have hb := S.beta_evaluation P X n
  -- Evaluation of beta cancels the reduction comparison at the internal-Hom object.
  have hv :
      (S.reductionEvaluation n).inv.app (HA.obj (op P, X)) ≫
        V.map (coefficientBaseChangeHom S.integralClosed S.systemClosed
          S.reduction S.reductionTensor P X ≫
          HB.map (Prod.mkHom (𝟙 _) (S.adjunction.counit.app N))) ≫
        (S.fiberHom (S.reduction.obj P) N (S.reduction_normalized P) hN n).hom =
      coefficientBaseChangeHom S.integralClosed (S.finiteClosed n) L
          (S.finiteTensor n) P X ≫
        HC.map (Prod.mkHom ((S.reductionEvaluation n).hom.app P).op k) := by
    dsimp only [V, HA, HB, HC, L, X, k] at *
    rw [Functor.map_comp, Category.assoc, hf,
      ← Category.assoc _ _ (HC.map _), hb]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    change _ ≫ HC.map _ ≫ HC.map _ = _ ≫ HC.map _
    simp only [← HC.map_comp, prod_comp]
    rw [(coefficientSequenceDerivedEvaluation l E W n).map_id (S.reduction.obj P), op_id]
    congr 3
    exact Category.comp_id _
  -- Compare the two finite scalar adjuncts, retaining the first-variable transport.
  change (S.adjunction.homEquiv _ _ _) ≫ _ ≫ _ = _
  rw [adjunct_projection S.reduction S.adjunction V L R a
    (S.reductionEvaluation n) (coefficientSequenceProjection l E W n)
    (fun Y ↦ S.unit_projection Y n)]
  rw [hv]
  change _ = (HA.map _ ≫ coefficientEnrichedAdjunctionMap S.integralClosed
    (S.finiteClosed n) L a (S.finiteTensor n) P (V.obj N) ≫ R.map (HC.map _))
  rw [← Category.assoc, ht]
  rw [← a.homEquiv_naturality_right]
  congr 1
  change _ ≫ HC.map _ = (_ ≫ HC.map _) ≫ HC.map _
  simp only [Category.assoc, ← HC.map_comp, prod_comp, Category.id_comp]
  congr 3
  exact (Category.comp_id k).symm

end WeilConjectures
