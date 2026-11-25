/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedTensorAssociativity
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedEvaluationProjection
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedTensorHorizontal
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Internal-Hom fibers of normalized coefficient systems

Source: Stacks 07A4, 08J9, 0A95 and 0941; semilinear finite-prefix adjunction
(blueprint: lem-coef-normalized-internal-hom-fibers).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b v w c r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Preservation of internal composition for an evaluation-defined comparison.
Source: Stacks 08J9, 0A98
(blueprint: lem-coef-normalized-internal-hom-fibers). -/
def CoefficientInternalHomComposition
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ P Q V : A,
    F.map (SA.composition P Q V) ≫ coefficientBaseChangeHom SA SB F μ P V =
      μ.hom.app (HA.obj (op Q, V), HA.obj (op P, Q)) ≫
        SB.tensor.map
          (Prod.mkHom (coefficientBaseChangeHom SA SB F μ Q V)
            (coefficientBaseChangeHom SA SB F μ P Q)) ≫
        SB.composition (F.obj P) (F.obj Q) (F.obj V)

attribute [local irreducible] CoefficientInternalHomComposition

/-- The local Hom comparisons, without any global-sections data.
Source: Stacks 08J9, 0A95 and 0941
(blueprint: lem-coef-normalized-internal-hom-fibers). -/
structure CoefficientNormalizedInternalHomFibers
    (R : CoefficientDerivedSystemReduction l E W)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) where
  /-- Reduction preserves internal composition as a system map. -/
  reduction_composition : CoefficientInternalHomComposition R.integralClosed R.systemClosed
    R.reduction R.reductionTensor
  /-- Finite scalar comparison preserves internal composition. -/
  finite_composition : ∀ n : ℕ, CoefficientInternalHomComposition
    R.integralClosed (R.finiteClosed n)
    (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n)
  /-- Internal Hom on normalized inputs has exactly the finite internal-Hom fibers. -/
  fiberHom : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E W n).obj
          ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteInternalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- The fiber identification is induced by simultaneous system evaluation. -/
  fiber_evaluation : ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ),
    (R.evaluationTensor n).inv.app
        ((coefficientSequenceInternalHom l E W).obj (op M, N), M) ≫
      (coefficientSequenceDerivedEvaluation l E W n).map (R.systemClosed.evaluation M N) =
    (R.finiteClosed n).tensor.map
        (Prod.mkHom ((fiberHom M N hM hN n).hom) (𝟙 _)) ≫
      (R.finiteClosed n).evaluation
        ((coefficientSequenceDerivedEvaluation l E W n).obj M)
        ((coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- The adjunct of the actual `coefficientSequenceDerivedTransition` on internal Hom,
  under `fiberHom` at m and n, is c_(m,n) followed by RHom(alpha_M inverse, alpha_N).
  Here c_(m,n) transposes reduced finite evaluation using `Q.tensor`,
  whose `tensor_model` fixes its comparison on every pair of K-flat representatives. -/
  fiber_transition : CoefficientFiberTransition l E W R.toCoefficientDerivedSystemTensors
    Q fiberHom
private theorem uncurry_formula {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    (T P Q : D) (t : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm t =
      S.tensor.map (Prod.mkHom t (𝟙 P)) ≫ S.evaluation P Q := by
  change (@MonoidalCategory.tensorRight D _ S.monoidal P).map t ≫
    S.evaluation P Q = _
  let _ := S.monoidal
  simp [CoefficientClosedStructure.tensor]

private theorem uncurry_precomp {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {T T' P Q : D} (a : T' ⟶ T) (t : T ⟶ H.obj (op P, Q)) :
    (S.transpose T' P Q).symm (a ≫ t) =
      S.tensor.map (Prod.mkHom a (𝟙 P)) ≫ (S.transpose T P Q).symm t := by
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    Prod.sectR] using (S.adjunction P).homEquiv_naturality_left_symm a t

section ClosedCalculus

variable {A : Type*} [Category* A] {H : Aᵒᵖ × A ⥤ A}
  (S : CoefficientClosedStructure H)

private theorem evaluation_target (K N N' : A) (n : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K)) n)) (𝟙 K)) ≫
      S.evaluation K N' = S.evaluation K N ≫ n := by
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR] using (S.adjunction K).counit.naturality n

private theorem evaluation_source (K K' N : A) (f : K' ⟶ K) :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 N))) (𝟙 K')) ≫
      S.evaluation K' N =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, N))) f) ≫ S.evaluation K N := by
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR] using S.evaluation_naturality K K' N f

private theorem evaluation_both (K K' N N' : A) (f : K' ⟶ K) (n : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op n)) (𝟙 K')) ≫
      S.evaluation K' N' =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, N))) f) ≫ S.evaluation K N ≫ n := by
  have hf : Prod.mkHom f.op n =
      Prod.mkHom f.op (𝟙 N) ≫ Prod.mkHom (𝟙 (op K')) n := by simp
  rw [hf, H.map_comp]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 N)) ≫ H.map (Prod.mkHom (𝟙 (op K')) n)) (𝟙 K') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 N))) (𝟙 K') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) n)) (𝟙 K') := by simp
  rw [ht, S.tensor.map_comp, Category.assoc, evaluation_target,
    ← Category.assoc, evaluation_source, Category.assoc]

private theorem uncurry_naturality (X K K' N N' : A)
    (t : X ⟶ H.obj (op K, N)) (f : K' ⟶ K) (n : N ⟶ N') :
    (S.transpose X K' N').symm (t ≫ H.map (Prod.mkHom f.op n)) =
      S.tensor.map (Prod.mkHom (𝟙 X) f) ≫ (S.transpose X K N).symm t ≫ n := by
  rw [uncurry_formula, uncurry_formula]
  have ht : Prod.mkHom (t ≫ H.map (Prod.mkHom f.op n)) (𝟙 K') =
      Prod.mkHom t (𝟙 K') ≫ Prod.mkHom (H.map (Prod.mkHom f.op n)) (𝟙 K') := by simp
  rw [ht, S.tensor.map_comp, Category.assoc, evaluation_both]
  have ht' : Prod.mkHom t (𝟙 K') ≫ Prod.mkHom (𝟙 (H.obj (op K, N))) f =
      Prod.mkHom (𝟙 X) f ≫ Prod.mkHom t (𝟙 K) := by simp
  rw [← Category.assoc, ← Category.assoc, ← S.tensor.map_comp, ht', S.tensor.map_comp]
  simp only [Category.assoc]

end ClosedCalculus

private theorem uncurry_composition {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H) (P Q T : D) :
    S.tensor.map (Prod.mkHom (S.composition P Q T) (𝟙 P)) ≫ S.evaluation P T =
      (S.monoidal.associator (H.obj (op Q, T)) (H.obj (op P, Q)) P).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 (H.obj (op Q, T))) (S.evaluation P Q)) ≫
        S.evaluation Q T := by
  rw [← uncurry_formula]
  exact (S.transpose _ _ _).symm_apply_apply _

private theorem tensor_map_comp {D : Type*} [Category* D] (K : D × D ⥤ D)
    {A B C A' B' C' : D} (a : A ⟶ B) (b : B ⟶ C)
    (a' : A' ⟶ B') (b' : B' ⟶ C') :
    K.map (Prod.mkHom a a') ≫ K.map (Prod.mkHom b b') =
      K.map (Prod.mkHom (a ≫ b) (a' ≫ b')) := by
  rw [← K.map_comp]
  rfl

-- The site and coefficient types require extra elaboration of the comparison equations.
private theorem double_evaluation_naturality {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {U V P Q T : D} (a : U ⟶ H.obj (op Q, T)) (b : V ⟶ H.obj (op P, Q)) :
    S.tensor.map (Prod.mkHom (S.tensor.map (Prod.mkHom a b)) (𝟙 P)) ≫
        S.tensor.map (Prod.mkHom (S.composition P Q T) (𝟙 P)) ≫
        S.evaluation P T =
      (S.monoidal.associator U V P).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 U)
          (S.tensor.map (Prod.mkHom b (𝟙 P)) ≫ S.evaluation P Q)) ≫
        (S.tensor.map (Prod.mkHom a (𝟙 Q)) ≫ S.evaluation Q T) := by
  rw [uncurry_composition]
  let _ := S.monoidal
  change ((a ⊗ₘ b) ⊗ₘ 𝟙 P) ≫ (α_ _ _ _).hom ≫
      (𝟙 _ ⊗ₘ S.evaluation P Q) ≫ S.evaluation Q T =
    (α_ U V P).hom ≫ (𝟙 U ⊗ₘ ((b ⊗ₘ 𝟙 P) ≫ S.evaluation P Q)) ≫
      (a ⊗ₘ 𝟙 Q) ≫ S.evaluation Q T
  rw [MonoidalCategory.associator_naturality_assoc]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]

private theorem tensor_first_comp {D : Type*} [Category* D] (K : D × D ⥤ D)
    {A B C : D} (a : A ⟶ B) (b : B ⟶ C) (P : D) :
    K.map (Prod.mkHom (a ≫ b) (𝟙 P)) =
      K.map (Prod.mkHom a (𝟙 P)) ≫ K.map (Prod.mkHom b (𝟙 P)) := by
  rw [tensor_map_comp, Category.id_comp]

private theorem closed_comparison_composition
    {A B : Type*} [Category* A] [Category* B]
    {H : Aᵒᵖ × A ⥤ A} {H' : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (S' : CoefficientClosedStructure H')
    (F : A ⥤ B) (c : F.prod F ⋙ S'.tensor ⟶ S.tensor ⋙ F)
    (ha : ∀ P Q T : A,
      S'.tensor.map (Prod.mkHom (c.app (P, Q)) (𝟙 (F.obj T))) ≫
          c.app (S.tensor.obj (P, Q), T) ≫ F.map (S.monoidal.associator P Q T).hom =
        (S'.monoidal.associator (F.obj P) (F.obj Q) (F.obj T)).hom ≫
          S'.tensor.map (Prod.mkHom (𝟙 (F.obj P)) (c.app (Q, T))) ≫
          c.app (P, S.tensor.obj (Q, T)))
    (β : ∀ P Q : A, F.obj (H.obj (op P, Q)) ⟶ H'.obj (op (F.obj P), F.obj Q))
    (he : ∀ P Q : A,
      S'.tensor.map (Prod.mkHom (β P Q) (𝟙 (F.obj P))) ≫
          S'.evaluation (F.obj P) (F.obj Q) =
        c.app (H.obj (op P, Q), P) ≫ F.map (S.evaluation P Q))
    (P Q T : A) :
    c.app (H.obj (op Q, T), H.obj (op P, Q)) ≫
        F.map (S.composition P Q T) ≫ β P T =
      S'.tensor.map (Prod.mkHom (β Q T) (β P Q)) ≫
        S'.composition (F.obj P) (F.obj Q) (F.obj T) := by
  let U := H.obj (op Q, T)
  let V := H.obj (op P, Q)
  apply (S'.transpose _ _ _).symm.injective
  rw [uncurry_formula, uncurry_formula]
  simp only [tensor_first_comp, Category.assoc]
  rw [he, double_evaluation_naturality, he, he]
  have hn := c.naturality (Prod.mkHom (S.composition P Q T) (𝟙 P))
  change S'.tensor.map (Prod.mkHom (F.map (S.composition P Q T)) (F.map (𝟙 P))) ≫
      c.app (H.obj (op P, T), P) =
    c.app (S.tensor.obj (U, V), P) ≫
      F.map (S.tensor.map (Prod.mkHom (S.composition P Q T) (𝟙 P))) at hn
  rw [F.map_id] at hn
  rw [← Category.assoc _ _ (F.map (S.evaluation P T)), hn,
    Category.assoc, ← F.map_comp, uncurry_composition]
  simp only [F.map_comp]
  have hn' := c.naturality (Prod.mkHom (𝟙 U) (S.evaluation P Q))
  change S'.tensor.map (Prod.mkHom (F.map (𝟙 U)) (F.map (S.evaluation P Q))) ≫
      c.app (U, Q) =
    c.app (U, S.tensor.obj (V, P)) ≫
      F.map (S.tensor.map (Prod.mkHom (𝟙 U) (S.evaluation P Q))) at hn'
  rw [F.map_id] at hn'
  have hα := congrArg (fun z ↦ z ≫
    F.map (S.tensor.map (Prod.mkHom (𝟙 U) (S.evaluation P Q))) ≫
      F.map (S.evaluation Q T)) (ha U V P)
  simp only [Category.assoc] at hα
  rw [hα]
  have hne := congrArg (fun z ↦ z ≫ F.map (S.evaluation Q T)) hn'
  simp only [Category.assoc] at hne
  rw [← hne]
  have ht : S'.tensor.map (Prod.mkHom (𝟙 (F.obj U)) (c.app (V, P))) ≫
      S'.tensor.map (Prod.mkHom (𝟙 (F.obj U)) (F.map (S.evaluation P Q))) =
    S'.tensor.map (Prod.mkHom (𝟙 (F.obj U))
      (c.app (V, P) ≫ F.map (S.evaluation P Q))) := by
    rw [tensor_map_comp, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (fun z ↦
      (S'.monoidal.associator (F.obj U) (F.obj V) (F.obj P)).hom ≫ z ≫
        c.app (U, Q) ≫ F.map (S.evaluation Q T)) ht

private theorem baseChange_evaluation
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    SB.tensor.map
        (Prod.mkHom (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 (F.obj P))) ≫
      SB.evaluation (F.obj P) (F.obj Q) =
    μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q) := by
  rw [← uncurry_formula]
  exact (SB.transpose _ _ _).symm_apply_apply _

private theorem baseChange_composition
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ha : CoefficientTensorAssociativity SA SB F μ) :
    CoefficientInternalHomComposition SA SB F μ := by
  unfold CoefficientInternalHomComposition
  intro P Q V
  apply (cancel_epi (μ.inv.app (HA.obj (op Q, V), HA.obj (op P, Q)))).mp
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
    closed_comparison_composition SA SB F μ.inv ha
      (coefficientBaseChangeHom SA SB F μ) (baseChange_evaluation SA SB F μ) P Q V

private theorem closed_evaluation_of_projection
    {A : Type*} [Category A] {D : Type*} [Category D]
    {H : Aᵒᵖ × A ⥤ A} {I : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    (E : A ⥤ D) (L : D ⥤ A) (adj : L ⊣ E)
    (μ : S.tensor ⋙ E ≅ (E.prod E) ⋙ T.tensor) (M : A)
    (hp : ∀ P : D, IsIso ((adj.homEquiv _ _).symm
      (T.tensor.map (Prod.mkHom (adj.unit.app P) (𝟙 (E.obj M))) ≫
        μ.inv.app (L.obj P, M)))) :
    ∃ γ : Prod.sectR (op M) A ⋙ H ⋙ E ≅
        E ⋙ Prod.sectR (op (E.obj M)) D ⋙ I,
      ∀ N : A,
        T.tensor.map (Prod.mkHom (γ.hom.app N) (𝟙 (E.obj M))) ≫
          T.evaluation (E.obj M) (E.obj N) =
        μ.inv.app (H.obj (op M, N), M) ≫ E.map (S.evaluation M N) := by
  let θ : E ⋙ @MonoidalCategory.tensorRight D _ T.monoidal (E.obj M) ≅
      @MonoidalCategory.tensorRight A _ S.monoidal M ⋙ E :=
    NatIso.ofComponents (fun X ↦ (μ.app (X, M)).symm) (by
      intro X Y f
      simpa [CoefficientClosedStructure.tensor, MonoidalCategory.tensorRight] using
        μ.inv.naturality (Prod.mkHom f (𝟙 M)))
  let p := ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ θ.hom))
  have hcomponent (P : D) : p.app P = (adj.homEquiv _ _).symm
      (T.tensor.map (Prod.mkHom (adj.unit.app P) (𝟙 (E.obj M))) ≫
        μ.inv.app (L.obj P, M)) := by
    simp [p, θ, Adjunction.homEquiv_counit, Functor.map_comp,
      CoefficientClosedStructure.tensor, MonoidalCategory.tensorRight]
  have (P : D) : IsIso (p.app P) := by
    rw [hcomponent]
    exact hp P
  have : IsIso p := NatIso.isIso_of_isIso_app p
  let β := (mateEquiv (S.adjunction M) (T.adjunction (E.obj M))
    (TwoSquare.mk _ _ _ _ θ.hom))
  have hβ : β = conjugateEquiv (adj.comp (S.adjunction M))
      ((T.adjunction (E.obj M)).comp adj) p := by
    have h := iterated_mateEquiv_conjugateEquiv adj adj
      (T.adjunction (E.obj M)) (S.adjunction M)
      ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ θ.hom))
    rw [Equiv.apply_symm_apply] at h
    exact h
  have : IsIso β := by
    rw [hβ]
    infer_instance
  refine ⟨asIso β, ?_⟩
  intro N
  simpa [β, θ, CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensorRight, Prod.sectR] using
    mateEquiv_counit (S.adjunction M) (T.adjunction (E.obj M))
      (TwoSquare.mk _ _ _ _ θ.hom) N

section EvaluationAdjoint
open SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem evaluation_isRightAdjoint (n : ℕ) :
    (e.{c, v, max c v r} J B τ n).IsRightAdjoint := by
  let R := rings.{c, v, max c v r} J B τ
  let E := SheafOfModules.strictSystemSequenceEquivalence R
  have : E.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive R
  have : E.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive R
  let S : SheafOfModules.SystemScalarAssignment.{c, v, max c v r} (J := J) :=
    fun φ ↦ Classical.choice (SheafOfModules.nonempty_systemScalarModel φ)
  let T := SheafOfModules.systemTensorCoherence S
  let d := SheafOfModules.systemSingleDerivedExtension R n S T
  have := evaluationAdditive.{c, v, max c v r} J B τ n
  have := evaluationLimits.{c, v, max c v r} J B τ n
  have := evaluationColimits.{c, v, max c v r} J B τ n
  let η : E.inverse ⋙ SheafOfModules.systemEvaluation R n ≅
      evaluation.{c, v, max c v r} J B τ n :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ = (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  let β := (Functor.mapDerivedCategoryCompIso E.inverse
      (SheafOfModules.systemEvaluation R n)) ≪≫
    Functor.mapDerivedCategoryNatIso η
  exact ((d.adjunction.comp E.mapDerivedCategory.toAdjunction).ofNatIsoRight β).isRightAdjoint

end EvaluationAdjoint

private theorem coefficientEvaluation_rightAdjoint (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).IsRightAdjoint := by
  exact evaluation_isRightAdjoint.{t, t + 1, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W) n

private theorem tensorHomTranspose
    {D₀ D₁ : Type*} [Category* D₀] [Category* D₁]
    (H₁ : D₁ᵒᵖ × D₁ ⥤ D₁) (S₁ : CoefficientClosedStructure H₁)
    (t₀ : D₀ × D₀ ⥤ D₀) (F : D₀ ⥤ D₁)
    (μ : t₀ ⋙ F ≅ (F.prod F) ⋙ S₁.tensor)
    {V W X Y : D₀} {X' Y' : D₁}
    (a : V ⟶ W) (v₀ : t₀.obj (W, X) ⟶ Y)
    (x : F.obj V ⟶ H₁.obj (op X', Y')) (y : F.obj X ≅ X') (z : F.obj Y ⟶ Y')
    (hw : S₁.tensor.map (Prod.mkHom x y.hom) ≫ S₁.evaluation X' Y' =
      μ.inv.app (V, X) ≫ F.map (t₀.map (Prod.mkHom a (𝟙 X)) ≫ v₀) ≫ z) :
    x = F.map a ≫ S₁.transpose _ X' Y'
      (S₁.tensor.map (Prod.mkHom (𝟙 _) y.inv) ≫
        μ.inv.app (W, X) ≫ F.map v₀ ≫ z) := by
  let := S₁.monoidal
  have hmap {P Q : D₁} (f : P ⟶ Q) :
      (MonoidalCategory.tensorRight X').map f =
        S₁.tensor.map (Prod.mkHom f (𝟙 X')) := by
    exact (MonoidalCategory.tensorHom_id f X').symm
  apply ((S₁.adjunction X').homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  simp only [CoefficientClosedStructure.transpose]
  erw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, hmap, hmap]
  change S₁.tensor.map (Prod.mkHom x (𝟙 X')) ≫ S₁.evaluation X' Y' =
    S₁.tensor.map (Prod.mkHom (F.map a) (𝟙 X')) ≫
      (S₁.tensor.map (Prod.mkHom (𝟙 _) y.inv) ≫
        μ.inv.app (W, X) ≫ F.map v₀ ≫ z)
  have : IsIso (Prod.mkHom (𝟙 (F.obj V)) y.hom) :=
    (isIso_prod_iff D₁ D₁).mpr ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (S₁.tensor.map (Prod.mkHom (𝟙 (F.obj V)) y.hom))).mp
  have hc : S₁.tensor.map (Prod.mkHom (𝟙 (F.obj V)) y.hom) ≫
      S₁.tensor.map (Prod.mkHom (F.map a) (𝟙 X')) ≫
      S₁.tensor.map (Prod.mkHom (𝟙 (F.obj W)) y.inv) =
      S₁.tensor.map (Prod.mkHom (F.map a) (𝟙 (F.obj X))) := by
    simp only [← Functor.map_comp, prod_comp, Category.id_comp,
      Category.comp_id, Iso.hom_inv_id]
  calc
    _ = S₁.tensor.map (Prod.mkHom x y.hom) ≫ S₁.evaluation X' Y' := by
      simp only [← Category.assoc, ← Functor.map_comp, prod_comp,
        Category.id_comp, Category.comp_id]
    _ = μ.inv.app (V, X) ≫ F.map (t₀.map (Prod.mkHom a (𝟙 X)) ≫ v₀) ≫ z := hw
    _ = S₁.tensor.map (Prod.mkHom (F.map a) (𝟙 (F.obj X))) ≫
        μ.inv.app (W, X) ≫ F.map v₀ ≫ z := by
      have hn := congrArg (fun k ↦ k ≫ F.map v₀ ≫ z)
        (μ.inv.naturality (Prod.mkHom a (𝟙 X))).symm
      dsimp only [Functor.comp_map, Functor.prod_map, Prod.mkHom] at hn
      simpa only [F.map_id, F.map_comp, Category.assoc] using hn
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ k ≫ μ.inv.app (W, X) ≫ F.map v₀ ≫ z) hc.symm

private theorem transitionAdjoint_naturality
    (R : CoefficientDerivedSystemReduction l E W)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors)
    {m n : ℕ} (h : n ≤ m) {M N : coefficientSequenceDerived l E W} (f : M ⟶ N) :
    (coefficientFiniteQuotientDerived l E W h).map
        ((coefficientSequenceDerivedEvaluation l E W m).map f) ≫
      coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h N =
    coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h M ≫
      (coefficientSequenceDerivedEvaluation l E W n).map f := by
  apply ((Q.adjunction h).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [coefficientSequenceTransitionAdjoint, Equiv.apply_symm_apply]
  exact (coefficientSequenceDerivedTransition l E W h).naturality f

private theorem baseChange_source_target
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (P Q : A) (P' Q' : B) (f : P' ⟶ F.obj P) (g : F.obj Q ⟶ Q') :
    SB.transpose _ P' Q'
        (SB.tensor.map (Prod.mkHom (𝟙 _) f) ≫
          μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q) ≫ g) =
      coefficientBaseChangeHom SA SB F μ P Q ≫ HB.map (Prod.mkHom f.op g) := by
  apply (SB.transpose _ _ _).symm.injective
  rw [Equiv.symm_apply_apply, uncurry_naturality]
  change _ = SB.tensor.map _ ≫ (SB.transpose _ _ _).symm (SB.transpose _ _ _ _) ≫ _
  rw [Equiv.symm_apply_apply]
  simp only [Category.assoc]

private theorem fiber_transition_of_evaluation
    (R : CoefficientDerivedSystemReduction l E W)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors)
    (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) {m n : ℕ} (h : n ≤ m)
    (γm : (coefficientSequenceDerivedEvaluation l E W m).obj
        ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≅
      (coefficientFiniteInternalHom l E W m).obj
        (op ((coefficientSequenceDerivedEvaluation l E W m).obj M),
          (coefficientSequenceDerivedEvaluation l E W m).obj N))
    (γn : (coefficientSequenceDerivedEvaluation l E W n).obj
        ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≅
      (coefficientFiniteInternalHom l E W n).obj
        (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
          (coefficientSequenceDerivedEvaluation l E W n).obj N))
    (hem : (R.finiteClosed m).tensor.map (Prod.mkHom γm.hom (𝟙 _)) ≫
        (R.finiteClosed m).evaluation
          ((coefficientSequenceDerivedEvaluation l E W m).obj M)
          ((coefficientSequenceDerivedEvaluation l E W m).obj N) =
      (R.evaluationTensor m).inv.app
          ((coefficientSequenceInternalHom l E W).obj (op M, N), M) ≫
        (coefficientSequenceDerivedEvaluation l E W m).map (R.systemClosed.evaluation M N))
    (hen : (R.finiteClosed n).tensor.map (Prod.mkHom γn.hom (𝟙 _)) ≫
        (R.finiteClosed n).evaluation
          ((coefficientSequenceDerivedEvaluation l E W n).obj M)
          ((coefficientSequenceDerivedEvaluation l E W n).obj N) =
      (R.evaluationTensor n).inv.app
          ((coefficientSequenceInternalHom l E W).obj (op M, N), M) ≫
        (coefficientSequenceDerivedEvaluation l E W n).map (R.systemClosed.evaluation M N)) :
    coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
        ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≫ γn.hom =
      (coefficientFiniteQuotientDerived l E W h).map γm.hom ≫
        coefficientFiniteQuotientHomComparison l E W R.toCoefficientDerivedSystemTensors Q h
          ((coefficientSequenceDerivedEvaluation l E W m).obj M)
          ((coefficientSequenceDerivedEvaluation l E W m).obj N) ≫
        (coefficientFiniteInternalHom l E W n).map
          (Prod.mkHom
            (coefficientSequenceNormalizationIso l E W
              R.toCoefficientDerivedSystemTensors Q h M hM).inv.op
            (coefficientSequenceNormalizationIso l E W
              R.toCoefficientDerivedSystemTensors Q h N hN).hom) := by
  let H := (coefficientSequenceInternalHom l E W).obj (op M, N)
  let Em := coefficientSequenceDerivedEvaluation l E W m
  let En := coefficientSequenceDerivedEvaluation l E W n
  let F := coefficientFiniteQuotientDerived l E W h
  let red (P : coefficientSequenceDerived l E W) :=
    coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h P
  let a := γm.hom
  let b := γn.hom
  let μ := Q.tensor h
  let δm := (R.evaluationTensor m).app (H, M)
  let δn := (R.evaluationTensor n).app (H, M)
  let d := coefficientSequenceNormalizationIso l E W R.toCoefficientDerivedSystemTensors Q h M hM
  change (R.finiteClosed m).tensor.map (Prod.mkHom a (𝟙 (Em.obj M))) ≫
    (R.finiteClosed m).evaluation (Em.obj M) (Em.obj N) =
      δm.inv ≫ Em.map (R.systemClosed.evaluation M N) at hem
  change (R.finiteClosed n).tensor.map (Prod.mkHom b (𝟙 (En.obj M))) ≫
    (R.finiteClosed n).evaluation (En.obj M) (En.obj N) =
      δn.inv ≫ En.map (R.systemClosed.evaluation M N) at hen
  have hr : (R.finiteClosed n).tensor.map (Prod.mkHom (red H) (red M)) ≫ δn.inv =
      μ.inv.app (Em.obj H, Em.obj M) ≫ F.map δm.inv ≫ red (R.systemClosed.tensor.obj (H, M)) := by
    have ht := coefficientNormalizedTensorHorizontal l E W R hE Q H M h
    change F.map δm.hom ≫ μ.hom.app (Em.obj H, Em.obj M) ≫
      (R.finiteClosed n).tensor.map (Prod.mkHom (red H) (red M)) =
      red (R.systemClosed.tensor.obj (H, M)) ≫ δn.hom at ht
    have ht' := congrArg
      (fun f ↦ μ.inv.app (Em.obj H, Em.obj M) ≫ F.map δm.inv ≫ f ≫ δn.inv) ht
    simpa only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      F.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id, Category.comp_id] using ht'
  have hw : (R.finiteClosed n).tensor.map (Prod.mkHom (red H ≫ b) d.hom) ≫
      (R.finiteClosed n).evaluation (En.obj M) (En.obj N) =
      μ.inv.app (Em.obj H, Em.obj M) ≫
        F.map ((R.finiteClosed m).tensor.map (Prod.mkHom a (𝟙 (Em.obj M))) ≫
          (R.finiteClosed m).evaluation (Em.obj M) (Em.obj N)) ≫ red N := by
    calc
      _ = (R.finiteClosed n).tensor.map (Prod.mkHom (red H) (red M)) ≫
          ((R.finiteClosed n).tensor.map (Prod.mkHom b (𝟙 (En.obj M))) ≫
            (R.finiteClosed n).evaluation (En.obj M) (En.obj N)) := by
        have hp : Prod.mkHom (red H ≫ b) (red M) =
            Prod.mkHom (red H) (red M) ≫ Prod.mkHom b (𝟙 (En.obj M)) :=
          Prod.ext rfl (Category.comp_id (red M)).symm
        change (R.finiteClosed n).tensor.map (Prod.mkHom (red H ≫ b) (red M)) ≫ _ = _
        rw [hp, Functor.map_comp, Category.assoc]
      _ = (R.finiteClosed n).tensor.map (Prod.mkHom (red H) (red M)) ≫
          δn.inv ≫ En.map (R.systemClosed.evaluation M N) := by
        rw [hen]
      _ = μ.inv.app (Em.obj H, Em.obj M) ≫ F.map δm.inv ≫
          red (R.systemClosed.tensor.obj (H, M)) ≫ En.map (R.systemClosed.evaluation M N) := by
        rw [← Category.assoc, hr, Category.assoc, Category.assoc]
      _ = μ.inv.app (Em.obj H, Em.obj M) ≫ F.map δm.inv ≫
          F.map (Em.map (R.systemClosed.evaluation M N)) ≫ red N := by
        rw [transitionAdjoint_naturality l E W R Q h (R.systemClosed.evaluation M N)]
      _ = μ.inv.app (Em.obj H, Em.obj M) ≫
          F.map (δm.inv ≫ Em.map (R.systemClosed.evaluation M N)) ≫ red N := by
        rw [F.map_comp, Category.assoc]
      _ = _ := by rw [← hem]
  have hh := tensorHomTranspose _ (R.finiteClosed n) (R.finiteClosed m).tensor F μ
    a ((R.finiteClosed m).evaluation (Em.obj M) (Em.obj N))
    (red H ≫ b) d (red N) hw
  rw [baseChange_source_target] at hh
  exact hh

/-- Normalized reduction and quotient models give the local internal-Hom calculus.
Source: Stacks, sites-cohomology.tex, Tags 07A4, 08J9, 0A95 and 0941;
resolution-model construction, step 3
(blueprint: lem-coef-normalized-internal-hom-fibers).

Proof:
The tensor associativity lemma and the two closed adjunctions imply preservation of
internal composition: uncurry both sides and use associativity and naturality of
evaluation. Construct a left adjoint to actual finite evaluation from the derived
singleton extension, transported across the strict-system equivalence. The tensor
projection lemma makes the mate of the evaluated closed adjunction invertible.
This gives a natural fiber isomorphism with exactly the displayed evaluation equation.
Finally uncurry the desired horizontal transition equation. Naturality of the actual
transition, the tensor horizontal lemma and the fiber evaluation equations identify
its two sides. Transpose back and cancel the normalized source transition. Thus no
comparison with a separately chosen internal-Hom model, global sections or total
inverse limit is needed. The three remaining model arguments are separate tensor
lemmas; all closed-category and adjunction calculations here are proved. -/
theorem coefficientNormalizedInternalHomFibers
    (R : CoefficientDerivedSystemReduction l E W)
    (hT : CoefficientDerivedSystemTensorCoherence l E W R.toCoefficientDerivedSystemTensors)
    (hR : CoefficientReductionTensorNormalization l E W R)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) :
    Nonempty (CoefficientNormalizedInternalHomFibers l E W R Q) := by
  classical
  obtain ⟨ha, hf⟩ := coefficientNormalizedTensorAssociativity l E W R hT hR hF
  have h (M : coefficientSequenceDerived l E W)
      (hM : IsNormalizedCoefficientSequence l E W M) (n : ℕ) := by
    have := coefficientEvaluation_rightAdjoint l E W n
    let Eₙ := coefficientSequenceDerivedEvaluation l E W n
    exact closed_evaluation_of_projection R.systemClosed (R.finiteClosed n)
      Eₙ Eₙ.leftAdjoint (Adjunction.ofIsRightAdjoint Eₙ) (R.evaluationTensor n) M
      (coefficientNormalizedEvaluationProjection l E W R hE M hM n
        Eₙ.leftAdjoint (Adjunction.ofIsRightAdjoint Eₙ))
  choose γ hγ using h
  refine ⟨{
    reduction_composition := baseChange_composition R.integralClosed R.systemClosed
      R.reduction R.reductionTensor ha
    finite_composition := fun n ↦ baseChange_composition R.integralClosed (R.finiteClosed n)
      (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n) (hf n)
    fiberHom := fun M N hM _ n ↦ (γ M hM n).app N
    fiber_evaluation := fun M N hM _ n ↦ (hγ M hM n N).symm
    fiber_transition := ?_ }⟩
  intro M N hM hN m n hmn
  exact fiber_transition_of_evaluation l E W R hE Q M N hM hN hmn
    ((γ M hM m).app N) ((γ M hM n).app N)
    (hγ M hM m N) (hγ M hM n N)

end WeilConjectures
