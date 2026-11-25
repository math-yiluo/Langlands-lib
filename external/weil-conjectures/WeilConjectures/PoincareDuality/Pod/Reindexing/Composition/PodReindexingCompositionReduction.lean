/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import Mathlib.Tactic.CategoryTheory.Slice

/-! # Reduction composition from total-limit composition

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5.
The proof uses injectivity of the adjunction Hom equivalence and the Unit law. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section CompositionMates

set_option backward.defeqAttrib.useBackward true

variable {C₀ : Type*} {C₁ : Type*} {C₂ : Type*}
  {D₀ : Type*} {D₁ : Type*} {D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}
  {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
  {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}

private theorem unit_inverse
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁)
    {F : C₀ ⥤ C₁} {S : D₀ ⥤ D₁}
    (α : L₀ ⋙ S ≅ F ⋙ L₁) (β : R₀ ⋙ F ≅ S ⋙ R₁)
    (hu : ∀ K, F.map (a₀.unit.app K) ≫ β.hom.app (L₀.obj K) ≫
      R₁.map (α.hom.app K) = a₁.unit.app (F.obj K)) (K : C₀) :
    a₁.unit.app (F.obj K) ≫ R₁.map (α.inv.app K) =
      F.map (a₀.unit.app K) ≫ β.hom.app (L₀.obj K) := by
  erw [← hu K]
  erw [Category.assoc, Category.assoc, ← R₁.map_comp, α.hom_inv_id_app]
  erw [R₁.map_id ((L₀ ⋙ S).obj K)]
  exact congrArg (fun z ↦ F.map (a₀.unit.app K) ≫ z)
    (Category.comp_id (β.hom.app (L₀.obj K)))

private theorem composition_mates
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {H : C₀ ⥤ C₂}
    {S : D₀ ⥤ D₁} {T : D₁ ⥤ D₂} {U : D₀ ⥤ D₂}
    (αF : L₀ ⋙ S ≅ F ⋙ L₁) (βF : R₀ ⋙ F ≅ S ⋙ R₁)
    (αG : L₁ ⋙ T ≅ G ⋙ L₂) (βG : R₁ ⋙ G ≅ T ⋙ R₂)
    (αH : L₀ ⋙ U ≅ H ⋙ L₂) (βH : R₀ ⋙ H ≅ U ⋙ R₂)
    (κ : H ≅ F ⋙ G) (σ : U ≅ S ⋙ T)
    (uF : ∀ K, F.map (a₀.unit.app K) ≫ βF.hom.app (L₀.obj K) ≫
      R₁.map (αF.hom.app K) = a₁.unit.app (F.obj K))
    (uG : ∀ K, G.map (a₁.unit.app K) ≫ βG.hom.app (L₁.obj K) ≫
      R₂.map (αG.hom.app K) = a₂.unit.app (G.obj K))
    (uH : ∀ K, H.map (a₀.unit.app K) ≫ βH.hom.app (L₀.obj K) ≫
      R₂.map (αH.hom.app K) = a₂.unit.app (H.obj K))
    (hc : ∀ N, κ.hom.app (R₀.obj N) ≫ G.map (βF.hom.app N) ≫
      βG.hom.app (S.obj N) = βH.hom.app N ≫ R₂.map (σ.hom.app N)) (K : C₀) :
    σ.hom.app (L₀.obj K) ≫ T.map (αF.hom.app K) ≫ αG.hom.app (F.obj K) =
      αH.hom.app K ≫ L₂.map (κ.hom.app K) := by
  let i := σ.app (L₀.obj K) ≪≫ T.mapIso (αF.app K) ≪≫ αG.app (F.obj K)
  let j := αH.app K ≪≫ L₂.mapIso (κ.app K)
  have hi : i.inv = j.inv := by
    apply (a₂.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, i, j, Iso.trans_inv, Functor.mapIso_inv,
      Iso.app_inv, Category.assoc]
    change a₂.unit.app (G.obj (F.obj K)) ≫
      R₂.map (αG.inv.app (F.obj K) ≫ T.map (αF.inv.app K) ≫ σ.inv.app (L₀.obj K)) =
      a₂.unit.app (G.obj (F.obj K)) ≫
        R₂.map (L₂.map (κ.inv.app K) ≫ αH.inv.app K)
    simp only [Functor.map_comp]
    erw [← Category.assoc, ← Category.assoc, unit_inverse a₁ a₂ αG βG uG]
    have hnat := βG.hom.naturality (αF.inv.app K)
    simp only [Functor.comp_map, Functor.comp_obj] at hnat
    slice_lhs 2 3 => erw [← hnat]
    slice_lhs 1 2 =>
      erw [← G.map_comp, unit_inverse a₀ a₁ αF βF uF, G.map_comp]
    have hc' := congrArg
      (fun z ↦ κ.inv.app (R₀.obj (L₀.obj K)) ≫ z ≫ R₂.map (σ.inv.app (L₀.obj K)))
      (hc (L₀.obj K))
    simp only [← Category.assoc, κ.inv_hom_id_app, Category.id_comp] at hc'
    simp only [Category.assoc, ← R₂.map_comp, σ.hom_inv_id_app, R₂.map_id] at hc'
    erw [Category.comp_id] at hc'
    slice_lhs 2 4 => erw [hc']
    erw [← Category.assoc, κ.inv.naturality, Category.assoc,
      ← unit_inverse a₀ a₂ αH βH uH]
    erw [← a₂.unit_naturality_assoc]
    rfl
  have hij : i.symm = j.symm := Iso.ext hi
  exact congrArg Iso.inv hij

end CompositionMates

/-- Composition for reduction follows from composition for total limit.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 0941 (blueprint: lem-pod-reindexing-composition-reduction-equation).

Proof: invert each reduction isomorphism. Unit compatibility identifies its
adjunction transpose with ordinary reindexing of the source unit followed by
the limit comparison. Transpose the inverse composite reduction map at Z.
Naturality of the h-limit map moves the f-reduction inverse across it. The
f-unit equation combines the two source-unit factors. Substitute hlimit and
cancel the system compositor with its inverse. Naturality of the ordinary
compositor moves the remaining unit past that compositor. The composite-unit
equation and naturality of the Z-unit identify the result with the transpose
of the other inverse reduction map. The adjunction Hom equivalence is injective,
so the inverse reduction maps are equal. Inverting gives the desired equation.
This is formal for arbitrary ambient objects; it uses no evaluation faithfulness,
constructibility, tensor law, or additional normalization assumption. -/
theorem podReindexingCompositionReduction
    (A : PodReindexFamily l E)
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (A.completion f))
    (hlimit :
    ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      [∀ z : Z, Invertible (l : Z.residueField z)],
      ∀ N : coefficientSequenceDerived l E V,
        (A.compositionDerived l E h f).hom.app ((coefficientSequenceLimit l E V).obj N) ≫
          (podOrdinaryReindex l E h).map ((A.completion f).limit.hom.app N) ≫
          (A.completion h).limit.hom.app ((integralComparisonDerivedSequencePullback l E f).obj N) =
        (A.completion (h ≫ f)).limit.hom.app N ≫
          (coefficientSequenceLimit l E Z).map
            ((integralComparisonSystemComposition l E h f).hom.app N)) :
    ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      [∀ z : Z, Invertible (l : Z.residueField z)],
      ∀ K : DerivedCategory (scalarReductionSource l E V),
        (integralComparisonSystemComposition l E h f).hom.app
            ((podReindexCalculus l E V).reduction.obj K) ≫
          (integralComparisonDerivedSequencePullback l E h).map
            ((A.completion f).reduction.hom.app K) ≫
          (A.completion h).reduction.hom.app ((podOrdinaryReindex l E f).obj K) =
        (A.completion (h ≫ f)).reduction.hom.app K ≫
          (podReindexCalculus l E Z).reduction.map
            ((A.compositionDerived l E h f).hom.app K) := by
  intro V W Z h f _ _ _ _ _ K
  exact composition_mates
    (podReindexCalculus l E V).adjunction
    (podReindexCalculus l E W).adjunction
    (podReindexCalculus l E Z).adjunction
    (A.completion f).reduction (A.completion f).limit
    (A.completion h).reduction (A.completion h).limit
    (A.completion (h ≫ f)).reduction (A.completion (h ≫ f)).limit
    (A.compositionDerived l E h f) (integralComparisonSystemComposition l E h f)
    (hcompletion f).2.2.2.1 (hcompletion h).2.2.2.1
    (hcompletion (h ≫ f)).2.2.2.1 (hlimit h f) K

end WeilConjectures
