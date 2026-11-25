/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionComparison
public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModel
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackComparison
public import WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorRepresentatives
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

set_option linter.privateModule false

/-! # Completion-unit realization of the strict open tensor map

Source: Stacks Project, sites-cohomology.tex Tag 0GL1 and sites-modules.tex Tag 0E8I;
strict-system and completion-unit refinement, node proof steps 4--9
(blueprint: lem-pur-completed-open-tensor-system-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOpenTensor
open IntegralOpenReduction

private theorem transition_bijective_of_iso
    {C A B : Type*} [Category* C] [Category* A] [Category* B]
    (F : C ⥤ A) (G : C ⥤ B) (T : B ⥤ A) (τ : F ⟶ G ⋙ T)
    {X Y : C} (e : X ≅ Y)
    (hX : ∀ P : B, Function.Bijective (fun f : G.obj X ⟶ P ↦ τ.app X ≫ T.map f))
    (P : B) : Function.Bijective (fun f : G.obj Y ⟶ P ↦ τ.app Y ≫ T.map f) := by
  let fn := Iso.homCongr (G.mapIso e) (Iso.refl P)
  let fm := Iso.homCongr (F.mapIso e) (Iso.refl (T.obj P))
  have heq : (fun f : G.obj Y ⟶ P ↦ τ.app Y ≫ T.map f) =
      fm ∘ (fun f ↦ τ.app X ≫ T.map f) ∘ fn.symm := by
    funext f
    simp only [Function.comp_apply, fm, fn, Iso.homCongr_symm, Iso.homCongr_apply,
      Iso.refl_symm, Iso.symm_inv, Iso.refl_hom, Category.comp_id,
      Functor.mapIso_hom, Functor.mapIso_inv]
    rw [T.map_comp]
    have hn : F.map e.inv ≫ τ.app X = τ.app Y ≫ T.map (G.map e.inv) :=
      τ.naturality e.inv
    rw [reassoc_of% hn, ← T.map_comp_assoc, ← G.map_comp, e.inv_hom_id,
      G.map_id, T.map_id, Category.id_comp]
  rw [heq]
  exact fm.bijective.comp ((hX P).comp fn.symm.bijective)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U V : Scheme.{t}} (j : U ⟶ V) [IsOpenImmersion j]
  (C : Context l E j)
  (K : DerivedCategory (scalarReductionSource l E U))
  (N : DerivedCategory (scalarReductionSource l E V))

private theorem complete_of_iso (W : Scheme.{t})
    {A B : DerivedCategory (scalarReductionSource l E W)} (e : A ≅ B)
    (hA : complete l E W A) : complete l E W B := by
  obtain ⟨D, hlD, P, G, q, hq, a, hprod, δ, hδ⟩ := hA
  let := hprod
  refine ⟨D, hlD, P, G, q, hq, a ≪≫ e, hprod,
    δ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ _
  refine Pretriangulated.Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · apply Pi.hom_ext
    intro n
    simp [Category.assoc]
  · simp
  · simp [Category.assoc, ← Functor.map_comp]

private theorem normalized_of_iso (W : Scheme.{t})
    {A B : coefficientSequenceDerived l E W} (e : A ≅ B)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsNormalizedCoefficientSequence l E W B := by
  intro m n h P
  exact transition_bijective_of_iso (coefficientSequenceDerivedEvaluation l E W m)
    (coefficientSequenceDerivedEvaluation l E W n) (normalizedDVRRes l E W h)
    (coefficientSequenceDerivedTransition l E W h) e (hA h) P

end WeilConjectures.CompletedOpenTensor
