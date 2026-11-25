/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionPresentation
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitLocality
import WeilConjectures.SixFunctors.Constructible.ConstructibleProjectiveChartRefinement
import WeilConjectures.SixFunctors.Supporting.Tensor.ProjectiveTensorChartComplete

/-! # Completeness of ordinary tensor on constructible inputs

Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50
(blueprint: lem-fix-constructible-tensor-completion-constructible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleTensorModel
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective
attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLocalizationIsMonoidal
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
attribute [local instance 3100] integralTowerHasDerivedCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local irreducible] IntegralOnSlice.duality IntegralOnSlice.roosUnit
  IntegralAmbient.tensorTowerIso IntegralAmbient.tensorOperationUnit

omit [Fact l.Prime] in
private theorem tensorPrime_globalUnit
    [∀ w : W, Invertible (l : W.residueField w)] : IsUnit (l : Γ(W, ⊤)) := by
  apply W.toRingedSpace.isUnit_of_isUnit_germ ⊤ (l : Γ(W, ⊤))
  intro w _
  simpa only [map_natCast] using tensorPrime_stalkUnit l W w

private theorem tensorUnit_onConstructible
    [CompactSpace W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : sfIntegralConstructible l E W M) (hN : sfIntegralConstructible l E W N) :
    IsIso ((tensorCompletionUnit l E W).app
      ((ordinaryTensor l E W).obj (M, N))) := by
  classical
  have hl := tensorPrime_globalUnit l W
  obtain ⟨d, T, toW, root, parent, left, right, leftEdge, rightEdge, leaf,
    hroot, hparent, hlt, hcompact, hqs, himm, hchild, hleaf, hsplit, hlocal⟩ :=
    constructible_projective_chart_refinement l E W hl M N hM hN
      0 (fun a ↦ Fin.elim0 a) (fun a ↦ Fin.elim0 a) (fun a ↦ Fin.elim0 a)
      (fun a ↦ Fin.elim0 a) (fun a ↦ Fin.elim0 a) (fun a ↦ Fin.elim0 a)
      (fun a ↦ Fin.elim0 a) (fun a ↦ Fin.elim0 a)
  let H := (ordinaryTensor l E W).obj (M, N)
  have charts (v : Fin d) :
      ∃ (c : ℕ) (A : Fin c → (T v).ProEt),
        (∀ i, CompactSpace (A i).left) ∧ (∀ i, QuasiSeparatedSpace (A i).left) ∧
        (leaf v → Nonempty (T v) →
          Presieve.ofArrows A (fun i ↦
            (MorphismProperty.Over.homMk (A i).hom (Category.comp_id _) :
              A i ⟶ AlgebraicGeometry.Scheme.ProEt.mk (𝟙 (T v)))) ∈
            AlgebraicGeometry.Scheme.ProEt.precoverage (T v)
              (AlgebraicGeometry.Scheme.ProEt.mk (𝟙 (T v)))) ∧
        (leaf v → Nonempty (T v) → ∀ i,
          IntegralOnSlice.IsComplete l E (A i).left none
            ((IntegralOnSlice.ordinaryDerivedPull.{u, u} l E ((A i).hom ≫ toW v)).obj H)) := by
    by_cases hv : leaf v ∧ Nonempty (T v)
    · let := hcompact v
      let := hqs v
      obtain ⟨_, _, V, _, _, _, c, U, _, _, hqc, hquasi, hcover, hmodel⟩ :=
        hlocal v hv.1 hv.2
      let A : Fin c → (T v).ProEt := fun i ↦
        AlgebraicGeometry.Scheme.ProEt.mk ((U i).ι ≫ V.hom)
      have hAqc (i) : CompactSpace (A i).left := hqc i
      have hAqs (i) : QuasiSeparatedSpace (A i).left := hquasi i
      refine ⟨c, A, hAqc, hAqs, ?_, ?_⟩
      · intro _ _
        let C : (T v).Cover (AlgebraicGeometry.Scheme.precoverage @AlgebraicGeometry.WeaklyEtale) :=
          { I₀ := Fin c
            X := fun i ↦ (A i).left
            f := fun i ↦ (A i).hom
            mem₀ := (AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff _).mpr
              ⟨hcover, fun i ↦ inferInstance⟩ }
        have (i : C.I₀) : AlgebraicGeometry.QuasiCompact (C.f i) := by
          let := hAqc i
          exact AlgebraicGeometry.quasiCompact_of_compactSpace _
        have : Scheme.JointlySurjective (Scheme.precoverage @WeaklyEtale) :=
          Scheme.instJointlySurjectivePrecoverage
        have : AlgebraicGeometry.QuasiCompactCover C.toPreZeroHypercover :=
          AlgebraicGeometry.QuasiCompactCover.of_finite
        with_unfolding_all
          erw [AlgebraicGeometry.Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
        exact C.ofQuasiCompactCover.mem₀
      · intro _ _ i
        with_unfolding_all
          change IntegralOnSlice.IsComplete l E (U i).toScheme none
            ((IntegralOnSlice.ordinaryDerivedPull.{u, u} l E
              (((U i).ι ≫ V.hom) ≫ toW v)).obj H)
        let := hqc i
        let := hquasi i
        obtain ⟨P, a, b, _, ha, hb, hp, ep⟩ := hmodel i M (.inl rfl)
        obtain ⟨Q, c', d', _, hc, hd, hq, eq⟩ := hmodel i N (.inr rfl)
        let := ha
        let := hb
        let := hc
        let := hd
        have hlT : IsUnit (l : Γ((U i).toScheme, ⊤)) := by
          simpa only [map_natCast] using hl.map
            ((((U i).ι ≫ V.hom) ≫ toW v).appTop.hom)
        dsimp only [H, ordinaryTensor]
        with_unfolding_all
          refine projectiveTensorChartComplete l E (((U i).ι ≫ V.hom) ≫ toW v)
            (fun x ↦ ?_) M N P Q ?_ ?_ hp hq
            (by simpa only [Category.assoc] using ep)
            (by simpa only [Category.assoc] using eq)
        · simpa only [map_natCast] using hlT.map ((U i).toScheme.Γevaluation x).hom
        · refine ⟨a, b, fun k hk ↦ ?_⟩
          rcases hk with hk | hk
          · exact P.isZero_of_isStrictlyGE a k hk
          · exact P.isZero_of_isStrictlyLE b k hk
        · refine ⟨c', d', fun k hk ↦ ?_⟩
          rcases hk with hk | hk
          · exact Q.isZero_of_isStrictlyGE c' k hk
          · exact Q.isZero_of_isStrictlyLE d' k hk
    · refine ⟨0, Fin.elim0, (fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i), ?_, ?_⟩
      · intro hv' hn
        exact (hv ⟨hv', hn⟩).elim
      · intro hv' hn
        exact (hv ⟨hv', hn⟩).elim
  choose c A hqc hquasi hcover hcomplete using charts
  have hloc := (IntegralOnSlice.qcqsCompletionUnitLocality.{u, u, 0} l E W hl).2.2
    d T toW root parent left right leftEdge rightEdge leaf
    hroot hparent hlt hcompact hqs himm hchild hleaf hsplit
    (fun v ↦ Fin (c v)) A (fun v i _ _ ↦ hqc v i)
    (fun v i _ _ ↦ hquasi v i) hcover H
  unfold tensorCompletionUnit tensorCompletionFunctor
  with_unfolding_all
    exact ((IntegralOnSlice.qcqsCompletionUnitLocality.{u, u, 0} l E W hl).1 H).2
      (hloc.2.mpr hcomplete)

/-- The ordinary derived tensor of constructible inputs is complete, with invertible
canonical completion unit.
Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50; Lemma 6.5.8
(blueprint: lem-fix-constructible-tensor-completion-constructible).

Proof: simultaneous projective chart refinement gives a finite open--closed tree and
common finite covers of its nonempty leaves. On each chart the two inputs have
bounded finite-projective models, so projectiveTensorChartComplete proves local
completeness. The canonical finite-tree locality criterion gives invertibility of
the global completion unit and identifies it with derived completeness. Empty leaves
have empty chart families, and the locality criterion includes an empty root. -/
theorem tensorComplete_onConstructible
    [CompactSpace W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : sfIntegralConstructible l E W M) (hN : sfIntegralConstructible l E W N) :
    IsDerivedCompleteUnrestricted l E W ((ordinaryTensor l E W).obj (M, N)) ∧
      IsIso ((tensorCompletionUnit l E W).app ((ordinaryTensor l E W).obj (M, N))) := by
  have hu := tensorUnit_onConstructible l E W M N hM hN
  refine ⟨?_, hu⟩
  have hl := tensorPrime_globalUnit l W
  unfold tensorCompletionUnit tensorCompletionFunctor at hu
  with_unfolding_all
    exact ((IntegralOnSlice.qcqsCompletionUnitLocality.{u, u, 0} l E W hl).1 _).1 hu

end WeilConjectures.ConstructibleTensorModel
