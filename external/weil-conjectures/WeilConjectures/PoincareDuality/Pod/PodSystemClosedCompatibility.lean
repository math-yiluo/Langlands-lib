/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import all WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

/-! # Internal Hom compatibility for strict-system reindexing

The proof is the system-level calculation from the automorphism Hom comparison,
separated after profiling to keep each file within the single-file time limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  pullbackTensorCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- The evaluation-defined internal Hom comparison for strict derived coefficient
systems is invertible and preserves evaluation, transposition and composition.
Source: blueprint proper-duality compatibility proof, Step 5; Stacks 0941 and 0GMX.
Proof: identify ordinary reindexing with integral comparison pullback using the
coefficient ring-map equation. The derived identity and composition comparisons
exhibit pullback by the inverse scheme isomorphism as a quasi-inverse. Closed
transposition and full faithfulness identify postcomposition by the Hom comparison
with a bijection on all image test objects. Essential surjectivity then gives a
bijection on every test object, and Yoneda proves invertibility. The prescribed
tensorator associativity and unit equations construct a core monoidal structure.
Its tensor isomorphisms are exactly the prescribed comparisons, so the general
closed-monoidal evaluation calculation supplies all remaining compatibility laws.
(blueprint: lem-pod-system-closed-compatibility). -/
theorem podSystemClosedCompatibility :
    (∀ M N, IsIso (coefficientBaseChangeHom
      (pullbackTensorCalculus l E Y).systemClosed (pullbackTensorCalculus l E X).systemClosed
      (pullbackTensorSequenceDerived l E g) (pullbackTensorSystemComparison l E g) M N)) ∧
    CoefficientEvaluationCompatible (pullbackTensorCalculus l E Y).systemClosed
      (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
        (pullbackTensorSystemComparison l E g) := by
  let SA := (pullbackTensorCalculus l E Y).systemClosed
  let SB := (pullbackTensorCalculus l E X).systemClosed
  let F := pullbackTensorSequenceDerived l E g
  let μ := pullbackTensorSystemComparison l E g
  change (∀ M N, IsIso (coefficientBaseChangeHom SA SB F μ M N)) ∧
    CoefficientEvaluationCompatible SA SB F μ
  have hF : F ≅ integralComparisonDerivedSequencePullback l E g := by
    have heq : pullbackTensorSequenceInverse l E g =
        integralComparisonSequencePullback l E g := by
      unfold pullbackTensorSequenceInverse integralComparisonSequencePullback
      congr 1
      unfold pullbackTensorSequenceDirect integralComparisonSequenceDirectImage
      rw [pullbackTensorSequenceRing_eq]
    exact Functor.mapDerivedCategoryNatIso (eqToIso heq)
  have hH : (integralComparisonDerivedSequencePullback l E g).IsEquivalence := by
    let H := integralComparisonDerivedSequencePullback l E g
    let G := integralComparisonDerivedSequencePullback l E (inv g)
    let a : H ⋙ G ≅ 𝟭 _ :=
      (integralComparisonSystemComposition l E (inv g) g).symm ≪≫
        eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
          (IsIso.inv_hom_id g)) ≪≫ integralComparisonSystemUnit l E Y
    let b : G ⋙ H ≅ 𝟭 _ :=
      (integralComparisonSystemComposition l E g (inv g)).symm ≪≫
        eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
          (IsIso.hom_inv_id g)) ≪≫ integralComparisonSystemUnit l E X
    exact (CategoryTheory.Equivalence.mk H G a.symm b).isEquivalence_functor
  have : F.IsEquivalence := Functor.isEquivalence_of_iso hF.symm
  refine ⟨?_, ?_⟩
  · intro M N
    have hL (L : coefficientSequenceDerived l E Y) : Function.Bijective
        (fun x : F.obj L ⟶ F.obj ((coefficientSequenceInternalHom l E Y).obj (op M, N)) ↦
          x ≫ coefficientBaseChangeHom SA SB F μ M N) := by
      let e := (SA.transpose L M N).symm.trans
        ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
          ((Iso.homCongr (μ.app (L, M)) (Iso.refl (F.obj N))).trans
            (SB.transpose _ _ _)))
      have he (x : L ⟶ (coefficientSequenceInternalHom l E Y).obj (op M, N)) :
          e x = F.map x ≫ coefficientBaseChangeHom SA SB F μ M N := by
        dsimp only [e, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk,
          Functor.FullyFaithful.homEquiv, Iso.refl_hom]
        rw [Category.comp_id]
        change SB.transpose _ _ _ (μ.inv.app (L, M) ≫
          F.map ((SA.transpose L M N).symm x)) = _
        simpa only [Equiv.apply_symm_apply] using
          (finiteChange_transpose SA SB F μ L M N ((SA.transpose L M N).symm x)).symm
      have hbij : Function.Bijective
          (fun x : L ⟶ (coefficientSequenceInternalHom l E Y).obj (op M, N) ↦
            F.map x ≫ coefficientBaseChangeHom SA SB F μ M N) := by
        simpa only [← he] using e.bijective
      constructor
      · intro x y hxy
        obtain ⟨x₀, rfl⟩ := F.map_surjective x
        obtain ⟨y₀, rfl⟩ := F.map_surjective y
        exact congrArg F.map (hbij.1 hxy)
      · intro y
        obtain ⟨x, hx⟩ := hbij.2 y
        exact ⟨F.map x, hx⟩
    apply isIso_of_yoneda_map_bijective
    intro T
    let e := F.objObjPreimageIso T
    constructor
    · intro x y hxy
      apply (cancel_epi e.hom).mp
      apply (hL (F.objPreimage T)).1
      simpa only [Category.assoc] using congrArg (fun z ↦ e.hom ≫ z) hxy
    · intro y
      obtain ⟨x, hx⟩ := (hL (F.objPreimage T)).2 (e.hom ≫ y)
      refine ⟨e.inv ≫ x, ?_⟩
      change (e.inv ≫ x) ≫ coefficientBaseChangeHom SA SB F μ M N = y
      change x ≫ coefficientBaseChangeHom SA SB F μ M N = e.hom ≫ y at hx
      rw [Category.assoc, hx, Iso.inv_hom_id_assoc]
  let := SA.monoidal
  let := SB.monoidal
  have hright {A B : coefficientSequenceDerived l E X} (f : A ⟶ B)
      (P : coefficientSequenceDerived l E X) :
      SB.tensor.map (Prod.mkHom f (𝟙 P)) = SB.monoidal.whiskerRight f P :=
    @MonoidalCategory.tensorHom_id _ _ SB.monoidal A B f P
  have hleft (P : coefficientSequenceDerived l E X)
      {A B : coefficientSequenceDerived l E X} (f : A ⟶ B) :
      SB.tensor.map (Prod.mkHom (𝟙 P) f) = SB.monoidal.whiskerLeft P f :=
    @MonoidalCategory.id_tensorHom _ _ SB.monoidal P A B f
  obtain ⟨ε, hε⟩ := pullbackTensorSystemComparison_unit l E g
  let s : F.CoreMonoidal := Functor.CoreMonoidal.mk' ε.symm
    (fun M N ↦ (μ.app (M, N)).symm)
    (by
      intro M N f P
      have hn := μ.hom.naturality (Prod.mkHom f (𝟙 P))
      dsimp only [Functor.comp_map, Functor.prod_map] at hn
      rw [(pullbackTensorSequenceDerived l E g).map_id] at hn
      rw [hright] at hn
      simpa only [F, SA, SB, μ, Iso.app, Functor.comp_obj, Functor.prod_obj,
        MonoidalCategory.tensor_obj, CoefficientClosedStructure.tensor,
        Iso.symm_inv, Iso.app_hom,
        MonoidalCategory.tensor_map,
        @MonoidalCategory.tensorHom_id _ _ SA.monoidal,
        @MonoidalCategory.tensorHom_id _ _ SB.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SA.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SB.monoidal] using hn.symm)
    (by
      intro M N P f
      have hn := μ.hom.naturality (Prod.mkHom (𝟙 P) f)
      dsimp only [Functor.comp_map, Functor.prod_map] at hn
      rw [(pullbackTensorSequenceDerived l E g).map_id] at hn
      rw [hleft] at hn
      simpa only [F, SA, SB, μ, Iso.app, Functor.comp_obj, Functor.prod_obj,
        MonoidalCategory.tensor_obj, CoefficientClosedStructure.tensor,
        Iso.symm_inv, Iso.app_hom,
        MonoidalCategory.tensor_map,
        @MonoidalCategory.tensorHom_id _ _ SA.monoidal,
        @MonoidalCategory.tensorHom_id _ _ SB.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SA.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SB.monoidal] using hn.symm)
    (by
      intro M N P
      simpa only [F, SA, SB, μ, Iso.app, Iso.symm_inv, Iso.app_hom,
        CoefficientClosedStructure.tensor,
        Functor.comp_obj, Functor.prod_obj,
        MonoidalCategory.tensor_obj, MonoidalCategory.tensor_map,
        @MonoidalCategory.tensorHom_id _ _ SA.monoidal,
        @MonoidalCategory.tensorHom_id _ _ SB.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SA.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SB.monoidal] using
        (pullbackTensorSystemComparison_associativity l E g M N P).symm)
    (by
      intro M
      have h := (hε M).1
      rw [hright] at h
      apply (cancel_epi (F.map (SA.monoidal.leftUnitor M).hom)).1
      apply (cancel_mono (SB.monoidal.leftUnitor (F.obj M)).hom).1
      simpa only [F, SA, SB, μ, Iso.app, Functor.comp_obj, Functor.prod_obj,
        MonoidalCategory.tensor_obj, Category.assoc,
        ← (pullbackTensorSequenceDerived l E g).map_comp_assoc, Iso.hom_inv_id,
        (pullbackTensorSequenceDerived l E g).map_id,
        Iso.symm_inv, Iso.app_hom,
        Category.id_comp, Iso.inv_hom_id, Category.comp_id,
        CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
        @MonoidalCategory.tensorHom_id _ _ SA.monoidal,
        @MonoidalCategory.tensorHom_id _ _ SB.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SA.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SB.monoidal] using h.symm)
    (by
      intro M
      have h := (hε M).2
      rw [hleft] at h
      apply (cancel_epi (F.map (SA.monoidal.rightUnitor M).hom)).1
      apply (cancel_mono (SB.monoidal.rightUnitor (F.obj M)).hom).1
      simpa only [F, SA, SB, μ, Iso.app, Functor.comp_obj, Functor.prod_obj,
        MonoidalCategory.tensor_obj, Category.assoc,
        ← (pullbackTensorSequenceDerived l E g).map_comp_assoc, Iso.hom_inv_id,
        (pullbackTensorSequenceDerived l E g).map_id,
        Iso.symm_inv, Iso.app_hom,
        Category.id_comp, Iso.inv_hom_id, Category.comp_id,
        CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
        @MonoidalCategory.tensorHom_id _ _ SA.monoidal,
        @MonoidalCategory.tensorHom_id _ _ SB.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SA.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SB.monoidal] using h.symm)
  exact finiteChange_compatible SA SB F μ ⟨s, fun _ _ ↦ rfl⟩

end WeilConjectures
