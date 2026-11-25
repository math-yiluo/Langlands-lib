/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.CoefficientMorphismBasic
public import WeilConjectures.TraceFormula.CoefficientMorphismFixedPoints
public import WeilConjectures.TraceFormula.CoefficientMorphismPieces

/-!

# Additivity of the trace formula for Frobenius coefficient morphisms

For an open immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X`, both stable under the
Frobenius, and an arbitrary map `ψ : LΦ^* K ⟶ K`, the trace of `RΓ_c(X, ψ) ∘ Φ^♯` is the sum of
the traces of the corresponding operators of the restrictions of `ψ` to `U` and `Z`
(`ProEtale.CondensedRing.trace_compactPullback_comp_eq_add`, blueprint
`lemma-additivity-open-subscheme-complement`, item (3)), and the trace formula in degree one on `U`
and `Z` gives it on `X` (`ProEtale.CondensedRing.TraceFormulaHolds.of_isCompl`, blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Step 5).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

variable (ℓ) in
omit [IsUniversalHomeomorphism ΦZ.left] in
/-- **The operators `E_Z`, `E_U` of a coefficient morphism commute with the connecting morphism
of the compactly supported localization triangle** (blueprint
`lemma-additivity-open-subscheme-complement`, Step 3): `E_Z = RΓ_c(ψ_Z) ∘ Φ^♯` and
`E_U = RΓ_c(ψ_U) ∘ Φ^♯` with coefficients compatible with the unit and the counit of the
localization triangle, so `map_comp_connecting_eq_of_isCompl` applies. -/
theorem CoefficientMorphism.closedPieceOperator_comp_connecting
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))))
    (hδ : Pretriangulated.Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K)) δ ∈ distTriang _) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map (CoefficientMorphism.closedPieceOperator ℓ hi K ψ) ≫
        compactLocalizationConnecting ℓ j i K δ =
      compactLocalizationConnecting ℓ j i K δ ≫ (shiftFunctor _ (1 : ℤ)).map
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (point k).left)).ι.map (CoefficientMorphism.openPieceOperator ℓ hj K ψ)) := by
  have hX := map_comp_connecting_eq_of_isCompl ℓ hcompl hj K δ hδ
    (CoefficientMorphism.openPieceCoefficient ℓ hj K ψ) ψ
    (CoefficientMorphism.closedPieceCoefficient ℓ hi K ψ)
    (CoefficientMorphism.upperStar_map_counit_comp hj K ψ)
    (CoefficientMorphism.upperStar_map_unit_comp_closedPieceCoefficient hi K ψ)
  obtain ⟨δ₀, rfl⟩ := WeilBoundedConstructible.exists_eq_map_comp_commShiftIso
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).fullyFaithfulι
    δ
  rw [connectingOfIso_map_comp_commShiftIso, ← Functor.map_comp_assoc] at hX
  have key₁ := eq_comp_shift_map_of_map_comp_commShiftIso _ _ _ _ hX
  have key₂ := comp_map_comp_commShiftIso_eq_of_commShift
    (boundedConstructibleLowerShriek ℓ (toPoint X))
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ) (compactPullback ℓ Φ)
    (CoefficientMorphism.closedPieceCoefficient ℓ hi K ψ)
    (CoefficientMorphism.openPieceCoefficient ℓ hj K ψ) δ₀
    (key₁.trans (Category.assoc _ _ _))
    (CoefficientMorphism.closedPieceOperator ℓ hi K ψ)
    (CoefficientMorphism.openPieceOperator ℓ hj K ψ)
    (CoefficientMorphism.closedPieceOperator_eq hi K ψ)
    (CoefficientMorphism.openPieceOperator_eq hj K ψ)
  have := HasCompactification.of_over (toPoint X)
  rw [compactLocalizationConnecting, connectingOfIso_map_comp_commShiftIso]
  exact map_comp_commShiftIso_of_comp_eq _ _ _ _ key₂

omit [IsUniversalHomeomorphism ΦZ.left] in
/-- **Additivity of the compactly supported Frobenius operator of a coefficient morphism along an
open–closed decomposition** (blueprint `lemma-additivity-open-subscheme-complement`, item (3)): for
an open immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X`, both stable under the Frobenius,
and an arbitrary map `ψ : LΦ^* K ⟶ K`, the trace of `RΓ_c(X, ψ) ∘ Φ^♯` on `RΓ_c(X, K)` is the
sum of the traces of the operators `RΓ_c(U, ψ|_U) ∘ Φ_U^♯` and `RΓ_c(Z, ψ|_Z) ∘ Φ_Z^♯` of the
restrictions of `ψ`. -/
theorem trace_compactPullback_comp_eq_add [IsSepClosed k]
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj K)]
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint U)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))]
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint Z)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))] :
    trace ((compactPullback ℓ Φ).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map ψ) =
      trace ((compactPullback ℓ ΦU).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint U)).map
          ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map ψ)) +
      trace ((compactPullback ℓ ΦZ).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
          ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map ψ)) := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openClosed ℓ j i hcompl K
  have h₁ := CoefficientMorphism.openPieceOperator_comp_map_counit hj K ψ
  have h₃ := CoefficientMorphism.closedPieceOperator_comp_connecting ℓ hcompl hj hi K ψ δ hδ
  let : HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))) :=
    hasRightDualOfIso ((boundedConstructibleLowerShriekCompToPoint ℓ j).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))
  let : HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))) :=
    hasRightDualOfIso ((boundedConstructibleLowerStarCompToPoint ℓ i).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))
  have hT := compactLocalizationTriangle_distinguished ℓ j i K δ hδ
  have h₂ := CoefficientMorphism.comp_map_unit_eq_map_unit_comp_closedPieceOperator hi K ψ
  dsimp only [Functor.comp_obj, Functor.id_obj] at hT h₁ h₂ h₃
  rw [trace_eq_trace_add_trace_of_distTriang _ _ _ hT _ _ _ h₁ h₂ h₃]
  congr 1
  · let w : (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) ≅
        (boundedConstructibleLowerShriek ℓ (toPoint U)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) :=
      (boundedConstructibleLowerShriekCompToPoint ℓ j).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)
    refine trace_eq_of_iso w _ _ ?_
    simp only [w, CoefficientMorphism.openPieceOperator, Iso.app_hom, Category.assoc,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]
  · let w : (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ≅
        (boundedConstructibleLowerShriek ℓ (toPoint Z)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) :=
      (boundedConstructibleLowerStarCompToPoint ℓ i).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)
    refine trace_eq_of_iso w _ _ ?_
    simp only [w, CoefficientMorphism.closedPieceOperator, Iso.app_hom, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]

omit [IsUniversalHomeomorphism ΦZ.left] in
/-- **The trace formula is additive along open–closed decompositions** (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Step 5, from
`lemma-additivity-open-subscheme-complement`, item (3)): for an open immersion `j : U ⟶ X` with
closed complement `i : Z ⟶ X`, both stable under the Frobenius, the trace formula in degree one on
`U` and on `Z` gives it on `X`: the fixed points of `Φ` are those of `Φ_U` and `Φ_Z`, with the same
stalk maps (`ProEtale.CondensedRing.trace_graphStalkMap_upperStar`). -/
theorem TraceFormulaHolds.of_isCompl [IsSepClosed k]
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (hU : TraceFormulaHolds ℓ ΦU)
    (hZ : TraceFormulaHolds ℓ ΦZ) : TraceFormulaHolds ℓ Φ := by
  intro K ψ _ _ _
  have : Fintype {y : RationalPoint U // y ≫ ΦU = y} :=
    Fintype.ofInjective (fun y ↦ fixedRationalPointsSumEquiv hcompl hj hi (.inl y))
      ((fixedRationalPointsSumEquiv hcompl hj hi).injective.comp Sum.inl_injective)
  have : Fintype {z : RationalPoint Z // z ≫ ΦZ = z} :=
    Fintype.ofInjective (fun z ↦ fixedRationalPointsSumEquiv hcompl hj hi (.inr z))
      ((fixedRationalPointsSumEquiv hcompl hj hi).injective.comp Sum.inr_injective)
  have : HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint U)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) :=
    (nonempty_hasRightDual_point ℓ k _).some
  have : HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint Z)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) :=
    (nonempty_hasRightDual_point ℓ k _).some
  have (y : RationalPoint U) : HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) :=
    (nonempty_hasRightDual_point ℓ k _).some
  have (z : RationalPoint Z) : HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) :=
    (nonempty_hasRightDual_point ℓ k _).some
  rw [trace_compactPullback_comp_eq_add hcompl hj hi K ψ, hU, hZ]
  refine Eq.trans ?_ (Fintype.sum_equiv (fixedRationalPointsSumEquiv hcompl hj hi)
    (fun s ↦ trace (Correspondence.graphStalkMap K Φ ψ
      (fixedRationalPointsSumEquiv hcompl hj hi s).1
      (fixedRationalPointsSumEquiv hcompl hj hi s).2)) _ fun _ ↦ rfl)
  rw [Fintype.sum_sum_type]
  simp only [fixedRationalPointsSumEquiv_inl, fixedRationalPointsSumEquiv_inr]
  exact congrArg₂ (· + ·)
    (Fintype.sum_congr _ _ fun y ↦ trace_graphStalkMap_upperStar hj K ψ y.1 y.2)
    (Fintype.sum_congr _ _ fun z ↦ trace_graphStalkMap_upperStar hi K ψ z.1 z.2)

end AlgebraicGeometry.ProEtale.CondensedRing
