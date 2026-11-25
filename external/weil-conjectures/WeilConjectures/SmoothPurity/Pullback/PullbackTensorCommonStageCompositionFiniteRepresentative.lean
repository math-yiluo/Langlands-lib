/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Common.CommonStageCompositionFiniteRepresentativeStageEquation

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Finite-stage representative calculation for common-stage pullback/tensor composition.

Source: Stacks 07A4 and 0941, and the finite-stage representative paragraph of the
common-stage composition proof.  At a coefficient field containing the stages of
all objects in the displayed diagram, expand every common-stage map by its prescribed
rational representative formula.  The two composites then become the same rational
composite after cancellation of the adjacent comparison isomorphisms.  Directedness
of the coefficient stages gives one common representative for the two resulting maps.

This is the finite-stage calculation used by the colimit descent theorem below.
(blueprint: lem-pur-pullback-tensor-common-stage-composition-coherence-finite-representative). -/
theorem commonStageCompositionFiniteRepresentative {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    ∃ (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (hA : ((commonStageDerivedPullback l Ω (h ≫ f)).obj
        ((commonStageDerivedTensor l Ω Y).obj (M, N))).stage ≤ L)
      (hB : ((commonStageDerivedTensor l Ω Z).obj
        ((commonStageDerivedPullback l Ω h).obj
          ((commonStageDerivedPullback l Ω f).obj M),
          (commonStageDerivedPullback l Ω h).obj
            ((commonStageDerivedPullback l Ω f).obj N))).stage ≤ L),
      ∃ r : ((commonStageDerivedPullback l Ω (h ≫ f)).obj
        ((commonStageDerivedTensor l Ω Y).obj (M, N))).toStage hA ⟶
        ((commonStageDerivedTensor l Ω Z).obj
          ((commonStageDerivedPullback l Ω h).obj
            ((commonStageDerivedPullback l Ω f).obj M),
            (commonStageDerivedPullback l Ω h).obj
              ((commonStageDerivedPullback l Ω f).obj N))).toStage hB,
        HEq
          (((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
            ((@commonStageDerivedTensor l _ Ω _ _ _ Z hZ)).map (Prod.mkHom
              (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) M).hom)
              (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) N).hom)))
          (GeneralAlgebraicallyClosedCoefficients.ofHom _ _ L hA hB r) ∧
        HEq
          (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ)
              (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (M, N))).hom ≫
            ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).map
              ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom ≫
            ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z X h hZ hX)
              (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
              (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)).hom)
          (GeneralAlgebraicallyClosedCoefficients.ofHom _ _ L hA hB r) := by
  let A := (commonStageDerivedPullback l Ω (h ≫ f)).obj
    ((commonStageDerivedTensor l Ω Y).obj (M, N))
  let B := (commonStageDerivedTensor l Ω Z).obj
    ((commonStageDerivedPullback l Ω h).obj
      ((commonStageDerivedPullback l Ω f).obj M),
      (commonStageDerivedPullback l Ω h).obj
        ((commonStageDerivedPullback l Ω f).obj N))
  let left :=
    ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
      ((@commonStageDerivedTensor l _ Ω _ _ _ Z hZ)).map (Prod.mkHom
        (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) M).hom)
        (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) N).hom))
  let right :=
    ((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ)
        (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (M, N))).hom ≫
      ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).map
        ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom ≫
      ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z X h hZ hX)
        (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
        (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)).hom
  obtain ⟨L, hA, hB, r, hr⟩ :=
    (GeneralAlgebraicallyClosedCoefficients.representatives A B).1 left
  refine ⟨L, hA, hB, r, ?_, ?_⟩
  · exact heq_of_eq hr
  · exact commonStageCompositionFiniteRepresentative_stageEquation
      l Ω f h M N L hA hB r (heq_of_eq hr)

end WeilConjectures
