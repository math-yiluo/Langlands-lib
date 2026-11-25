/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodQuotientTransition.PodQuotientTransitionGenerators
import WeilConjectures.PoincareDuality.Pod.PodOrdinaryQuotientTransitionCubeAux3

/-! # Ordinary quotient scalar and reindexing cube

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-ordinary-quotient-transition-cube).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The normalized quotient associators satisfy the ordinary scalar/reindexing cube.
Source: Stacks 03EL, 06YY, 0941; blueprint dual-Tate compatibility Steps 1 and 5.
(blueprint: lem-pod-ordinary-quotient-transition-cube).

Proof: construct alpha at X and Y by associating the two quotient scalar tensors;
its inverse inserts a unit. Construct beta at E and L by reindexing quotient tensors,
using the coefficient-map projection square. The inverse reverses the relabelling.
These maps preserve all horizontal transitions and vertical restrictions, so they
are isomorphisms of sequence-module functors. Their unit formulas are the four
normalizations in the conclusion. To compare the two routes, evaluate a local
generator with scalar coefficient one and module section x. The four unit formulas,
the ordinary sequence scalar/pullback generator formula, and hb identify both
images with the same quotient of the scalar unit tensor. Linearity extends this to
all scalar coefficients and sheafification extends it to all sections. Thus the
ordinary natural transformations agree. Apply their cochain functors degreewise
to obtain the stated chain-map identity, including every quotient transition.
This statement has no derived functor, reduction calculus, Roos realization, scalar
completion or completeness assumption. Zero modules, the empty scheme, identity
maps, n=0 and ramified coefficient embeddings use the same balanced identities. -/
theorem podOrdinaryQuotientTransitionCube
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (MEY : CompletionUnit.OrdinaryModel l E Y) (MEX : CompletionUnit.OrdinaryModel l E X)
    (MLY : CompletionUnit.OrdinaryModel l L Y) (MLX : CompletionUnit.OrdinaryModel l L X)
    (b : isoReductionIntegralInverse l E g ⋙ integralOrdinaryScalar l E L ι X ≅
      integralOrdinaryScalar l E L ι Y ⋙ isoReductionIntegralInverse l L g)
    (hb : ∀ (N : scalarReductionSource l E Y) (U : X.ProEt)
      (x : N.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      (b.hom.app N).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((isoReductionIntegralInverse l E g).obj N) (op U)
            ((isoReductionCompletedMap l L g).hom.hom.app (op U) a) x) =
        integralOrdinaryTensorSection l E L ι Y N
          (op ((proEtaleIsoPostcompose g).obj U)) a x) :
    ∃ (αX : MEX.tensor ⋙ (integralComparisonSequenceScalarModel l E L ι X).E ≅
        integralOrdinaryScalar l E L ι X ⋙ MLX.tensor)
      (αY : MEY.tensor ⋙ (integralComparisonSequenceScalarModel l E L ι Y).E ≅
        integralOrdinaryScalar l E L ι Y ⋙ MLY.tensor)
      (βE : MEY.tensor ⋙ integralComparisonSequencePullback l E g ≅
        isoReductionIntegralInverse l E g ⋙ MEX.tensor)
      (βL : MLY.tensor ⋙ integralComparisonSequencePullback l L g ≅
        isoReductionIntegralInverse l L g ⋙ MLX.tensor),
      PodQuotientTransition.ScalarNormalized l E L ι X MEX MLX αX ∧
      PodQuotientTransition.ScalarNormalized l E L ι Y MEY MLY αY ∧
      PodQuotientTransition.ReindexNormalized l E g MEY MEX βE ∧
      PodQuotientTransition.ReindexNormalized l L g MLY MLX βL ∧
      ∀ P : CochainComplex (scalarReductionSource l E Y) ℤ,
        (NatIso.mapHomologicalComplex αX (.up ℤ)).inv.app
            ((isoReductionIntegralComplex l E g).obj P) ≫
          ((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
            (.up ℤ)).map ((NatIso.mapHomologicalComplex βE (.up ℤ)).inv.app P) ≫
          (NatIso.mapHomologicalComplex (integralComparisonSequenceScalarPullback l E L ι g)
            (.up ℤ)).hom.app ((MEY.quotient l E Y).obj P) =
        (MLX.quotient l L X).map
            ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P) ≫
          (NatIso.mapHomologicalComplex βL (.up ℤ)).inv.app
            (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
          ((integralComparisonSequencePullback l L g).mapHomologicalComplex (.up ℤ)).map
            ((NatIso.mapHomologicalComplex αY (.up ℤ)).inv.app P) := by
  obtain ⟨αX, hαX⟩ := OrdinaryQuotientCube.scalarComparison_exists l E L ι X MEX MLX
  obtain ⟨αY, hαY⟩ := OrdinaryQuotientCube.scalarComparison_exists l E L ι Y MEY MLY
  obtain ⟨βE, hβE⟩ := OrdinaryQuotientCube.reindexComparison_exists l E g MEY MEX
  obtain ⟨βL, hβL⟩ := OrdinaryQuotientCube.reindexComparison_exists l L g MLY MLX
  refine ⟨αX, αY, βE, βL, hαX, hαY, hβE, hβL, fun P ↦ ?_⟩
  ext i : 1
  simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplex_map_f]
  exact OrdinaryQuotientCube.cube_component l E L ι g MEY MEX MLY MLX b hb αX αY βE βL
    hαX hαY hβE hβL (P.X i)

end WeilConjectures
