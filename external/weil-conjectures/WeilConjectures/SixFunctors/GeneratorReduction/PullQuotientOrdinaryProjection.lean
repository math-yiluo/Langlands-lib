/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.GeneratorReduction.PullQuotientOrdinaryProjectionSection

/-! # Ordinary projections of the quotient pullback mate

Source: Stacks 03D7 and 0941; the primitive coefficient comparisons in
`fix-prop-coherence.proof.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Each ordinary limit projection of the pullback/scalar mate is the quotient
augmentation transported by the specified strict pullback tower. This is an equality
of cochain maps at one finite level, for arbitrary complexes, before localization.

Source: Stacks Project, Tag 03D7, sites-modules.tex,
lemma-adjoint-pullback-pushforward-modules; Tag 03EL,
lemma-tensor-product-pullback; Tag 0941, sites-cohomology.tex,
lemma-derived-limit-is-ok; current blueprint
`sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`, maps-used sentence.
(blueprint: lem-sf-pull-quotient-ordinary-projection).

Proof: Work in each degree. By the unit identity for adjoint conjugates,
the ordinary reduction unit followed by the limit of a.reductionPull is the
transpose of the sequence pullback unit through a.comparison. Project to n.
The equation a.projections identifies this with the finite direct-image projection
of that sequence unit. The normalization of pullbackTensorSequenceInverseEvaluation
identifies its finite pullback adjunct; the normalization of
pullbackTensorReductionEvaluation identifies the scalar adjunct. After inserting
the two inverse evaluation comparisons in pullbackTensorPullbackTower, the result
sends the ordinary pullback unit of x to the finite pullback unit of 1 tensor x.
The equation p.generators gives exactly this value for the quotient augmentation
followed by p.tower. The ordinary pullback adjunction is injective on Hom sets,
so equality on all original sections proves equality of the two completed-linear
maps on the pulled module. This holds in every degree and proves equality of
cochain maps. Quotient exponent one, zero complexes, empty schemes and identity
maps use the same unit identities; no completeness or K-flatness is required. -/
theorem pullQuotientOrdinaryProjection
    (a : IntegralSystemRealization.OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : OpenFactorCoherence.Pull l E f)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    let R := (OpenFactorCoherence.pullCx l E f).obj P
    let C := ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
      (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P)
    let Z := ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C
    ((pullbackTensorOrdinaryAdjunction l E X).mapHomologicalComplex (.up ℤ)).unit.app R ≫
        ((pullbackTensorOrdinaryLimit l E X).mapHomologicalComplex (.up ℤ)).map
          (a.reductionPullComplex l E f P) ≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E X ⋙
            pullbackTensorConstantLimit l E X)) (.up ℤ)).inv.app C ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app Z ≫
        (pullbackTensorPullbackTower l E f P).hom.app (op n) =
      ((IntegralOnSlice.augmentation l E X none).app R).app (op n) ≫
        (p.tower.hom.app P).app (op n) := by
  intro R C Z
  apply HomologicalComplex.hom_ext
  intro i
  ext V x
  exact pullQuotientOrdinaryProjection_section l E a f p P n i V x

end WeilConjectures.GeneratorReduction
