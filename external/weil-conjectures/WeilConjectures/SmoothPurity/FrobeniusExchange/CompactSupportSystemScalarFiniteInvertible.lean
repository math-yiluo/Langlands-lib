/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
import WeilConjectures.SmoothPurity.FrobeniusExchange.CompactSupportScalarEvaluationSquare

/-! # Finite evaluation of the compact-support scalar mate

Source: proposition-six-operations-change-coefficients, compact-support paragraph; Stacks 0GL6 and
09AL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FrobeniusExchange

/-- A single evaluation of the actual proper/open system scalar mate is invertible
when both the input evaluation and its scalar extension are bounded constructible.
There is no completeness, cartesian-system, uniform-interval or limit hypothesis.

Source: proposition-six-operations-change-coefficients, compact-support paragraph; Stacks 0GL6,
09AL; Zheng, Construction 4.1 and Lemma 4.10.
(blueprint: lem-sf-compact-support-system-scalar-finite-invertible).

Proof: put A = O_E/(pi_E^(n+1)) and B = O_L/(pi_L^(n+1)), with the recorded
quotient map induced by the embedding. The first bounded constructibility hypothesis
and finiteRing_constructibleDerived_origin give a bounded constructible etale
antecedent G of the evaluated input. Evaluation of system scalar extension is
ordinary derived scalar extension A -> B, by its K-flat tensor comparison. The
canonical tensor/pullback comparison therefore identifies the intrinsic realization
of G tensor_A^L B with the evaluated scalar input. The second hypothesis makes
this realization bounded. Exactness and faithfulness of etale/pro-etale inverse
image reflect vanishing of cohomology sheaves, so G tensor_A^L B is bounded below;
choose it as the etale antecedent GB. These comparisons work for arbitrary system
inputs at this single index and need no information about their transitions.

Apply intrinsicCompactScalarIsoOfOrigin_hom to G, GB and the fixed compactification.
It identifies the intrinsic scalar-adjunction transpose with an isomorphism. Evaluate
the defining systemCompactScalar word: the direct-image evaluation comparison and
the scalar evaluation comparison identify the proper mate with the proper finite
scalar transpose; the open evaluation comparison identifies the other factor with
the exact finite open scalar isomorphism. The unit and counit evaluation equations
in SemilinearSections.evaluation_mate and mate pasting show that their composite is
the intrinsic compact-support scalar transpose. Conjugate by these evaluation
isomorphisms and the chosen antecedent isomorphism. Thus the displayed evaluated
map is invertible. This uses equality of the specified adjunction words, rather
than detection of equality by evaluation, and assumes no flatness of A -> B.
The argument includes zero inputs, identity embeddings and empty schemes. -/
theorem systemCompactScalar_evaluation_isIso
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y]
    (N : coefficientSequenceDerived l E X) (n : ℕ)
    (hN : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
      ((coefficientSequenceDerivedEvaluation l E X n).obj N))
    (hS : intrinsicFiniteTorsionConstructible l L (n + 1) (Nat.succ_pos n) X
      ((coefficientSequenceDerivedEvaluation l L X n).obj
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj N))) :
    IsIso ((coefficientSequenceDerivedEvaluation l L Y n).map
      ((systemCompactScalar l E L ι c).app N)) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := Padic.coefficientExtensionRing l L (n + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : Finite B := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
  obtain ⟨s, hs⟩ := systemCompactScalar_evaluation_square l E L ι c n
  let φ := integralScalarQuotientMap l E L ι n
  let K := (coefficientSequenceDerivedEvaluation l E X n).obj N
  have hSf : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X B)) i).obj
        ((pbcDerivedExtend (FiniteCompactScalar.scalarRingMap φ X)).obj K))} := by
    apply hS.1.subset
    intro i hi hz
    exact hi (hz.of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso ((s X).app N)).symm)
  have := FiniteCompactScalar.intrinsicCompactScalar_isIso_of_constructible
    φ c K hN.1 hN.2 hSf
  have hcomp : IsIso
      ((coefficientSequenceDerivedEvaluation l L Y n).map
          ((systemCompactScalar l E L ι c).app N) ≫
        (systemCompactEvaluation l L c n).hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj N) ≫
        (sfIntrinsicCompactSupport c B).map ((s X).hom.app N)) := by
    rw [hs N]
    infer_instance
  have : IsIso
      ((coefficientSequenceDerivedEvaluation l L Y n).map
          ((systemCompactScalar l E L ι c).app N) ≫
        (systemCompactEvaluation l L c n).hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj N)) := by
    rw [← Category.assoc] at hcomp
    exact IsIso.of_isIso_comp_right _
      ((sfIntrinsicCompactSupport c B).map ((s X).hom.app N))
  exact IsIso.of_isIso_comp_right _
    ((systemCompactEvaluation l L c n).hom.app
      ((integralComparisonDerivedSequenceScalar l E L ι X).obj N))

end WeilConjectures.FrobeniusExchange
