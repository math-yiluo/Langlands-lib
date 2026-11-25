/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceData
import WeilConjectures.SixFunctors.Regular.RegularQuotientInjectiveKernel
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAdjoint

/-! # Invertibility of the normalized regular quotient coinduction trace

Source: Tags 06YY, 07A6, 0A70, 0BZE, 0BZH and 08FZ; Zheng Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-regular-quotient-trace-is-iso). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The actual quotient-linear cone trace is an isomorphism on unbounded derived categories.
Source: Stacks Project, Tags 06YY, 07A6, 0A70 and 0A71; the normalized principal quotient
resolution and evaluation-at-one coinduction counit.
(blueprint: lem-sf-regular-quotient-trace-is-iso).

Proof: resolve the input by a K-injective complex of injective completed-coefficient
modules. The already constructed ordinary coinduction counit is the kernel of the
positive uniformizer scalar. That scalar is surjective on each injective term, so
these maps form a short exact sequence of complexes. Its connecting triangle identifies
the scalar cone with restricted coinduction shifted by one. The derived coinduction
comparison computes coinduction termwise on this resolution. Its counit is the
localization of the ordinary counit. The cone augmentation adjoint formula, with its
zero shifted component, identifies the adjoint of the displayed trace with the shifted
boundary of this same short exact sequence. Consequently the restricted trace is the
inverse of the preceding cone comparison. Exact restriction detects derived
isomorphisms, since it preserves homology and reflects ordinary module isomorphisms.
Thus the quotient-linear trace is invertible on the resolution. Naturality and the
invertible resolution map give it on the original input; componentwise invertibility
gives invertibility of the natural transformation. This uses neither boundedness nor
constructibility and includes n=0 and the empty scheme. -/
theorem reductionCoinductionTrace_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    IsIso (reductionCoinductionTrace.{u} l E T n) := by
  sorry

end WeilConjectures
