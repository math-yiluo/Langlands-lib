/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity

/-! # Open reduction as the normalized adjunction mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical open mate is invertible on complete constructible inputs, and its
output has invertible reconstruction unit.
Source: Stacks 0GL1, 0E8I and 07A7; primitive realization Step 4
(blueprint: lem-sf-integral-open-mate-normalization).

Proof: use integralOpenReductionComparison on the actual slice presentation of j.
Uniqueness of the left adjoints to the fixed reconstruction limit identifies its
reduction calculus with calculus. Uniqueness of extension by zero as the left adjoint
to the fixed inverse image identifies its whole-system open operation with o.extension.
The quotient-complex model equation for m.reductionPull identifies its restriction
square with the specified slice square before localization. Taking open-adjunction
mates therefore identifies the theorem's inverse reduction comparison with
m.openReduction. The theorem proves completeness of the integral open extension and
invertibility of its actual reconstruction unit. Transport these conclusions through
the normalized identifications. The empty open and identity open use the same adjoint
uniqueness and require no nonempty hypothesis. -/
theorem integralOpenMateNormalization (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤)))
    (K : Integral l E X) (hK : sfIntegralConstructible l E X K)
    (hg : Good l E X ((calculus l E X).reduction.obj K))
    (hj : Good l E Y ((Operations.shriek l E o j).obj
      ((calculus l E X).reduction.obj K))) :
    IsIso ((calculus l E Y).adjunction.unit.app ((ringedOpen l E j).obj K)) ∧
      IsIso ((m.openReduction l E j).app K) := by
  have _domain := And.intro hX (And.intro hY hj)
  have htor : finiteTorConstructibleIntegral l E X K := by
    obtain ⟨a, b, c, d, _hab, hcd, hb⟩ := hg.2.1
    refine ⟨hK, c, d, hcd, ?_⟩
    intro n
    obtain ⟨hcd', ht⟩ := (hb n).2.2
    refine ⟨hcd', ?_⟩
    intro L P hL f hf hP M i hi
    obtain ⟨e⟩ := hL
    exact ht L P ⟨e ≪≫ ((calculus l E X).reductionEvaluation n).symm.app K⟩
      f hf hP M i hi
  exact (GeneratorReduction.openReconstructionEffectivity l E o m j K (Or.inl htor)).symm

end WeilConjectures.IntegralSystemRealization
