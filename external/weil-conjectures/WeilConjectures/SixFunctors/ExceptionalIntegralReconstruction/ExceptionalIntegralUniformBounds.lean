/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces

/-! # ExceptionalIntegralUniformBounds
Source: Zheng, Section 5; integral reconstruction, step 2.
(blueprint: lem-sf-exceptional-integral-uniform-bounds).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived AlgebraicGeometry.strictEtaleLevelDerived

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralReconstruction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Common finite cohomological and Tor intervals for the actual exceptional system images.
Source: Zheng, Propositions 2.23, 2.29, 3.16 and 5.24.
(blueprint: lem-sf-exceptional-integral-uniform-bounds).

Proof: give the middle scheme the structure map through its proper factor. It is
finite type over the field, hence Noetherian, and the open factor is quasi-compact.
Choose its finite dimension bound once. At each positive coefficient exponent,
compose the coordinate evaluation comparison, the proper/open finite evaluation,
and the ordinary etale support realization. The site inverse comparison identifies
the result with the intrinsic compact-support functor. For the right image use
the right-adjoint comparison determined by this same support realization and
its adjunction, followed by the derived site comparison. Thus the intrinsic
finite bounds apply to both evaluated outputs. Choose the uniform exceptional
constants before varying the exponent, as in the finite-operations theorem.
Transport constructibility, cohomology vanishing and Tor intervals through these
isomorphisms, and enlarge endpoints by minima and maxima to retain ordered
intervals. These witnesses are precisely LevelBounds. For the empty middle
scheme both operations vanish and [0,0] works; no absolute separatedness of X or
Y and no flatness of coefficient quotients is used.
-/
theorem exceptionalIntegralUniformBounds
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f) (s : Systems l E c) :
    (∀ N, normalized l E X N →
      IntegralSystemRealization.LevelBounds l E Y ((s.left l E c).obj N)) ∧
    (∀ N, normalized l E Y N →
      IntegralSystemRealization.LevelBounds l E X ((s.exceptional l E c).obj N)) := by sorry

end WeilConjectures.ExceptionalIntegralReconstruction
