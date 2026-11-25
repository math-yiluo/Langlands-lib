/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces

/-! # ExceptionalIntegralNormalizationPreservation
Source: Zheng, Section 5; integral reconstruction, step 2.
(blueprint: lem-sf-exceptional-integral-normalization-preservation).
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

/-- The actual quotient transitions stay normalized under both exceptional operations.
Source: Zheng, Construction 4.1, Lemma 5.22 and Proposition 5.24; the normalization
part of integral reconstruction step 2.
(blueprint: lem-sf-exceptional-integral-normalization-preservation).

Proof: express each normalized source system, by the reconstruction counit, as
reduction of its reconstructed integral object. Integral compact support and its
successive-quotient comparison identify every scalar-adjoint transition of the
left image with a composite of reduction isomorphisms. These comparisons concern
the actual whole-system functor: use the ordinary exact open comparison and the
proper derived comparison, together with the coordinate counit. Naturality of the
reconstruction counit transports normalization back to the given input.
For the right image, the normalized input in sequence coordinates gives normalized
transitions in the generic quotient presentation: the quotient-ring square and
the exact-localization evaluation comparisons identify their scalar adjuncts.
Apply the normalization clause of s.transport and change coordinates back. The
inverse coordinate counit and the scalar adjunction triangles cancel the two
coordinate comparisons. The assertion includes every quotient n <= m, including
n = m and residue level zero, and uses no quotient-flatness assumption. Zero input
and empty schemes use the same comparisons, so their transitions stay invertible.
-/
theorem exceptionalIntegralNormalizationPreservation
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f) (s : Systems l E c) (rX : Reconstruction l E X) :
    (∀ N, normalized l E X N →
      IsNormalizedCoefficientSequence l E Y ((s.left l E c).obj N)) ∧
    (∀ N, normalized l E Y N →
      IsNormalizedCoefficientSequence l E X ((s.exceptional l E c).obj N)) := by sorry

end WeilConjectures.ExceptionalIntegralReconstruction
