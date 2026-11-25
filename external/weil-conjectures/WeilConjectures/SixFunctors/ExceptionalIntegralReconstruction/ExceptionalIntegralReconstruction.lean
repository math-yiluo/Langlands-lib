/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionEquivalence
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralSystemExistence
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralNormalizedAdjunction
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralRealizationAssembly

/-! # Integral exceptional reconstruction assembly -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.ExceptionalIntegralReconstruction
open IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Actual integral reconstruction and the normalized compact-support adjunction.
All operations, stability assertions and comparisons are conclusions, and absolute
separatedness of X and Y is not assumed.

Source: Zheng, Propositions 2.23, 2.29, 3.16, Lemma 5.22 and Proposition 5.24;
blueprint exceptional inverse-image construction, integral steps 10--12
(blueprint: lem-sf-exceptional-integral-reconstruction).

Proof:
1. Restrict the actual reduction/limit adjunction to complete objects and normalized
systems. Its unit and counit are invertible by actual reconstruction. Reduction and
the evaluated counit retain precisely the common constructible, cohomological and
Tor intervals, giving the equivalence of these full subcategories. The sequence-site
resolution comparison identifies its unit with the compatible quotient cone and its
counit with the scalar adjunct of the actual total-limit projection.
2. The compactification's middle scheme is finite type over k, and its open immersion
is quasi-compact by Noetherianity. Transport the ordinary-etale system adjunction.
Its fixed evaluations give uniform finite cohomological and Tor bounds. The right
operation preserves normalization. The left does too: integral compact support and
its successive reduction comparisons identify every transition adjunct with a
composite of isomorphisms; every normalized input is a reduction by step 1. The
constructible-origin theorem gives the compatible site origins. Open extension
retains the bounds at the intermediate object. No absolute separatedness is used.
3. Compose the two reconstruction adjunctions with the restricted system adjunction.
The resulting Hom chain is Hom(L F R K,L') = Hom(F R K,R L') =
Hom(R K,G R L') = Hom(K,L G R L'). Its unit and counit are exactly those of
integralAdjunction; substitution of the identities gives the triangle equations.
4. The actual reconstruction counits, followed by the system evaluation comparisons,
give leftEvaluation and rightEvaluation. Substitution of the composite-adjunction
unit and counit and the reconstruction triangle identities identifies their finite
maps with the fixed system and finite adjunction maps, including quotient transitions.
The uniform bounds from step 2 apply independently of the level.
5. The full integral finite-Tor category is triangulated. Flat-term K-flat sequence
models compute reduction and its cones and shifts. Simultaneous K-injective tower
models compute limit; signed Roos reindexing identifies its shift with the derived
one. Transport exactness and shifts through the equivalence and system adjunction.
Uniqueness of the adjoint shift gives the displayed rightShift_adjoint equation
and shift compatibility of the unit and counit.
6. The primitive integral direct comparison identifies the entire proper/open
reduction tower with the prescribed compact-support tower, retaining all quotient
transitions. Reconstruction and full faithfulness give its finite-Tor lift and the
identification u, so this prescribed functor can be the integral left adjoint.
7. For the same proper/open word, use the inverse open-adjunction mate of reduction
pullback and the proper direct-image/limit comparison. The open-extension completion
unit is invertible. Their composite, in precisely the order written in primitive,
is the actual ambient realization r. The quotient-cone normalization identifies
the prescribed h with the inverse canonical ambient-to-tower realization.
8. The preceding whole-tower identification and primitive normalization give
I(u) = r followed by h inverse. Cancellation is on these actual integral maps;
no joint faithfulness of finite reduction is invoked.
9. Exact open localization, proper right derivation, termwise quotient models and
signed Roos cones give the same shifts on these normalized comparisons. Their
primitive squares paste to leftCompositeShift, rightCompositeShift, realizationShift,
prescribedRealizationShift and identificationShift. Zero, negative and composite
shifts retain their cochain signs and satisfy the CommShift coherence laws. -/
theorem exceptionalIntegralReconstruction (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    (∀ (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))],
      Nonempty (Reconstruction l E T)) ∧
    ∃ (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
      (s : Systems l E c) (a : SystemAdjunction l E c s),
      Nonempty (Realization l E c D hl rX rY s a) := by
  have hrec : ∀ (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))],
      Nonempty (Reconstruction l E T) := fun T ↦
    exceptionalIntegralReconstructionEquivalence l E D hl T
  obtain ⟨rX⟩ := hrec X
  obtain ⟨rY⟩ := hrec Y
  obtain ⟨s⟩ := exceptionalIntegralSystemExistence l E D hl f c
  obtain ⟨a⟩ := exceptionalIntegralNormalizedAdjunction l E D hl f c rX s
  obtain ⟨t, ht⟩ := exceptionalIntegralRealizationAssembly l E D hl f c rX rY s a
  exact ⟨hrec, rX, rY, { s with transport := t }, a.withTransport l E c s t, ht⟩

end WeilConjectures.ExceptionalIntegralReconstruction
