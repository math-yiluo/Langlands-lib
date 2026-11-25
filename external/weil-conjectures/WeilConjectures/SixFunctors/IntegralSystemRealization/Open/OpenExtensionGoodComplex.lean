/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenExtensionGoodComplexExtension
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenExtensionGoodComplexPullback

/-! # Good representatives under completed-ring open extension

Source: Stacks Tags 03DI, 03DJ, 0E8I and 0G7E.
(blueprint: lem-sf-open-extension-good-complex).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

local instance goodOpen_additive {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).Additive :=
  (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j).left_adjoint_additive

/-- Completed-ring open extension and its restriction preserve good representatives.
Source: Stacks 03DI, 03DJ, 0E8I and 0G7E; the first step of the localization proof
(blueprint: lem-sf-open-extension-good-complex).

Proof: present the actual open extension as ringed slice extension, after the
coefficient and site equivalences of proEtaleOpen_slicePresentation. These are the
ringed-site equivalences: their sectionwise tensor comparisons identify flatness
and the acyclic total-tensor tests for K-flatness. Slice extension preserves flat
terms and K-flatness by ringedOpen_preserves_flat_resolution. Transport its two
conclusions across the natural isomorphism with the actual open extension;
termwise natural isomorphisms preserve flatness, and total tensor sends chain
isomorphisms to chain isomorphisms. This proves the first conjunct. Apply the
ringed-topos K-flat pullback theorem, including its flat-term conclusion, to the
completed coefficient inverse image and this extended complex. This proves the
second conjunct. The slice construction works for every open, including the
empty and identity opens, and the direct-sum total tensor needs no boundedness. -/
theorem openExtension_goodComplex {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    integralOperationsGoodComplex l E Y
        (((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) j).mapHomologicalComplex
           (.up ℤ)).obj P.obj) ∧
      integralOperationsGoodComplex l E X
        (((integralOrdinaryPull l E j).mapHomologicalComplex (.up ℤ)).obj
          (((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) j).mapHomologicalComplex
             (.up ℤ)).obj P.obj)) := by
  exact ⟨openExtension_goodComplex_extension l E j P,
    openExtension_goodComplex_pullback l E j P⟩

end WeilConjectures.IntegralSystemRealization
