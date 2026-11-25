/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Published.PublishedSystemAmbientPresentation
import WeilConjectures.SixFunctors.Published.PublishedSystemTensorRepresentativeNormalization

/-! # Normalization of the published system presentation

Source: Stacks 03D3, 03EL, 07A4 and 07A7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.pullbackTensorCalculus HasDerivedCategory.standard
  WeilConjectures.CoefficientClosedStructure.tensor
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The published tensor comparison agrees with the ambient comparison under the
specified equality of inverse-image functors, for a single scheme morphism.
Source: Stacks 03D3 and 03EL, and 07A4
(blueprint: lem-sf-published-system-tensor-identification).
Proof: identify the ordinary inverse images by sequence_inverse_eq. The normalized
ordinary tensor map sends the adjunction unit of a pure tensor to the tensor of
its two units. On each summand of the total tensor complex this is exactly the
formula specifying pullbackTensorSequenceCochain. Adjunction-unit injectivity,
pure-tensor extensionality and total-summand extensionality identify these maps.
Invert the ambient representative equation to obtain the defining forward
representative equation of pullbackTensorSystemComparison. Uniqueness follows
from tensorComparison_unique_on_flat_representatives, or equivalently from
faithfulness of restriction to pairs of flat-term K-flat complexes. Cancelling
the tensor-model and exact-localization isomorphisms gives the displayed equation.
All operations occur on the sequence site, including its horizontal arrows.
The argument also applies to zero modules and imposes no transition isomorphisms. -/
theorem publishedSystemTensorIdentification {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : coefficientSequenceDerived l E Y) :
    (WeilConjectures.publishedSystemAmbientPullIso l E f).hom.app
        ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M, N)) ≫
      ((publishedSystemAmbientData l E).tensor f).hom.app (M, N) =
    (pullbackTensorSystemComparison l E f).hom.app (M, N) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((WeilConjectures.publishedSystemAmbientPullIso l E f).hom.app M)
          ((WeilConjectures.publishedSystemAmbientPullIso l E f).hom.app N)) := by
  have heq : publishedSystemTransportedTensor l E f =
      pullbackTensorSystemComparison l E f :=
    publishedSystemTransportedTensor_eq l E f
      (fun P Q hP hQ ↦ publishedSystemTransportedTensor_normalized l E f P Q hP hQ)
  let G := (publishedSystemAmbientData l E).pull f
  apply tensor_comparison_transport_hom_eq
    (pullbackTensorCalculus l E Y).systemClosed.tensor
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (pullbackTensorSequenceDerived l E f) G
    (publishedSystemAmbientPullIso l E f)
    (pullbackTensorSystemComparison l E f)
    ((publishedSystemAmbientData l E).tensor f)
  · simpa only [publishedSystemTransportedTensor] using heq

end WeilConjectures
