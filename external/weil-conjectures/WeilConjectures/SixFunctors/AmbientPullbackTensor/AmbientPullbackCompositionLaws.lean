/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackOrdinaryCompositionLaws
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackDerivedCompositionLaws

/-! # Components of ambient pullback coherence

Source: Stacks 03CB, 03D3, 03EL, 07A4 and 04VG.
(blueprint: lem-sf-ambient-pullback-composition-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

/-- Associativity and the two unit laws for the specified pullback comparisons.
Source: Stacks 03CB, 03D3, Categories 0B65 and 04VG
(blueprint: lem-sf-ambient-pullback-composition-laws).
Proof: the section formulas defining pushComp and pushId express their maps as
restriction by the canonical iterated fibre-product comparisons. Both routes
through a triple comparison preserve all projections, so pullback uniqueness
identifies them. Identity comparisons satisfy the corresponding two equations.
Apply Adjunction.leftAdjointCompIso_assoc, leftAdjointCompIso_comp_id and
leftAdjointCompIso_id_comp to the specified adjunctions. The unit characterization
identifies the resulting comparisons with comp and identity. Include the
transport by Category.assoc, comp_id or id_comp to the chosen endpoint functor.
Map the equations termwise to complexes. Full faithfulness of restriction along
the quasi-isomorphism localization transfers all three equations to derived
categories. The exact-factorization isomorphisms identify these localized
comparisons with derivedComp and derivedIdentity. All restrictions, including
horizontal restrictions, occur on the original ringed site. -/
theorem pullback_compositionLaws (K : Scheme.{t}) (s : Option ℕ) :
    CompositionLaws ell E K s := by
  obtain ⟨ho₁, ho₂, ho₃⟩ := ordinary_pullback_compositionLaws ell E K s
  obtain ⟨hd₁, hd₂, hd₃⟩ := derived_pullback_compositionLaws ell E K s
  exact ⟨ho₁, ho₂, ho₃, hd₁, hd₂, hd₃⟩

end WeilConjectures.AmbientPullbackTensor
