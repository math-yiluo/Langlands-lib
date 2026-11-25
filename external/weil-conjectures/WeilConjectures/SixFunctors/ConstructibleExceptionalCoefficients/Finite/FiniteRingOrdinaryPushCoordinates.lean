/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingOrdinaryNormalizedCompositor

/-! # Ordinary section-normalized finite direct-image compositor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.finite
  AlgebraicGeometry.Scheme.ProEt CategoryTheory.MorphismProperty
set_option backward.defeqAttrib.useBackward true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The ordinary finite compositor is the transported constant-section compositor.
Source: Stacks 03D1 and 03D6; compactification-coherence proof, second paragraph
(blueprint: lem-sf-finite-ring-ordinary-push-coordinates).

Proof: the coefficient map adjoint to the specified inverse-image identification
is the constant-section map, by the adjunction inverse equations. Substitute these
three scalar-map equalities in the transported ordinary compositor. On sections,
all equality transports become identities. The intrinsic compositor acts by
restriction along pullbackComp. The unique section normalization that defines
modulePushComposition_existsUnique therefore identifies the two isomorphisms. -/
theorem finiteOrdinaryPushComposition {U V W : Scheme.{w}} (h : U ⟶ V) (k : V ⟶ W)
    (hc : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (h ≫ k) =
      proEtaleRingCompositeCoefficients h k
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring W)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring V)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring U)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull k)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull h)) :
    (PurCompactSupport.modulePushComposition_existsUnique
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) h k hc).exists.choose =
      finiteTransportedOrdinaryCompositor l E n h k := by
  apply (PurCompactSupport.modulePushComposition_existsUnique _ h k hc).unique
  · exact (PurCompactSupport.modulePushComposition_existsUnique _ h k hc).exists.choose_spec
  · exact finiteTransportedOrdinaryCompositor_normalization l E n h k

end WeilConjectures.ConstructibleExceptionalCoefficients
