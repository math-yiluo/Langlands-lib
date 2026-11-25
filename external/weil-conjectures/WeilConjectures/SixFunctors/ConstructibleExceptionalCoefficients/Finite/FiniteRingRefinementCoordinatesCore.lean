/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusWitnessedCompactification
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedOpenNormalization
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingEndpointCancellation

/-! # Canonical finite proper/open coordinate witness

The finite proper/open construction supplies the unique normalized open comparison
and its endpoint coordinate formula.  This is the geometric part of the refinement
coordinate calculation; the parent theorem only performs the categorical uniqueness
and cancellation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- The finite proper/open comparison constructed from the constant-coefficient
proper/open map has the displayed open-unit normalization and endpoint coordinate
formula.  The construction expands `finiteOpenIso` and `finiteDirectImage_eq`,
transports the canonical `properOpenProEtaleIso` through the fixed witness, and
pastes the proper compositor.  Uniqueness of the open adjunction transpose makes
this witness independent of all presentation choices.
Source: Stacks Tags 03DI, 03D6 and 0F7B; compactification-coherence proof,
first two paragraphs (blueprint: lem-sf-finite-ring-refinement-coordinates-canonical).

Proof: construct the canonical finite proper/open comparison from the normalized
constant-coefficient adjunctions, transport it through the retained witness, and
expand the proper compositor. Naturality and the triangle identities cancel the
endpoint coordinate isomorphisms, yielding the displayed intrinsic refinement word.
-/
theorem finite_ring_refinement_coordinates_canonical
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (O : FrobeniusExchange.CompactOrigin
      (Padic.coefficientExtensionRing l E (n + 1)) X)
    (hi : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull r.hom)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.i))
    (hg : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (r.hom ≫ d.g) =
      proEtaleRingCompositeCoefficients r.hom d.g
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull d.g)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull r.hom)) :
    ∃ ε :
      (PurCompactSupport.openExtension
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.i).mapDerivedCategory.obj O.K ≅
      (PurCompactSupport.push (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n))
        r.hom).obj ((PurCompactSupport.openExtension
          (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c.i).mapDerivedCategory.obj O.K),
      ((PurCompactSupport.openDerivedAdjunction
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.i).homEquiv _ _ ε.hom ≫
        PurCompactSupport.refinementRestriction
          (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) r hi O.K =
      (PurCompactSupport.openDerivedAdjunction
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c.i).unit.app O.K) ∧
      ((PurCompactSupport.geometricPushComposition
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) r.hom d.g hg ≪≫
      eqToIso (congrArg (fun h ↦ PurCompactSupport.push
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) h) r.hom_g)).symm.app _) ≪≫
      (PurCompactSupport.push
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.g).mapIso ε.symm ≪≫
      (PurCompactSupport.finiteImageIso l E n d).app O.K =
    (PurCompactSupport.finiteImageIso l E n c).app O.K ≪≫
      FrobeniusExchange.intrinsicRefinement
        (Padic.coefficientExtensionRing l E (n + 1)) r O := by
  refine ⟨finiteFixedRefinementOpenIso l E n r O,
    finiteFixedRefinementOpenIso_normalization l E n r O hi, ?_⟩
  exact finiteFixedEndpointCancellation l E n r O hg

end WeilConjectures.ConstructibleExceptionalCoefficients
