/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar

/-!
# A right adjoint to proper constructible pushforward with condensed Qlbar coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-coefficients-constructible/
sec-n-brown/sk-thm-existence/
lem-sfb-dc-proper-pushforward-left-adjoint-qlbar.md and its adjacent proof file
(blueprint: theorem-exceptional-inverse-image--17).

The functor is the existing restriction of ambient derived direct image, with coefficient
ring `Profinite.padicAlgClRingObj`, whose sections take values in a finite subextension.
The proof route is descent of finite-coefficient adjunctions along the constructible cocones.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper direct image on bounded constructible condensed Qlbar complexes has a right adjoint.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-coefficients-constructible/
sec-n-brown/sk-thm-existence/
lem-sfb-dc-proper-pushforward-left-adjoint-qlbar.md; adjacent proof, sentences 1--3
(blueprint: theorem-exceptional-inverse-image--17).

Proof:
1. Index the finite coefficient fields by finite intermediate extensions of Q_l in its
   algebraic closure. Composita make this a nonempty directed poset. Scalar extension
   preserves bounded constructibility. Tensor associativity supplies coherent transitions
   and cocones. Object descent and Hom descent (the degree-zero case of the two-colimit
   theorem) give essential surjectivity, eventual representation, and eventual equality.
2. For every finite field E choose the finite-coefficient proper adjunction P_E adjoint to
   G_E. Finite scalar extension commutes with P_E. The exceptional counit transposes of these
   comparisons are invertible by the finite-coefficient-mate theorem. Direct-image mate
   coherence gives normalization, tower compatibility and compatibility with the adjunction
   bijections, units and counits. This forms a compatible system of finite adjunctions.
3. Use the actual Qlbar pushforward as the vertex functor. Properness and boundedness make
   its canonical finite-to-Qlbar direct-image comparisons invertible. The coefficient-tower
   equation makes their inverses a compatible family of vertex comparisons.
4. Apply `condensedQbarExceptionalAdjointColimit` to the two constructible cocones and these
   data. It constructs a right adjoint with natural Hom bijections. On an object descended
   from K_E its value is the Qlbar scalar extension of G_E(K_E), hence bounded constructible.
   The assembly theorem gives functoriality, independence of models and the counit. This
   right adjoint is Rp^!.
-/
theorem properPushforward_isLeftAdjoint_qlbar
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] :
    (boundedConstructibleLowerStar ℓ p).IsLeftAdjoint := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
