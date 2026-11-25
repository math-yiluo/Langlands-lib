/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.RingTheory.SubsingletonH1CotangentOfCharP
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.CharP.Basic

/-!
# Lifting ring maps from fields of positive characteristic

Source: Stacks Project, Algebra, Tag 0320 (3), and the successive lifting argument of Tag 07K4
(blueprint: lem-weil-pbc-field-char-p-nilpotent-lifting).
-/

@[expose] public section

universe u v

namespace RingHom

/-- Ring maps from a field of characteristic `p > 0` lift along nilpotent ideals of rings
annihilated by `p`.

Source: Stacks Project, Algebra, Tag 0320 (3), with the induction of Tag 07K4
(blueprint: lem-weil-pbc-field-char-p-nilpotent-lifting).

Proof:
1. The prime subfield of `K` is `F_p`. Rings annihilated by `p` have a unique `F_p`-algebra
   structure, and all the ring maps in question are automatically `F_p`-algebra maps.
2. The node `lem-weil-pbc-field-char-p-h1-cotangent-vanishing` gives vanishing of the first
   cotangent homology of `K/F_p`. Its differentials form a vector space, hence are projective
   by `lem-weil-pbc-vector-space-projective`. The node
   `lem-weil-pbc-smooth-ring-map-square-zero-lifting` therefore gives lifting along every
   square-zero ideal. This is formal smoothness in Tag 0320 (3), via Tags 031Z and 031J.
3. Starting with `g` into `D/J`, lift successively into `D/J^i` for `1 ≤ i ≤ N`. The kernel
   of `D/J^(i+1) → D/J^i` is `J^i/J^(i+1)` and is square-zero since `2*i ≥ i+1`.
   Each lift still reduces to `g`; at `i = N`, the equality `J^N = 0` identifies the target
   with `D`. This also covers `N = 1`, when `J = 0`. -/
theorem exists_lift_of_field_charP (K : Type u) (D : Type v) [Field K] [CommRing D]
    (p : ℕ) [CharP K p] (hp : 0 < p) (hD : (p : D) = 0)
    (J : Ideal D) (N : ℕ) (hN : 1 ≤ N) (hJ : J ^ N = ⊥) (g : K →+* D ⧸ J) :
    ∃ f : K →+* D, (Ideal.Quotient.mk J).comp f = g := by
  have hN' : 0 < N := by omega
  rcases subsingleton_or_nontrivial D with hsub | hnon
  · let := hsub
    let f : K →+* D :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := by intros; apply Subsingleton.elim
        map_zero' := Subsingleton.elim _ _
        map_add' := by intros; apply Subsingleton.elim }
    refine ⟨f, ?_⟩
    ext x
    exact Subsingleton.elim _ _
  · let := hnon
    let := ZMod.algebra K p
    let : CharP D p := by
      apply (CharP.charP_iff_prime_eq_zero (R := D)
        (CharP.char_prime_of_ne_zero K (by omega))).2
      exact hD
    let := ZMod.algebra D p
    let : Module.Free K (KaehlerDifferential (ZMod p) K) :=
      Module.Free.of_divisionRing K _
    let : Module.Projective K (KaehlerDifferential (ZMod p) K) := Module.Projective.of_free
    have h₁ : Subsingleton (Algebra.H1Cotangent (ZMod p) K) :=
      Algebra.subsingleton_h1Cotangent_of_charP p hp K
    let : Algebra.FormallySmooth (ZMod p) K := Algebra.FormallySmooth.mk inferInstance h₁
    obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift J ⟨N, hJ⟩
      ({ toRingHom := g, commutes' := by
          intro r
          obtain ⟨n, rfl⟩ := ZMod.intCast_surjective r
          simp } : K →ₐ[ZMod p] D ⧸ J)
    refine ⟨f.toRingHom, ?_⟩
    exact congrArg AlgHom.toRingHom hf

end RingHom
