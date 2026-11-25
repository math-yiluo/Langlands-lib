/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.SingularIdealsRelativeBound
import WeilConjectures.RingTheory.SingularIdealsAbsoluteBound

/-! # From an annihilator bound to singular-ideal comparisons

Source: Stacks Project, Tag 07CT, second paragraph and final sentence of the proof.
(blueprint: lem-weil-pbc-singular-ideals-of-annihilator-bound).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- For a finitely presented tower, an annihilator bound makes the relative and absolute
singular ideals contain the extension of the singular ideal of the intermediate algebra.
This comparison involves neither a source algebra `A` nor a factorization into `Λ`.

Source: Stacks Project, Tag 07CT, second paragraph and final sentence of the proof.

Proof: Write `p = algebraMap R D π` and `M = Ann_D(p²)/Ann_D(p)`. Its annihilator is the
ideal of elements `r` such that `p² * x = 0` implies `r * p * x = 0` for every `x`.
Since `D` is Noetherian, `M` is finite. At a prime `q` where `D_q` is flat over `R`,
flat base change of annihilators (Tag 07T8) and `hR` give `M_q = 0`. The finite-module
support criterion (Tag 00L2) therefore supplies an element of `Ann_D(M)` outside `q`.
At a prime `Q` of `B` outside the extension of `H_{D/R}`, the inverse-image prime `q`
is smooth for `D/R`, hence `D_q` is flat over `R`. The preceding annihilator element
maps outside `Q`, and `hbound` puts it in `H_{B/D}`. Thus `D → B` is smooth at `Q`.
The nonsmooth-locus characterization of singular ideals and their radicality imply the
first containment. Smoothness of `R → D` at `q` and of `D → B` at `Q` implies smoothness
of `R → B` at `Q`: choose smooth principal neighbourhoods and localize both so that the
maps compose, using smooth base change and composition (Tags 00T4 and 00TD).
Apply the same radical/zero-locus criterion to get the second containment.
(blueprint: lem-weil-pbc-singular-ideals-of-annihilator-bound). -/
theorem singularIdeals_of_annihilator_bound
    (R : Type u) (D : Type v) (B : Type w)
    [CommRing R] [CommRing D] [CommRing B]
    [Algebra R D] [Algebra R B] [IsNoetherianRing R] [FinitePresentation R D]
    (dB : D →ₐ[R] B)
    (hfp : @FinitePresentation D B _ _ dB.toRingHom.toAlgebra)
    (π : R) (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0)
    (hbound : Ideal.span (dB ''
      {r : D | ∀ x : D, (algebraMap R D π) ^ 2 * x = 0 →
        r * algebraMap R D π * x = 0}) ≤
      @singularIdeal D B _ _ dB.toRingHom.toAlgebra) :
    Ideal.map dB.toRingHom (singularIdeal R D) ≤
      @singularIdeal D B _ _ dB.toRingHom.toAlgebra ∧
    Ideal.map dB.toRingHom (singularIdeal R D) ≤ singularIdeal R B := by
  exact ⟨singularIdeal_map_le_relative_of_annihilator_bound R D B dB hfp π hR hbound,
    singularIdeal_map_le_absolute_of_annihilator_bound R D B dB hfp π hR hbound⟩

end Algebra
