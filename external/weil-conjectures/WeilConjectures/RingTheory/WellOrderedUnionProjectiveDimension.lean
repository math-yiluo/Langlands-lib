/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
import WeilConjectures.RingTheory.WellOrderedUnionProjectiveDimensionZero
import WeilConjectures.RingTheory.WellOrderedUnionProjectiveDimensionSucc

/-!
# Projective dimension of a well-ordered union of submodules

Source: Stacks Project, Algebra, Lemma 0D1U
(blueprint: lem-weil-pbc-well-ordered-union-projective-dimension).
-/

@[expose] public section

universe u v w

namespace ModuleCat

/-- A well-ordered increasing union of submodules whose successive quotients have
projective resolutions of length at most `n` has a projective resolution of length at most `n`.
The predecessor union is represented by its submodule supremum and pulled back along the
inclusion of `F e` into `M`. For a least index this is the zero submodule.
Source: Stacks Project, Algebra, Lemma 0D1U
(blueprint: lem-weil-pbc-well-ordered-union-projective-dimension).

Proof: generalize the module, the index type and all filtration hypotheses before
induction on the length bound. At zero use the splitting/direct-sum base case
`hasProjectiveResolutionLE_of_wellOrderedUnion_zero`. At a successor use
`hasProjectiveResolutionLE_of_wellOrderedUnion_succ`, supplying the generalized
induction hypothesis. The successor obligation constructs a projective presentation,
filters its kernel, applies the induction hypothesis to that kernel and splices its
resolution with the presentation. These two obligations are stated separately;
the induction combining them is complete. -/
theorem hasProjectiveResolutionLE_of_wellOrderedUnion
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) (n : ℕ)
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (hquot : ∀ e : E, HasProjectiveResolutionLE
      (ModuleCat.of R ((F e) ⧸
        ((⨆ e' : {i : E // i < e}, F e'.val).comap (F e).subtype))) n) :
    HasProjectiveResolutionLE M n := by
  revert M E F hF hcover hquot
  induction n with
  | zero =>
      intro M E _ _ F hF hcover hquot
      exact hasProjectiveResolutionLE_of_wellOrderedUnion_zero M F hF hcover hquot
  | succ n ih =>
      intro M E _ _ F hF hcover hquot
      exact hasProjectiveResolutionLE_of_wellOrderedUnion_succ n ih M F hF hcover hquot

end ModuleCat
