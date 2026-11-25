/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Depth is bounded by support dimension

Source: Stacks Project, Algebra, Lemma 00LK (lemma-bound-depth)
(blueprint: lem-weil-pbc-depth-le-support-dimension).
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- The depth of a nonzero finite module over a Noetherian local ring is at most
its support dimension. Source: Stacks Project, Algebra, Lemma 00LK
(blueprint: lem-weil-pbc-depth-le-support-dimension).

Proof:
1. Nakayama gives `m M ≠ M`, so depth is the supremum of lengths of
   `M`-regular sequences in the maximal ideal.
2. For each such list `rs`, Mathlib's
   `Module.supportDim_add_length_eq_supportDim_of_isRegular` gives
   `dim Supp(M/(rs)M) + length(rs) = dim Supp(M)`. Regularity makes the
   quotient nonzero, so its support dimension is nonnegative. Thus
   `length(rs) ≤ dim Supp(M)`, including when this dimension is infinite.
3. The support dimension of `M` is not bottom. Write it as a coercion from
   `ℕ∞`, apply the preceding bound to every regular sequence, and take the
   supremum defining depth. -/
theorem depth_le_supportDim {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    (IsLocalRing.depth (R := R) M : WithBot ℕ∞) ≤ Module.supportDim R M := by
  have hm : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  have hd := Module.supportDim_ne_bot_of_nontrivial R M
  rw [← WithBot.coe_unbot (Module.supportDim R M) hd]
  apply WithBot.coe_le_coe.mpr
  unfold IsLocalRing.depth Ideal.depth
  rw [ite_eq_right hm]
  apply sSup_le
  rintro n ⟨rs, hreg, _, rfl⟩
  apply WithBot.coe_le_coe.mp
  rw [WithBot.coe_unbot]
  let := hreg.quot_ofList_smul_nontrivial (⊤ : Submodule R M)
  have hq := Module.supportDim_ne_bot_of_nontrivial R
    (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))
  have hzero : 0 ≤ Module.supportDim R
      (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) := by
    rw [← WithBot.coe_unbot _ hq]
    exact WithBot.coe_le_coe.mpr zero_le
  calc
    ((rs.length : ℕ∞) : WithBot ℕ∞) ≤
        Module.supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) + rs.length := by
      simpa only [add_zero, add_comm, WithBot.coe_natCast] using
        add_le_add_right hzero (rs.length : WithBot ℕ∞)
    _ = Module.supportDim R M :=
      Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg

end IsLocalRing
