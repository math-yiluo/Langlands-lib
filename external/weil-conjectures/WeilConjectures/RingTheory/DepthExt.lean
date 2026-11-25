/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.ULift
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.RingTheory.DepthLeSupportDimension
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Depth via Ext from the residue field

Source: Stacks Project, Algebra, Lemma 10.72.5 (Tag 00LW)
(blueprint: lem-weil-pbc-depth-ext).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Abelian

namespace IsLocalRing

/-- For a nonzero finite module over a Noetherian local ring, depth is the least degree
of nonzero Ext from the residue field (Stacks, Tag 00LW;
(blueprint: lem-weil-pbc-depth-ext)). The `ULift`s place the residue field and the module
in one universe without restricting either carrier; `ULift.moduleEquiv` identifies each
lift with the original module.

Proof (using Mathlib's Rees theorem, `Mathlib.RingTheory.Depth.Rees`):
1. Nakayama gives `m M ≠ M`, so depth is the supremum of regular-sequence lengths.
   The support-dimension bound and finite local Krull dimension make it a natural
   number `d`. The empty sequence ensures the set is nonempty; a finite supremum
   in `ℕ∞` belongs to the set, giving a regular sequence of length `d`.
2. Lift `M` and the residue field to the common universe already used in the statement.
   `ULift.moduleEquiv` preserves regularity and support. The lifted residue field
   has support exactly `V(m)`, and Nakayama also gives `m (ULift M) ≠ ULift M`.
3. Rees, `ModuleCat.subsingleton_ext_of_exists_isRegular`, applied to the sequence
   of length `d`, gives vanishing of the stated Ext groups in all degrees below `d`.
4. If Ext in degree `d` were also zero, all degrees below `d+1` would vanish.
   Rees, `ModuleCat.exists_isRegular_of_exists_subsingleton_ext`, would give a
   regular sequence of length `d+1`. Transporting it back to `M` contradicts the
   supremum defining depth. Thus degree `d` is nonzero, including when `d=0`. -/
theorem exists_depth_eq_ext_degree {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ∃ i : ℕ, depth (R := R) M = (i : ℕ∞) ∧
      Nontrivial (Ext (ModuleCat.of R (ULift.{v} (R ⧸ maximalIdeal R)))
        (ModuleCat.of R (ULift.{u} M)) i) ∧
      ∀ j : ℕ, j < i →
        Subsingleton (Ext (ModuleCat.of R (ULift.{v} (R ⧸ maximalIdeal R)))
          (ModuleCat.of R (ULift.{u} M)) j) := by
  classical
  have hm : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  have hdef : depth (R := R) M = sSup {n : ℕ∞ | ∃ rs : List R,
      RingTheory.Sequence.IsRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
        n = (rs.length : ℕ∞)} := by
    simp only [depth, Ideal.depth, ite_eq_right hm]
  have hfinite : depth (R := R) M ≠ ⊤ := by
    intro heq
    have hbound := (depth_le_supportDim (R := R) M).trans
      (Module.supportDim_le_ringKrullDim R M)
    rw [heq] at hbound
    exact (ne_of_lt (ringKrullDim_lt_top (R := R))) (by simpa using hbound)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hsupmem : depth (R := R) M ∈ {n : ℕ∞ | ∃ rs : List R,
      RingTheory.Sequence.IsRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
        n = (rs.length : ℕ∞)} := by
    rw [hdef]
    have hempty : RingTheory.Sequence.IsRegular (R := R) M [] := by
      simp [RingTheory.Sequence.isRegular_iff]
    let : Nonempty {n : ℕ∞ | ∃ rs : List R,
        RingTheory.Sequence.IsRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
          n = (rs.length : ℕ∞)} := ⟨⟨0, [], hempty, by simp, rfl⟩⟩
    apply ENat.sSup_mem_of_nonempty_of_lt_top
    simpa only [← hdef] using hfinite.lt_top
  obtain ⟨rs, hrs, hmem, hlen⟩ := hsupmem
  have hlen' : rs.length = d := by
    rw [← hd] at hlen
    exact_mod_cast hlen.symm
  let L := ModuleCat.of R (ULift.{u} M)
  let K := ModuleCat.of R (ULift.{v} (R ⧸ maximalIdeal R))
  let e : ULift.{u} M ≃ₗ[R] M := ULift.moduleEquiv
  have hL : maximalIdeal R • (⊤ : Submodule R L) < ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R L))).symm.lt_top
  have hK : Module.support R K = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
    rw [(ULift.moduleEquiv : ULift.{v} (R ⧸ maximalIdeal R) ≃ₗ[R]
      (R ⧸ maximalIdeal R)).support_eq, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient]
  have hvan : ∀ j : ℕ, j < d → Subsingleton (Ext K L j) := by
    intro j hj
    apply ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) K hK.subset
      L hL rs hmem ((e.isRegular_congr rs).mpr hrs) j
    simpa only [hlen'] using hj
  refine ⟨d, hd.symm, ?_, hvan⟩
  apply not_subsingleton_iff_nontrivial.mp
  intro hz
  have hvan' : ∀ j : ℕ, j < d + 1 → Subsingleton (Ext K L j) := by
    intro j hj
    by_cases hjd : j < d
    · exact hvan j hjd
    · have : j = d := by omega
      simpa only [this] using hz
  obtain ⟨qs, hqlen, hqmem, hqreg⟩ :=
    ModuleCat.exists_isRegular_of_exists_subsingleton_ext (maximalIdeal R) (d + 1)
      L hL K hK hvan'
  have hbound : ((d + 1 : ℕ) : ℕ∞) ≤ depth (R := R) M := by
    rw [hdef]
    exact le_sSup ⟨qs, (e.isRegular_congr qs).mp hqreg, hqmem, by simp [hqlen]⟩
  rw [← hd] at hbound
  have : d + 1 ≤ d := by exact_mod_cast hbound
  omega

end IsLocalRing
