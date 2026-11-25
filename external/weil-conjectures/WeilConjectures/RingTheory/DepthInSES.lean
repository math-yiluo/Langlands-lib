/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.RingTheory.DepthExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Depth in a short exact sequence

Source: Stacks Project, Algebra, Lemma Tag 00LX (blueprint: lem-weil-pbc-depth-in-ses).
-/

@[expose] public section

universe u v₁ v₂ v₃

namespace IsLocalRing

private theorem depth_equiv {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v₁} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {P : Type v₂} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (e : M ≃ₗ[R] P) : depth (R := R) M = depth (R := R) P := by
  have hmap : (maximalIdeal R • (⊤ : Submodule R M)).map e.toLinearMap =
      maximalIdeal R • (⊤ : Submodule R P) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]
  have htop : (maximalIdeal R • (⊤ : Submodule R M) = ⊤) ↔
      (maximalIdeal R • (⊤ : Submodule R P) = ⊤) := by
    constructor
    · intro h
      rw [← hmap, h]
      simp
    · intro h
      rw [← hmap] at h
      exact (Submodule.map_eq_top_iff.mp h)
  unfold depth Ideal.depth
  split_ifs with hM hP hP
  · rfl
  · exact (hP (htop.mp hM)).elim
  · exact (hM (htop.mpr hP)).elim
  · congr 1
    ext n
    constructor
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mp hreg, hmem, rfl⟩
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mpr hreg, hmem, rfl⟩

/-- Stacks Project, Algebra, Lemma Tag 00LX (blueprint: lem-weil-pbc-depth-in-ses).
The depth inequalities for a short exact sequence of nonzero finite modules over a
Noetherian local ring, proved as follows.

1. By Tag 00LW (lem-weil-pbc-depth-ext), each depth is the least degree of a nonzero
   Ext group from the residue field. Thus depth at least n is equivalent to Ext
   vanishing in every degree i with 0 ≤ i < n.
2. Tag 00LU (lem-weil-pbc-ext-long-exact-second-variable) gives the three consecutive
   pieces of the long exact Ext sequence, and injectivity of Hom into the middle
   term. In an exact triple, zero outer terms force the middle term to be zero.
3. For n = min(depth N', depth N''), both outer Ext groups vanish for i < n.
   Exactness forces Ext of N to vanish in those degrees, proving (1).
4. For n = min(depth N, depth N' - 1), Ext of N in degree i and of N' in degree
   i + 1 vanish when 0 ≤ i < n. Exactness gives vanishing of Ext of N'', proving
   (2). When depth N' = 0, the inequality is automatic by nonnegativity; truncated
   subtraction on extended naturals expresses the same bound.
5. For n = min(depth N, depth N'' + 1), Ext of N vanishes for i < n. In degree
   zero, injectivity gives vanishing for N'. In degree i ≥ 1, Ext of N'' in degree
   i - 1 also vanishes, so exactness gives vanishing for N', proving (3). -/
theorem depth_in_short_exact
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N' : Type v₁} [AddCommGroup N'] [Module R N'] [Module.Finite R N'] [Nontrivial N']
    {N : Type v₂} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    {N'' : Type v₃} [AddCommGroup N''] [Module R N''] [Module.Finite R N''] [Nontrivial N'']
    (f : N' →ₗ[R] N) (g : N →ₗ[R] N'')
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    depth (R := R) N ≥ min (depth (R := R) N') (depth (R := R) N'') ∧
      depth (R := R) N'' ≥ min (depth (R := R) N) (depth (R := R) N' - 1) ∧
      depth (R := R) N' ≥ min (depth (R := R) N) (depth (R := R) N'' + 1) := by
  let A := ULift.{max u v₁ v₂ v₃} N'
  let B := ULift.{max u v₁ v₂ v₃} N
  let C := ULift.{max u v₁ v₂ v₃} N''
  obtain ⟨a, ha, haN, haV⟩ := exists_depth_eq_ext_degree (R := R) A
  obtain ⟨b, hb, hbN, hbV⟩ := exists_depth_eq_ext_degree (R := R) B
  obtain ⟨c, hc, hcN, hcV⟩ := exists_depth_eq_ext_degree (R := R) C
  have haD : depth (R := R) N' = (a : ℕ∞) :=
    (depth_equiv (ULift.moduleEquiv : A ≃ₗ[R] N')).symm.trans ha
  have hbD : depth (R := R) N = (b : ℕ∞) :=
    (depth_equiv (ULift.moduleEquiv : B ≃ₗ[R] N)).symm.trans hb
  have hcD : depth (R := R) N'' = (c : ℕ∞) :=
    (depth_equiv (ULift.moduleEquiv : C ≃ₗ[R] N'')).symm.trans hc
  let eA : ULift.{u} A ≃ₗ[R] N' := ULift.moduleEquiv.trans ULift.moduleEquiv
  let eB : ULift.{u} B ≃ₗ[R] N := ULift.moduleEquiv.trans ULift.moduleEquiv
  let eC : ULift.{u} C ≃ₗ[R] N'' := ULift.moduleEquiv.trans ULift.moduleEquiv
  let S := ModuleCat.shortComplexOfConj eA eB eC f g hfg.linearMap_comp_eq_zero
  have hS : S.ShortExact :=
    ModuleCat.shortComplexOfConj_shortExact eA eB eC f g hfg hf hg
  have : CategoryTheory.Mono S.f := hS.mono_f
  let K := ModuleCat.of R (ULift.{max u v₁ v₂ v₃} (R ⧸ maximalIdeal R))
  have h₁ : min a c ≤ b := by
    by_contra h
    have hlt := lt_of_not_ge h
    have := haV b (hlt.trans_le (min_le_left _ _))
    have := hcV b (hlt.trans_le (min_le_right _ _))
    have : Subsingleton (CategoryTheory.Abelian.Ext K S.X₂ b) := by
      apply subsingleton_of_forall_eq 0
      intro x
      obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₂ K hS x
        (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, CategoryTheory.Abelian.Ext.zero_comp] at hy
      exact hy.symm
    let := hbN
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (CategoryTheory.Abelian.Ext K S.X₂ b)
    exact hxy (Subsingleton.elim _ _)
  have h₂ : min b (a - 1) ≤ c := by
    by_contra h
    have hlt := lt_of_not_ge h
    have hca : c + 1 < a := by omega
    have := hbV c (hlt.trans_le (min_le_left _ _))
    have := haV (c + 1) hca
    have : Subsingleton (CategoryTheory.Abelian.Ext K S.X₃ c) := by
      apply subsingleton_of_forall_eq 0
      intro x
      obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₃ K hS x rfl
        (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, CategoryTheory.Abelian.Ext.zero_comp] at hy
      exact hy.symm
    let := hcN
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (CategoryTheory.Abelian.Ext K S.X₃ c)
    exact hxy (Subsingleton.elim _ _)
  have h₃ : min b (c + 1) ≤ a := by
    by_contra h
    have hlt := lt_of_not_ge h
    have := hbV a (hlt.trans_le (min_le_left _ _))
    have : Subsingleton (CategoryTheory.Abelian.Ext K S.X₁ a) := by
      cases a with
      | zero =>
        exact Function.Injective.subsingleton
          (CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono K S.f)
      | succ i =>
        have hic : i < c := by omega
        have := hcV i hic
        apply subsingleton_of_forall_eq 0
        intro x
        obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ K hS x
          (Subsingleton.elim _ _) rfl
        rw [Subsingleton.elim y 0, CategoryTheory.Abelian.Ext.zero_comp] at hy
        exact hy.symm
    let := haN
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (CategoryTheory.Abelian.Ext K S.X₁ a)
    exact hxy (Subsingleton.elim _ _)
  rw [haD, hbD, hcD]
  constructor
  · have hm : (min (a : ℕ∞) (c : ℕ∞)) = ((min a c : ℕ) : ℕ∞) := by
      rfl
    rw [hm]
    exact_mod_cast h₁
  constructor
  · have hs : (a : ℕ∞) - 1 = ((a - 1 : ℕ) : ℕ∞) := by
      exact (ENat.natCast_sub a 1).symm
    rw [hs]
    have hm : (min (b : ℕ∞) ((a - 1 : ℕ) : ℕ∞)) =
        ((min b (a - 1) : ℕ) : ℕ∞) := by rfl
    rw [hm]
    exact_mod_cast h₂
  · have hs : (c : ℕ∞) + 1 = ((c + 1 : ℕ) : ℕ∞) := by
      exact (ENat.natCast_add c 1).symm
    rw [hs]
    have hm : (min (b : ℕ∞) ((c + 1 : ℕ) : ℕ∞)) =
        ((min b (c + 1) : ℕ) : ℕ∞) := by rfl
    rw [hm]
    exact_mod_cast h₃

end IsLocalRing
