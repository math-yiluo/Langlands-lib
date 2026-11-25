/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.RingTheory.DepthInSES
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Nakayama

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits

namespace IsLocalRing

private theorem depth_equiv_local {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    {B : Type*} [AddCommGroup B] [Module R B] [Module.Finite R B]
    (e : A ≃ₗ[R] B) : depth (R := R) A = depth (R := R) B := by
  have hmap : (maximalIdeal R • (⊤ : Submodule R A)).map e.toLinearMap =
      maximalIdeal R • (⊤ : Submodule R B) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]
  have htop : (maximalIdeal R • (⊤ : Submodule R A) = ⊤) ↔
      (maximalIdeal R • (⊤ : Submodule R B) = ⊤) := by
    constructor
    · intro h
      rw [← hmap, h]
      simp
    · intro h
      rw [← hmap] at h
      exact Submodule.map_eq_top_iff.mp h
  unfold depth Ideal.depth
  split_ifs with hA hB hB
  · rfl
  · exact (hB (htop.mp hA)).elim
  · exact (hA (htop.mpr hB)).elim
  · congr 1
    ext n
    constructor
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mp hreg, hmem, rfl⟩
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mpr hreg, hmem, rfl⟩

private theorem depth_subsingleton {R : Type u} [CommRing R] [IsLocalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [Subsingleton A] :
    depth (R := R) A = ⊤ := by
  unfold depth Ideal.depth
  have ht : maximalIdeal R • (⊤ : Submodule R A) = ⊤ := Subsingleton.elim _ _
  rw [ite_eq_left ht]

private theorem depth_free_ge {R : Type u} [CommRing R] [IsLocalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Free R A] :
    depth (R := R) R ≤ depth (R := R) A := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl h =>
    let := h
    rw [depth_subsingleton A]
    exact le_top
  | inr h =>
    let := h
    let ι := Module.Free.ChooseBasisIndex R A
    let e : A ≃ₗ[R] (ι → R) := (Module.Free.chooseBasis R A).equivFun
    rw [depth_equiv_local e]
    have ht : maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ :=
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (maximalIdeal_le_jacobson (Module.annihilator R R))).symm
    unfold depth Ideal.depth
    rw [ite_eq_right ht]
    split_ifs with hP
    · exact le_top
    · apply sSup_le
      rintro n ⟨rs, hr, hm, rfl⟩
      apply le_sSup
      refine ⟨rs, ?_, hm, rfl⟩
      apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal (ι → R) hm
      exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff
        (ι → R) (ι → R) rs).mp (hr.1.of_flat (S := ι → R))

private theorem depth_kernel_ge {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    {B C : Type*} [AddCommGroup B] [Module R B] [Module.Finite R B]
    [AddCommGroup C] [Module R C] (g : B →ₗ[R] C) :
    min (depth (R := R) B) (depth (R := R) (LinearMap.range g) + 1) ≤
      depth (R := R) (LinearMap.ker g) := by
  classical
  let f := (LinearMap.ker g).subtype
  let q := g.rangeRestrict
  have hf : Function.Injective f := Subtype.val_injective
  have hq : Function.Surjective q := LinearMap.range_eq_top.mp g.range_rangeRestrict
  have hex : Function.Exact f q := by
    rw [LinearMap.exact_iff]
    simp [f, q]
  cases subsingleton_or_nontrivial (LinearMap.ker g) with
  | inl h =>
    let := h
    rw [depth_subsingleton (LinearMap.ker g)]
    exact le_top
  | inr h =>
    let := h
    cases subsingleton_or_nontrivial B with
    | inl h =>
      let := h
      have : Subsingleton (LinearMap.ker g) := hf.subsingleton
      exact (not_subsingleton (LinearMap.ker g) this).elim
    | inr h =>
      let := h
      cases subsingleton_or_nontrivial (LinearMap.range g) with
      | inl h =>
        let := h
        have hs : Function.Surjective f := by
          intro b
          exact (hex b).mp (Subsingleton.elim _ _)
        let e := LinearEquiv.ofBijective f ⟨hf, hs⟩
        rw [depth_equiv_local e]
        exact min_le_left _ _
      | inr h =>
        let := h
        exact (depth_in_short_exact f q hf hex hq).2.2

/-- The nonzero finite left term of the prescribed free sequence has depth at least `d`.
Source: Stacks Project, Algebra, Tags 00NG, 00NE and 00LX, part (3).
(blueprint: lem-weil-pbc-cm-local-free-resolution-mcm-depth).

Proof: Put `n = d-e`. Read the sequence right to left as short exact sequences
`0 → N_{j+1} → F_j → N_j → 0`, with `N_0` identified with `M` and `N_n` with
`S.obj' 1`. All syzygies are finite: each is a submodule of a finite free module
and the ring is Noetherian. A nonzero finite free module has depth at least `d`:
a regular sequence on `R` acts regularly componentwise on a finite power of `R`;
a finite basis transports this fact, so taking suprema gives depth at least
`depth R`. Linear equivalences preserve depth because they preserve regularity
and the quotient by the maximal ideal.

Induct on `j` to show that any nonzero `N_j` has depth at least `min(d,e+j)`.
The initial bound is `he`. If the three terms are nonzero, part (3) of the depth
lemma gives `depth N_{j+1} ≥ min(depth F_j, depth N_j + 1)`, hence the next bound.
If `N_j` is zero, exactness identifies `N_{j+1}` with `F_j`, giving the bound by
freeness. If `F_j` is zero, injectivity makes `N_{j+1}` zero, so there is no bound
to prove at that step. If `N_{j+1}` is zero the induction assertion is vacuous;
the next step is covered by the zero-quotient case. Thus zero intermediate terms
do not interrupt induction. At `j=n`, `e≤d` gives `min(d,e+n)=d`; the assumed
nontriviality of the left term gives the desired bound. When `n=0`, endpoint
exactness identifies the left term with `M` and `he`, with `e=d`, proves it. -/
theorem first_term_depth_ge
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d e : ℕ)
    (hcm : (d : ℕ∞) ≤ depth (R := R) R)
    (he : depth (R := R) M = (e : ℕ∞)) (hed : e ≤ d)
    (S : ComposableArrows (ModuleCat.{max u v} R) (d - e + 3))
    (hS : S.Exact) (hzero0 : IsZero (S.obj' 0))
    (hzero1 : IsZero (S.obj' (d - e + 3)))
    (hM : Nonempty ((S.obj' (d - e + 2)) ≃ₗ[R] M))
    (hfree : ∀ i : Fin (d - e),
      Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
      Module.Finite R (S.obj' (i.val + 2) (by omega)))
    [Module.Finite R (S.obj' 1)] [Nontrivial (S.obj' 1)] :
    (d : ℕ∞) ≤ depth (R := R) (S.obj' 1) := by
  classical
  let n := d - e
  obtain ⟨eM⟩ := hM
  have hfin (i : ℕ) (hlo : 1 ≤ i) (hi : i ≤ n + 2) :
      Module.Finite R (S.obj' i (by omega)) := by
    by_cases h1 : i = 1
    · subst i
      infer_instance
    by_cases hlast : i = n + 2
    · subst i
      exact Module.Finite.equiv eM.symm
    have hidx : i - 2 < d - e := by dsimp [n] at hi hlast; omega
    have hobj : i - 2 + 2 = i := by omega
    let := (hfree ⟨i - 2, hidx⟩).2
    have ho : S.obj' (i - 2 + 2) (by omega) = S.obj' i (by omega) :=
      congrArg S.obj (Fin.ext hobj)
    exact Module.Finite.equiv (eqToIso ho).toLinearEquiv
  let f (i : ℕ) (hi : i + 1 ≤ n + 3) := (S.map' i (i + 1) (by omega)).hom
  -- Images are the syzygies, indexed from left to right.
  have hrangefin (i : ℕ) (hlo : 1 ≤ i) (hi : i ≤ n + 1) :
      Module.Finite R (LinearMap.range (f i (show i + 1 ≤ n + 3 by omega))) := by
    let := hfin i hlo (by omega)
    exact Module.Finite.of_surjective (f i (show i + 1 ≤ n + 3 by omega)).rangeRestrict
      (LinearMap.range_eq_top.mp (f i (show i + 1 ≤ n + 3 by omega)).range_rangeRestrict)
  have hsurj : Function.Surjective (f (n + 1) (by omega)) := by
    have hz : S.map' (n + 2) (n + 3) (by omega) = 0 := hzero1.eq_of_tgt _ _
    have := (hS.exact (n + 1) (by omega)).epi_f hz
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  let := hfin (n + 1) (by omega) (by omega)
  have hbase : depth (R := R) (LinearMap.range (f (n + 1) (by omega))) = (e : ℕ∞) := by
    let := hrangefin (n + 1) (by omega) (by omega)
    let := hfin (n + 2) (by omega) (by omega)
    let eLast : LinearMap.range (f (n + 1) (by omega)) ≃ₗ[R] S.obj' (n + 2) :=
      LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hsurj)
    exact (depth_equiv_local (eLast.trans eM)).trans he
  -- Move leftward, gaining one unit of depth until the ring bound is reached.
  have hind (i : ℕ) (hi : i ≤ n + 1) (hlo : 1 ≤ i) :
      let := hrangefin i hlo hi
      ((min d (e + (n + 1 - i)) : ℕ) : ℕ∞) ≤
        depth (R := R) (LinearMap.range (f i (show i + 1 ≤ n + 3 by omega))) := by
    induction hi using Nat.decreasingInduction with
    | self =>
      simp only [Nat.sub_self, Nat.add_zero, Nat.min_eq_right hed, hbase, le_refl]
    | of_succ i hi ih =>
      have hidx : i - 1 < d - e := by dsimp [n] at hi; omega
      have heq : i - 1 + 2 = i + 1 := by omega
      let := hfin (i + 1) (by omega) (by omega)
      let : Module.Free R (S.obj' (i + 1) (by omega)) := by
        let := (hfree ⟨i - 1, hidx⟩).1
        have ho : S.obj' (i - 1 + 2) (by omega) = S.obj' (i + 1) (by omega) :=
          congrArg S.obj (Fin.ext heq)
        exact Module.Free.of_equiv (eqToIso ho).toLinearEquiv
      let := hrangefin (i + 1) (by omega) (by omega)
      let := hrangefin i hlo (by omega)
      have hk : LinearMap.range (f i (show i + 1 ≤ n + 3 by omega)) =
          LinearMap.ker (f (i + 1) (show i + 1 + 1 ≤ n + 3 by omega)) := by
        have hex := hS.exact i (show i + 2 ≤ d - e + 3 by dsimp [n] at hi; omega)
        exact hex.moduleCat_range_eq_ker
      have hd := hcm.trans (depth_free_ge
        (S.obj' (i + 1) (show i + 1 ≤ d - e + 3 by dsimp [n] at hi; omega)))
      have hstep := depth_kernel_ge (f (i + 1) (show i + 1 + 1 ≤ n + 3 by omega))
      have htrans : depth (R := R) (LinearMap.ker (f (i + 1) (show i + 1 + 1 ≤ n + 3 by omega))) =
          depth (R := R) (LinearMap.range (f i (show i + 1 ≤ n + 3 by omega))) :=
        depth_equiv_local (LinearEquiv.ofEq _ _ hk.symm)
      rw [htrans] at hstep
      apply le_trans ?_ hstep
      apply le_min
      · exact le_trans (by exact_mod_cast Nat.min_le_left d (e + (n + 1 - i))) hd
      · have ha := add_le_add (ih (by omega)) (le_refl (1 : ℕ∞))
        apply le_trans ?_ ha
        exact_mod_cast (show min d (e + (n + 1 - i)) ≤
          min d (e + (n + 1 - (i + 1))) + 1 by omega)
  let := hrangefin 1 (by omega) (by omega)
  have hinj : Function.Injective (f 1 (show 1 + 1 ≤ n + 3 by omega)) := by
    have hz : S.map' 0 1 = 0 := hzero0.eq_of_src _ _
    have := (hS.exact 0).mono_g hz
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have hresult := hind 1 (by omega) (by omega)
  have hmin : min d (e + (n + 1 - 1)) = d := by dsimp [n]; omega
  rw [hmin] at hresult
  exact hresult.trans_eq
    (depth_equiv_local (LinearEquiv.ofInjective (f 1 (show 1 + 1 ≤ n + 3 by omega)) hinj)).symm

end IsLocalRing
