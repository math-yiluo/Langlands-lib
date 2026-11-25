/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.FreePrimeMembership
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Localization.Module

/-! # Prime membership in a finite projective module is detected at the prime localization

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00NX
(blueprint: lem-sc-affine-finite-projective-prime-membership)
-/

@[expose] public section

universe u v
namespace Module

/-- Prime membership in a finite projective module is detected at the prime localization.

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00NX
(blueprint: lem-sc-affine-finite-projective-prime-membership)
Here `R_p = Localization.AtPrime p` [def-weil-pbc-localization-at-prime] and
`N_p = LocalizedModule p.primeCompl N` [def-weil-pbc-module-localization]; `pN_p` is the
extension of `p` to `R_p` acting on `N_p`, and `pN` is `p • ⊤`.
Proof. Step 1: since `N` is finite, choose a surjection `π : R^n → N`; the lifting clause
of [def-weil-pbc-projective-module] lifts `id_N` along `π`, giving `i : N → R^n` with
`π ∘ i = id_N`. Mathlib's `Finite.exists_comp_eq_id_of_projective` supplies these maps.
Localizing `i` at `p` [def-weil-pbc-module-localization] and extending scalars gives
an `R_p`-linear map `i_p` sending `s/1` to `i(s)/1`.
Step 2: if `s/1 ∈ pN_p`, applying `i_p` gives
`i(s)/1 ∈ p(R^n)_p`; by [lem-sc-free-prime-membership] `i(s) ∈ pR^n`, and applying `π`
gives `s = π(i(s)) ∈ pN`. Conversely, if `s ∈ pN`, the canonical localization map sends
this relation to `s/1 ∈ pN_p`.
-/
theorem prime_mem_localized_iff
    {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (s : N) (p : Ideal R) [p.IsPrime] :
    LocalizedModule.mk s 1 ∈
        (Ideal.map (algebraMap R (Localization.AtPrime p)) p) •
          (⊤ : Submodule (Localization.AtPrime p) (LocalizedModule p.primeCompl N)) ↔
      s ∈ p • (⊤ : Submodule R N) := by
  obtain ⟨n, π, i, _, _, hπ⟩ := Finite.exists_comp_eq_id_of_projective R N
  let iₚ := (IsLocalizedModule.map p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl N)
    (LocalizedModule.mkLinearMap p.primeCompl (Fin n → R)) i).extendScalarsOfIsLocalization
      p.primeCompl (Localization.AtPrime p)
  constructor
  · intro hs
    have hi := Submodule.smul_top_le_comap_smul_top
      (Ideal.map (algebraMap R (Localization.AtPrime p)) p) iₚ hs
    have his : LocalizedModule.mkLinearMap p.primeCompl (Fin n → R) (i s) ∈
        (Ideal.map (algebraMap R (Localization.AtPrime p)) p) •
          (⊤ : Submodule (Localization.AtPrime p)
            (LocalizedModule p.primeCompl (Fin n → R))) := by
      simpa [iₚ, LocalizedModule.mkLinearMap_apply,
        IsLocalizedModule.map_LocalizedModules] using hi
    have hfree := (free_prime_mem_localized_iff n (i s) p).1.mp his
    have hmem := Submodule.smul_top_le_comap_smul_top p π hfree
    simpa only [Submodule.mem_comap, ← LinearMap.comp_apply, hπ,
      LinearMap.id_apply] using hmem
  · intro hs
    change LocalizedModule.mkLinearMap p.primeCompl N s ∈ _
    refine Submodule.smul_induction_on hs ?_ ?_
    · intro r hr x _
      rw [map_smul]
      simpa only [algebraMap_smul] using
        (Submodule.smul_mem_smul
          (Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) hr)
          (Submodule.mem_top (x := LocalizedModule.mkLinearMap p.primeCompl N x)))
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy

end Module
