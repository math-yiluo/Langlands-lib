/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.RingTheory.CohenMacaulayFreeResolutionConstruction
import WeilConjectures.RingTheory.CohenMacaulayFreeResolutionMCM

/-!
# Finite free resolutions ending in maximal Cohen–Macaulay modules

Source: Stacks Project, Algebra, Tags 00NG, 00NE, 00NF and 00LK
(blueprint: lem-weil-pbc-cm-local-free-resolution-to-mcm).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace IsLocalRing

/-- Over a Noetherian local Cohen–Macaulay ring of dimension `d`, a nonzero finite module
has depth `e ≤ d` and an exact sequence `0 → K → F_{d-e-1} → ⋯ → F₀ → M → 0`,
with the `Fᵢ` finite free and `K` finite and either zero or of depth `d`.
Source: Stacks Project, Algebra, Tags 00NG, 00NE, 00NF and 00LK
(blueprint: lem-weil-pbc-cm-local-free-resolution-to-mcm).

Proof plan (the seven steps of the node):
1. Tag 00LK (lem-weil-pbc-depth-le-support-dimension) bounds depth by support dimension,
   which is at most `d`; hence depth is a natural number `e ≤ d`.
2. An `R`-regular sequence of length `d` acts componentwise regularly on each nonzero
   finite free module, so such modules have depth at least `d`.
3. Induct on `k = d - e`. At `k = 0`, take `K = M` and the identity map.
4. Choose a finite free surjection onto the module. Its kernel is finite by
   lem-weil-pbc-noetherian-submodule-finite and is nonzero if the module has depth below `d`.
5. Parts (2) and (3) of Tag 00LX (lem-weil-pbc-depth-in-ses) show that this first kernel
   has depth exactly one larger, using the free module's depth bound.
6. Apply the induction hypothesis to the kernel and splice with its inclusion in the
   free module. Surjectivity, the kernel-image equality and injectivity give exactness.
7. This gives the required length `d - e` and the maximal Cohen–Macaulay last kernel.

For `k = d - e`, the objects of `S` in order are `0, K, F_{k-1}, …, F₀, M, 0`.
The linear equivalence identifies its penultimate object with the original `M`, even
when `R` and `M` have different universes. At `k = 0` there are no free terms; exactness
between the zero endpoints makes the map `K → M` an isomorphism. -/
theorem exists_finite_free_resolution_to_maximalCohenMacaulay
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (hcm : (d : ℕ∞) ≤ depth (R := R) R) :
    ∃ e : ℕ, depth (R := R) M = (e : ℕ∞) ∧ e ≤ d ∧
      ∃ S : ComposableArrows (ModuleCat.{max u v} R) (d - e + 3),
        S.Exact ∧ IsZero (S.obj' 0) ∧ IsZero (S.obj' (d - e + 3)) ∧
        Nonempty ((S.obj' (d - e + 2)) ≃ₗ[R] M) ∧
        (∀ i : Fin (d - e),
          Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
          Module.Finite R (S.obj' (i.val + 2) (by omega))) ∧
        (let K := S.obj' 1
         ∃ hK : Module.Finite R K,
           letI := hK
           Subsingleton K ∨ depth (R := R) K = (d : ℕ∞)) := by
  have hbound : (depth (R := R) M : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
    calc
      (depth (R := R) M : WithBot ℕ∞) ≤ Module.supportDim R M := depth_le_supportDim M
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
      _ = (d : WithBot ℕ∞) := hdim
  have hle : depth (R := R) M ≤ (d : ℕ∞) := WithBot.coe_le_coe.mp hbound
  have hfinite : depth (R := R) M ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hle
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hed : e ≤ d := ENat.natCast_le_natCast.mp (he ▸ hle)
  obtain ⟨S, hS, h0, hlast, hM, hfree⟩ :=
    exists_finite_free_resolution_data (R := R) M (d - e)
  refine ⟨e, he.symm, hed, S, hS, h0, hlast, hM, hfree, ?_⟩
  exact first_term_is_maximalCohenMacaulay M d e hdim hcm he.symm hed
    S hS h0 hlast hM hfree

end IsLocalRing
