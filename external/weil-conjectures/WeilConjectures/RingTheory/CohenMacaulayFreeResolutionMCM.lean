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
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.CohenMacaulayDepthFirstTerm

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits

namespace IsLocalRing

/-- The left term of a prescribed finite free sequence is zero or maximal
Cohen--Macaulay when its length is the ring dimension minus the depth of `M`.
Source: Stacks Project, Algebra, Tags 00NG, 00NE and 00LX, with the depth bound 00LK
(blueprint: lem-weil-pbc-cm-local-free-resolution-mcm).

Proof: Read the exact sequence from right to left as short exact sequences
`0 → N_{j+1} → F_j → N_j → 0`, with `N_0` identified with `M` and
`N_{d-e}` identified with its left term `K`. Every `N_j` is finite: `N_0` is finite
by hypothesis and each next kernel is a submodule of a finite free module over a
Noetherian ring. Every nonzero finite free module has depth at least `d`: a regular
sequence on `R` acts componentwise regularly on `R^n`, so its lengths give the same
lower bound for a free module. Transport by a finite basis preserves regularity.
Tag 00LK also bounds the depth of any nonzero finite module by `dim R = d`.

Inductively show that a nonzero `N_j` has depth at least `min(d, e+j)`.
When all three modules of a short exact sequence are nonzero, part (3) of Tag 00LX
bounds the next kernel's depth below by `min(depth F_j, depth N_j + 1)`.
If the quotient `N_j` is zero, the next kernel is isomorphic to `F_j`, so the bound
follows from freeness. If `F_j` is zero, its submodule `N_{j+1}` is zero. A zero next
kernel already satisfies the alternative in the conclusion. These cases also allow
continuing the induction after a zero intermediate syzygy. At `j = d-e`, the lower
bound is `d` because `e ≤ d`; the upper bound for a nonzero `K` gives equality.
At length zero, exactness with zero endpoints identifies `K` with `M`, and `e = d`
gives the conclusion directly. All isomorphisms used preserve regular sequences and
therefore depth. -/
theorem first_term_is_maximalCohenMacaulay
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d e : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (hcm : (d : ℕ∞) ≤ depth (R := R) R)
    (he : depth (R := R) M = (e : ℕ∞)) (hed : e ≤ d)
    (S : ComposableArrows (ModuleCat.{max u v} R) (d - e + 3))
    (hS : S.Exact) (hzero0 : IsZero (S.obj' 0))
    (hzero1 : IsZero (S.obj' (d - e + 3)))
    (hM : Nonempty ((S.obj' (d - e + 2)) ≃ₗ[R] M))
    (hfree : ∀ i : Fin (d - e),
      Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
      Module.Finite R (S.obj' (i.val + 2) (by omega))) :
    (let K := S.obj' 1
     ∃ hK : Module.Finite R K,
       letI := hK
       Subsingleton K ∨ depth (R := R) K = (d : ℕ∞)) := by
  dsimp
  have h1 : 1 ≤ d - e + 3 := by omega
  have hfinite2 : Module.Finite R (S.obj' 2) := by
    by_cases hn : d - e = 0
    · obtain ⟨a⟩ := hM
      have hfinite := Module.Finite.equiv a.symm
      have hobj : S.obj' (d - e + 2) = S.obj' 2 := by
        congr 1
        omega
      rw [hobj] at hfinite
      exact hfinite
    · exact (hfree ⟨0, by omega⟩).2
  have hmono : Mono (S.map' 1 2) :=
    (hS.exact 0).mono_g (hzero0.eq_of_src _ _)
  have hK : Module.Finite R (S.obj' 1) :=
    Module.Finite.of_injective (S.map' 1 2).hom
      ((ModuleCat.mono_iff_injective _).mp hmono)
  refine ⟨hK, ?_⟩
  rcases subsingleton_or_nontrivial (S.obj' 1) with hzero | hnonzero
  · exact Or.inl hzero
  · have hlower := first_term_depth_ge M d e hcm he hed S hS hzero0 hzero1 hM hfree
    have hupper : (depth (R := R) (S.obj' 1 h1) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      calc
        _ ≤ Module.supportDim R (S.obj' 1 h1) := depth_le_supportDim (S.obj' 1 h1)
        _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R (S.obj' 1 h1)
        _ = _ := hdim
    exact Or.inr (le_antisymm (WithBot.coe_le_coe.mp hupper) hlower)

end IsLocalRing
