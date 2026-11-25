/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.RepresentationTheory.HomogeneousCochainEvaluationBijective
import WeilConjectures.RepresentationTheory.HomogeneousCochainEvaluationDifferential

/-!
# Homogeneous and inhomogeneous continuous cochains

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
section-continuous-group-cohomology, displayed differential; homogeneous change of variables.
(blueprint: lem-sc-homogeneous-inhomogeneous-continuous-cohomology).
-/

@[expose] public section

universe u s

open CategoryTheory

namespace Rep

/-- Invariant homogeneous continuous cochains have locally constant inhomogeneous
coordinates, and their recursive differential becomes the usual inhomogeneous differential.

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
section-continuous-group-cohomology, displayed differential; the homogeneous conversion
in the proof of lem-sc-discrete-resolution-continuous-cohomology.
(blueprint: lem-sc-homogeneous-inhomogeneous-continuous-cohomology).

Proof: Use the compact-open exponential law for the compact Hausdorff group G to identify
iterated continuous maps with jointly continuous maps on G^(n+1). Invariants for the
diagonal action are exactly equivariant homogeneous maps. Evaluate such a map at
(1,g1,g1*g2,...,g1*...*gn). Conversely send c to the function taking (g0,...,gn) to
g0 acting on c(g0 inverse*g1,...,g(n-1) inverse*gn). The two maps are inverse by
equivariance and preserve addition. The open-stabilizer hypothesis makes the action
G times N to N continuous: near (g,x), keep the discrete coordinate x fixed and restrict
the group coordinate to the corresponding stabilizer coset. Thus both coordinate
transformations preserve continuity. Maps into the discrete coefficient space are
continuous exactly when locally constant. Uncurry and curry along the exponential law
to return to Mathlib's iterated-map terms. Its recursive differential, constant insertion
minus the preceding differential applied pointwise, expands inductively to alternating
omission. After evaluating at cumulative products, the first omission gives the action
term, internal omissions multiply adjacent arguments, and the last omission drops the
last argument. Their signs are respectively +1 and (-1)^(k+1), exactly as below.
For n=0 this gives g acting on m minus m. No resolution or homology assertion is used. -/
theorem exists_homogeneousCochains_inhomogeneous_coordinates
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : TopRep.{max u s} ℤ G) [DiscreteTopology N.V]
    (hN : ∀ x : N.V, IsOpen {g : G | N.ρ g x = x}) :
    ∃ t : ∀ n : ℕ, (TopRep.homogeneousCochains N).X n ≃+
        LocallyConstant (Fin n → G) N.V,
      ∀ (n : ℕ) (x : (TopRep.homogeneousCochains N).X n) (g : Fin (n + 1) → G),
        t (n + 1) (((TopRep.homogeneousCochains N).d n (n + 1)).hom x) g =
          N.ρ (g 0) (t n x (fun k ↦ g k.succ)) +
            ∑ k : Fin (n + 1),
              (-1 : ℤ) ^ (k.val + 1) • t n x (Fin.contractNth k (· * ·) g) := by
  let t (n : ℕ) := AddEquiv.ofBijective (homogeneousCochainEvaluation N n)
    (homogeneousCochainEvaluation_bijective N hN n)
  refine ⟨t, ?_⟩
  intro n x g
  exact homogeneousCochainEvaluation_differential N n x g

end Rep
