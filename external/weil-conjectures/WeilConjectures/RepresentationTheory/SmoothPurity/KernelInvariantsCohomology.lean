/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.RepresentationTheory.SmoothPurity.DiscreteContinuousCohomology
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Data.Int.GCD
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
/-!
# Exact kernel invariants and comparison of continuous cohomology

Source: blueprint main-20261015, `lem-exc-dvr-galois.proof.md`, third paragraph;
DAG proof steps 3--5 of `lem-exc-dvr-galois`.
(blueprint: lem-exc-kernel-invariants-cohomology)
-/

@[expose] public section
set_option autoImplicit false
universe u v w z
open CategoryTheory
namespace Rep
variable {A : Type v} [Ring A]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {B : Type z} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]

section Exactness
set_option linter.style.haveILetI false
variable {B₀ : Type} [Group B₀] [TopologicalSpace B₀] [IsTopologicalGroup B₀]
variable [Finite A] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable [CompactSpace B₀] [T2Space B₀] [TotallyDisconnectedSpace B₀]

end Exactness

end Rep
