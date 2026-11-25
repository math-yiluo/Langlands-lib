/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberDiagram
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.RingTheory.ColimitEventuallyFlat
import WeilConjectures.RingTheory.FlatSemilinearEquiv

@[expose] public section

universe u v w t
open scoped TensorProduct
namespace Module

/-- Existence of one fibre-flat stage in a Noetherian local model tower.
Source: Stacks Project, Algebra, proof of Tag 00R7, second paragraph.
The proof constructs the quotient directed systems, identifies their colimits with the
closed fibre, and applies `RingTheory.exists_flat_stage`.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-flat-stage) -/
theorem NoetherianLocalModelTower.exists_fiberFlat_stage
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M)
    (h_fibre : Module.Flat
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M)) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    ∃ i : X.ι, Module.Flat
      (X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
        (IsLocalRing.maximalIdeal (X.R₀ i)))
      ((X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
        (IsLocalRing.maximalIdeal (X.R₀ i))) ⊗[X.S₀ i] X.N₀ i) := by
  classical
  let := X.preorder
  let := X.nonempty
  let := X.directed
  let := X.commR
  let := X.commS
  let := X.localR
  let := X.algRS
  let := X.addN
  let := X.moduleS
  obtain ⟨A, B, D, act, φ, ψ, limitAct, hdata⟩ := X.exists_fiber_diagram
  let := act
  let := limitAct
  rcases hdata with
    ⟨hlocalA, hlocalB, hnoethA, hnoethB, hfinite, hφ, hA, hB, hcomm,
      hscalar, hψ, hlimitScalar, hloc, hbase, hstage, hlimit⟩
  let := hlocalA
  let := hlocalB
  let := hnoethA
  let := hnoethB
  let := hfinite
  obtain ⟨eA, eD, he⟩ := hlimit
  have hflat : let := Module.compHom (CategoryTheory.Limits.colimit D : AddCommGrpCat) ψ
      Module.Flat (CategoryTheory.Limits.colimit A : CommRingCat)
        (CategoryTheory.Limits.colimit D : AddCommGrpCat) := by
    let := Module.compHom (CategoryTheory.Limits.colimit D : AddCommGrpCat) ψ
    exact (Module.Flat.semilinearEquiv_iff eA eD he).mpr h_fibre
  obtain ⟨i, hi⟩ := RingTheory.exists_flat_stage A B D φ hφ hA hB hcomm
    hscalar ψ hψ hlimitScalar hloc hbase hflat
  obtain ⟨eAi, eDi, hei⟩ := hstage i
  refine ⟨i, ?_⟩
  let := Module.compHom (D.obj i) (φ i)
  exact (Module.Flat.semilinearEquiv_iff eAi eDi hei).mp hi

end Module
