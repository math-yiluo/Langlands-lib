/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.DiscreteContinuousRep
public import WeilConjectures.RepresentationTheory.DiscreteInvariantsContinuousComparison

/-!
# Cohomology of discrete modules by continuous cochains

For a profinite group `G` and a discrete `G`-module `M`, the cohomology
`DiscreteModule.H G M n = Extⁿ(ℤ, M)` is computed by continuous homogeneous cochains: it is
the continuous cohomology `continuousCohomology n N` of any discrete topological
representation `N` identified equivariantly with `M`.

Source: Stacks Project, Etale Cohomology, Section 0DVG.
-/

@[expose] public section

universe w u t

open CategoryTheory

namespace DiscreteModule

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- **Continuous cohomology of discrete modules.** For a profinite group `G`, a discrete
`G`-module `M` and a discrete topological representation `N` of `G` together with an
equivariant additive equivalence `e : M ≃+ N`, this is the additive equivalence
`Hⁿ(G, M) ≃+ Hⁿ_cont(G, N)` between `Extⁿ(ℤ, M)` in discrete `G`-modules and the cohomology of
continuous homogeneous cochains with values in `N`. It is the composite of
`DiscreteModule.hAddEquivRightDerivedInvariants` and
`Rep.rightDerivedAddEquivContinuousCohomology`, applied through the equivalence
`DiscreteModule.discreteContinuousRepEquivalence`. -/
noncomputable def hAddEquivContinuousCohomology (M : DiscreteModule.{w} G)
    (N : TopRep.{max u t} ℤ G) [DiscreteTopology N.V] (e : M.obj.V ≃+ N.V)
    (he : ∀ (g : G) (x : M.obj.V), e ((M.obj.ρ g).asHom.hom x) = N.ρ g (e x)) (n : ℕ) :
    H G M n ≃+ continuousCohomology n N :=
  (hAddEquivRightDerivedInvariants G M n).trans <|
    Rep.rightDerivedAddEquivContinuousCohomology G (DiscreteModule.{w} G)
      (discreteContinuousRepEquivalence G) (invariants G)
      (toDiscreteContinuousRepCompInvariantsIso G).symm M N e.toIntLinearEquiv he n

end DiscreteModule
