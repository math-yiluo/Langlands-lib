/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.Continuous.ContinuousCochainsDerivedInvariants

/-!
# Continuous cohomology of discrete profinite modules

Source: the blueprint, chapter `chap-Cohomology-of-torsion-sheaves-on-curves`, unit `sk-prop-h2`,
(blueprint: def-exc-continuous-cohomology); Stacks Project, Tags 04JP, 04JR and 0DVG.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

/-- The functor `H^q(G, -)` on discrete left `A`-modules with continuous `G`-action.
Its value on `M` is the `q`-th right derived functor of invariants, computed using
injective resolutions in the ordinary abelian category `DiscreteContinuousRep A G`.
The category uses open stabilizers and equivariant `A`-linear maps; its abelian structure
and enough injectives come from `discreteModules_abelian`.

The invariant functor is chosen from `continuousCochains_derived_invariants`: its objects
are naturally linearly equivalent to the submodules `⨅ g, ker (ρ g - id)`, precisely
`{m | ∀ g, ρ g m = m}`, and its maps are the restrictions of the coefficient maps.
That same theorem identifies these derived functors naturally with cohomology of the
continuous inhomogeneous cochain complex, with the usual differential and discrete
coefficient topology. Choosing data from that theorem postpones the existence and comparison
proofs, not the definition's data. No finiteness condition is imposed on the modules.

Source: blueprint `sec-curve-estimates/sk-prop-h2/def-exc-continuous-cohomology`;
Stacks Project, Tags 04JP, 04JR and 0DVG (blueprint: def-exc-continuous-cohomology). -/
noncomputable def discreteContinuousCohomologyFunctor
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] (q : ℕ) :
    DiscreteContinuousRep.{v, u, max u w} A G ⥤ ModuleCat.{max u w} A :=
  let h := Classical.choose (discreteModules_abelian.{u, v, max u w} G A)
  letI := h
  letI : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := h.toPreadditive
  letI : Preadditive (ModuleCat.{max u w} A) :=
    (inferInstance : Abelian (ModuleCat.{max u w} A)).toPreadditive
  letI := (Classical.choose_spec
    (discreteModules_abelian.{u, v, max u w} G A)).choose_spec.1
  letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, TopologicalSpace M.obj.V :=
    fun _ ↦ ⊥
  letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, DiscreteTopology M.obj.V :=
    fun _ ↦ ⟨rfl⟩
  letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
      ContinuousConstSMul A M.obj.V :=
    fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
  let comparison := continuousCochains_derived_invariants.{u, v, w} G A
  let V := Classical.choose comparison
  let a := Classical.choose (Classical.choose_spec comparison)
  @Functor.rightDerived _ _ _ _ h _ _ V a q

end Rep
