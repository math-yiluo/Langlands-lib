/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent

/-!
# Profinite connected-component quotient of a spectral space

Source: Stacks Project, `topology.tex`, Tag 0906, lemma-spectral-pi0
(blueprint: lem-pe-spectral-components-profinite).
-/

@[expose] public section

universe u

open Topology

/-- The connected-component quotient of a spectral space is compact Hausdorff and totally
disconnected, hence profinite in the topological sense.

Source: Stacks Project, `topology.tex`, Tag 0906, lemma-spectral-pi0
(blueprint: lem-pe-spectral-components-profinite).

Proof for stage 3.  Write `q : T → ConnectedComponents T` for the surjective quotient map.
1. Spectrality supplies compactness (`def-weil-spectral-space`). Pull an open cover back
along `q`, take a finite subcover of `T`, and use surjectivity to obtain a finite subcover
of the quotient.
2. For distinct quotient points choose representatives `x, y` in different components.
Spectrality supplies the compact-open basis and quasi-separatedness as well as compactness.
The intersection formula of `lem-weil-pbc-quasicompact-components-clopen-intersection`,
recorded as `sInter_isClopen_and_mem_eq_connectedComponent`, gives a clopen `U` containing
`x` and excluding `y`. A component meeting `U` lies wholly in `U`, since otherwise `U` and
its complement would disconnect it. Thus `U` is saturated for `q`. The inverse images of
`q(U)` and its complement are `U` and its complement, so the quotient topology makes these
two disjoint neighbourhoods open. They separate the given points and establish Hausdorffness.
3. A connected subset containing distinct quotient points would be separated by the
complementary clopens from step 2, a contradiction. Hence every connected subset has at most
one point. Together the three properties say that the quotient is profinite. -/
theorem spectralSpace_connectedComponents_profinite
    {T : Type u} [TopologicalSpace T] [SpectralSpace T] :
    CompactSpace (ConnectedComponents T) ∧
      T2Space (ConnectedComponents T) ∧
        TotallyDisconnectedSpace (ConnectedComponents T) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end
