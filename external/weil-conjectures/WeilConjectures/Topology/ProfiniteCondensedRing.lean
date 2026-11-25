/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing

/-!
# Arbitrary condensed rings in the profinite-site universe convention

Source: the blueprint, condensed rings and the tensor-abelian ring-object convention;
Hemo--Richarz--Scholbach, Section 3 (blueprint: sk-def-sfb-condensed-ring).

The existing continuous-function, adic and subfield constructions are publicly reexported.
The abbreviation also admits condensed rings not presented by a topological ring.
-/

@[expose] public section

universe u

open CategoryTheory

namespace Profinite

/-- A condensed ring is a ring object of abelian sheaves on the coherent profinite site,
equivalently a sheaf of rings. Multiplication is tensor multiplication, with integer unit.
The public imports retain the existing continuous-function sheaves, continuous-map
postcomposition, adic rings, subfields and valuation subrings. This abbreviation adds
only the general input type that those constructions inhabit.
Source: blueprint condensed rings; HRS Section 3 (blueprint: sk-def-sfb-condensed-ring). -/
abbrev CondensedRing : Type (u + 2) := Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

end Profinite
