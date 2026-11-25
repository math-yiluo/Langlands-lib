/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField

/-!
# Lower shriek on bounded constructible complexes under pushforward preservation

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/det-def-sfb-dc-lower-shriek-definition.md, defining composite
and chosen-compactification paragraph
(blueprint: proposition-construction-independence-rf-shriek).

## Main definitions

* `boundedConstructibleLowerShriekOfCompactificationOfPreserves`: restricted extension
  by zero followed by restricted derived pushforward for the specified compactification.
* `boundedConstructibleLowerShriekOfPreserves`: the same construction for the recorded
  chosen compactification `AlgebraicGeometry.compactificationOverField`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (H : PreservesBoundedConstructiblePushforwards Λ k)

/-- The lower shriek attached to the given compactification is `i_! ⋙ Rp_*` on the
bounded constructible full subcategories. Here `c` includes quasi-compactness of the open
immersion, and its canonical middle scheme and both arrows are over `Spec k`.
The coefficient hypothesis is preservation by every derived pushforward in the setting,
with no restriction to the three example coefficient families.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/det-def-sfb-dc-lower-shriek-definition.md, first displayed composite
(blueprint: proposition-construction-independence-rf-shriek). -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationOfPreserves
    {f : X ⟶ Y} (c : Compactification.BoundaryCompactification f.left) :
    ProEtale.BoundedConstructible (condensedRingObj Λ X.left) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ Y.left) :=
  boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.obj.obj.overI ⋙
    boundedConstructibleLowerStarOfPreserves Λ H c.obj.obj.overG

/-- The derived lower shriek is the preceding composite for the chosen compactification
of the dependency `proposition-construction-independence-rf-shriek`. Both factors already take
values in the bounded constructible full subcategories, so this construction needs no further
preservation assertion.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/det-def-sfb-dc-lower-shriek-definition.md, final paragraph
(blueprint: proposition-construction-independence-rf-shriek). -/
noncomputable def boundedConstructibleLowerShriekOfPreserves (f : X ⟶ Y) :
    ProEtale.BoundedConstructible (condensedRingObj Λ X.left) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ Y.left) :=
  letI : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  letI : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  letI : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  letI : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  letI : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  boundedConstructibleLowerShriekOfCompactificationOfPreserves Λ ℓ H
    (AlgebraicGeometry.compactificationOverField k f.left)

end AlgebraicGeometry.ProEtale.CondensedRing
