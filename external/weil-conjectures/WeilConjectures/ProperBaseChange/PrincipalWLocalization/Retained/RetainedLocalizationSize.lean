/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.Retained.ThmPeIndetaleRefinementPart2Supplement3
public import Mathlib.SetTheory.Cardinal.Basic

/-! # Cardinality of retained localization

Source: Stacks Project, Tag 0984 (blueprint: lem-weil-pbc-retained-localization-size).
-/

@[expose] public section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization.Retained

/-- Retained localization is a quotient of the principal w-localization, hence no larger.
Source: Stacks Project, Tag 0984 (blueprint: lem-weil-pbc-retained-localization-size).

Proof: every selector is idempotent. The map to its principal localization is therefore
surjective. Every element of the filtered colimit comes from one such localization. Lift it
to the base ring and use that the colimit inclusion is an algebra homomorphism to identify
its image with the structural map from the base. This proves surjectivity of that map;
cardinality decreases under surjections. This includes the empty closed subset and the
empty spectrum, since the localization and filtered-colimit arguments require neither
to be nonempty. -/
theorem cardinalMk_le (R : Type u) [CommRing R]
    (T : Set (PrimeSpectrum R)) (hT : IsClosed T) :
    #(algebra T hT) ≤ #(PrincipalWLocalization.algebra R) := by
  apply mk_le_of_surjective (f := algebraMap (PrincipalWLocalization.algebra R) (algebra T hT))
  intro x
  obtain ⟨E, y, hy⟩ := Concrete.colimit_exists_rep (localizationDiagram T) x
  obtain ⟨r, hr⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
    (S := Localization.Away (selector E.val E.property.1)) _
    (selector_idempotent E.val E.property.1) y
  refine ⟨r, ?_⟩
  rw [← hy, ← hr]
  exact ((colimit.ι (localizationDiagram T) E).hom.commutes r).symm

end PrincipalWLocalization.Retained
