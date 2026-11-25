/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralNormalizationPreservation
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralUniformBounds
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralCoordinateOrigin
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralOriginAdjunctionRestriction

/-! # Normalized exceptional system adjunction
Source: Zheng, Section 5; integral reconstruction, step 2.
(blueprint: lem-sf-exceptional-integral-normalized-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived AlgebraicGeometry.strictEtaleLevelDerived

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralReconstruction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Restrict the specified system adjunction to the normalized finite-Tor systems.
Source: Zheng, Lemma 5.22 and Proposition 5.24; integral reconstruction, step 2.
(blueprint: lem-sf-exceptional-integral-normalized-adjunction).

Proof: the proper factor of c is finite type and quasi-compact, so its middle
scheme is finite type over the base field. Noetherianity makes the open factor
quasi-compact. The finite exceptional operations give common cohomological and
Tor interval enlargements for both functors. The site evaluation comparisons
identify these finite operations with the evaluated system functors in the
coordinate equivalence. Thus both outputs have LevelBounds. Constructible
pro-etale origin at each finite level, together with the common lower bound on
the whole strict system, supplies the origin assertions at X and Y.

For the right functor, use the normalization assertion in the specified transport,
and the quotient-coordinate equivalence, to retain every transition adjunct.
For the left functor write a normalized input as the reduction of its inverse
under rX. Integral compact support has the prescribed finite reductions,
compatibly with successive quotients. The transition adjunct of the output is
therefore a composite of these reduction comparisons and canonical derived
base-change isomorphisms, hence invertible. Naturality transports the conclusion
back along the reconstruction counit, so no witness of origin is added to the
normalized predicate.

Finally restrict the origin adjunction of s.transport along the full normalized
subcategories, after conjugating by the two coordinate equivalences. The Hom
bijection first applies the inverse coordinate counit at the target, then the
specified origin Hom bijection, then the source coordinate equivalence. Its
transpose equation is exactly the recorded equation with the source site counit
and the coordinate counit displayed in SystemAdjunction.transpose. The inverse
Hom chain proves the two triangle identities. The zero input uses the same
adjunction and [0,0] bounds; identity and empty compactifications require no
extra separatedness assumption. -/
theorem exceptionalIntegralNormalizedAdjunction
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (rX : Reconstruction l E X) (s : Systems l E c) :
    Nonempty (SystemAdjunction l E c s) := by
  obtain ⟨hnL, hnR⟩ := exceptionalIntegralNormalizationPreservation l E D hl c s rX
  obtain ⟨hbL, hbR⟩ := exceptionalIntegralUniformBounds l E D hl c s
  exact exceptionalIntegralOriginAdjunctionRestriction l E c s
    (fun N hN ↦ ⟨hnL N hN, hbL N hN⟩)
    (fun N hN ↦ ⟨hnR N hN, hbR N hN⟩)
    (fun N hN ↦ exceptionalIntegralCoordinateOrigin l E X s.ordinary.PX s.siteX N hN.2)
    (fun N hN ↦ exceptionalIntegralCoordinateOrigin l E Y s.ordinary.PY s.siteY N hN.2)

end WeilConjectures.ExceptionalIntegralReconstruction
