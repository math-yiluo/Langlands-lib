/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleLocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic

/-! # Uniform upper bound for the discarded lower tail

Source: blueprint `lemma-proper-direct-image-unbounded-complexes` and
`proposition-compactness-proper-direct-image--2` (1)-(2).
(blueprint: lem-sfb-adic-proper-truncation-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ k hΛ

set_option linter.unusedSectionVars false in
/-- The direct image of a sufficiently low lower tail has no cohomology in
degree `q` or above, uniformly on the bounded constructible localizing hull.

Source: blueprint `lemma-proper-direct-image-unbounded-complexes` (arbitrary-complex clause)
and `proposition-compactness-proper-direct-image--2` (1)-(2).
(blueprint: lem-sfb-adic-proper-truncation-bound)

Proof: the schemes and their locally closed strata are Noetherian. The class
of complexes with ind-constructible cohomology is replete, triangulated and
closed under ambient sums, and contains every bounded constructible complex.
The universal property of the localizing hull therefore puts K in this class.
For integral coefficients use the same statement for the integral
ind-constructible heart, proved from the local torsion charts and locally free
resolutions; all colimits remain those of ordinary module sheaves.
Choose a uniform geometric fibre-dimension bound d for g. Proper
finiteness bounds the cohomology of direct images of constructible heart
objects in [0,2d+1]. In the integral case the local torsion charts and free
resolutions put derived torsion reductions in degrees [-1,0]. Their proper
direct images vanish above 2d. Use the Milnor sequence for their
countable derived inverse limit. In the rational cases use the proper heart
bound, and for Qlbar descend to finite coefficient subextensions. Bounded-below
filtered continuity extends the bound to the ind-constructible heart. Finite
truncation triangles then bound the image of a bounded-below ind-constructible
complex with cohomology at most b by b+2d+1. Left completeness reconstructs an
arbitrary complex from its lower truncations. The discarded heart layer between
successive lower truncations has image
bounded above by 2d-n. For a fixed degree r choose n at least
max(0,2d-r+2). Both degree-r and degree-(r-1) towers then have invertible
transitions, so their first derived inverse limits vanish. Above b+2d+1 the
degree-r terms also vanish. The Milnor exact sequence gives
the same upper bound without boundedness below. Apply this to
the lower tail in the triangle τ<q-c K → K → τ≥q-c K, with c=2d+1.
Its image is supported in degrees at most q-1, which is the asserted bound.
The constant c is independent of K
and q, including zero complexes and empty fibres.
-/
theorem ellAdic_proper_lowerTail_bound :
    ∃ c : ℕ, ∀ (q : ℤ)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
        (condensedRingObj Λ Z.left))),
      boundedConstructibleLocalizingClosure Λ Z.left K →
      ((R((g.left)_*⟦Λ⟧)).obj
        ((DerivedCategory.TStructure.t.truncLT (q - (c : ℤ))).obj K)).IsLE (q - 1) := by
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  have hheart : ProperLowerStarHeartHypotheses Λ g.left := by
    cases hΛ with
    | continuous E =>
      exact properLowerStarHeartHypotheses_continuousMapRingObj ℓ E Y.hom g.left
    | integral E =>
      exact properLowerStarHeartHypotheses_padicIntegersRingObj ℓ E Y.hom g.left
    | algebraicClosure =>
      exact properLowerStarHeartHypotheses_padicAlgClRingObj ℓ Y.hom g.left
  obtain ⟨d, hd⟩ := hheart.1
  let P := constructibleCoproductClosure Λ Z.left
  have hclosure : boundedConstructibleLocalizingClosure Λ Z.left ≤
      DerivedCategory.homologyProperty P := by
    apply boundedConstructibleLocalizingClosure_le
    intro K hK n
    exact ObjectProperty.le_weakSerreCoproductClosure _ _ (hK.2 n)
  -- The coarse Milnor bound costs one extra degree, absorbed in the existential constant.
  refine ⟨d.toNat + 1, fun q K hK ↦ ?_⟩
  let a : ℤ := q - ((d.toNat + 1 : ℕ) : ℤ)
  let L := (DerivedCategory.TStructure.t.truncLT a).obj K
  have hL : DerivedCategory.homologyProperty P L :=
    (DerivedCategory.homologyProperty P).prop_of_iso
      ((DerivedCategory.TStructure.t.truncLEIsoTruncLT (a - 1) a (by omega)).app K)
      (DerivedCategory.homologyProperty_truncLE (hclosure K hK) (a - 1))
  have : L.IsLE (a - 1) :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj K a (a - 1) (by omega)
  have hbound : ((R((g.left)_*⟦Λ⟧)).obj L).IsLE (a - 1 + d + 1) := by
    apply DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE
    intro n
    exact DerivedCategory.isLE_obj_of_isLE_of_homologyProperty
      (R((g.left)_*⟦Λ⟧)) d P hd _
      ⟨⟨-(n : ℤ), inferInstance⟩, ⟨a - 1, inferInstance⟩⟩
      (DerivedCategory.homologyProperty_truncGE hL _) (a - 1)
  exact DerivedCategory.TStructure.t.isLE_of_le
    ((R((g.left)_*⟦Λ⟧)).obj L) (a - 1 + d + 1) (q - 1) (by dsimp [a]; omega)

end AlgebraicGeometry.ProEtale.CondensedRing
