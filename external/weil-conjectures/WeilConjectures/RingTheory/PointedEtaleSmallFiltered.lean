/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic

import WeilConjectures.RingTheory.PointedEtaleEssentiallySmall
import WeilConjectures.RingTheory.PointedEtaleFiltered

/-!
# Size and filteredness of pointed etale algebras

Source: Stacks Project, Algebra, Tag 04GW.
(blueprint: lem-sc-pointed-etale-small-filtered).
-/

@[expose] public section

universe u
open CategoryTheory
namespace Algebra

/-- The category of etale algebras pointed in the chosen residue separable closure
is essentially small and filtered.
Source: Stacks Project, Algebra, Tag 04GW, proof of
`lemma-strict-henselization-different`.
(blueprint: lem-sc-pointed-etale-small-filtered).

Proof: Identify an object with its etale algebra, the kernel of its map to `K`,
and the induced residue-field embedding. This identifies the category with the
etale residue triples at the maximal ideal. Finite presentation and essential
smallness of the affine etale site give a small set of representatives; the
maps to `K` over each representative form a set. The identity algebra is an
object. Tensor products give common successors. For two parallel maps
`S → S'`, the etale algebra `(S' ⊗[S] S') ⊗[S' ⊗[R] S'] S'` equalizes them;
the compatible maps to `K` extend to this algebra. These are precisely the
nonemptiness, common-successor and equalization conditions for filteredness. -/
theorem pointedEtale_small_filtered
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K] :
    let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
    EssentiallySmall.{u} P.FullSubcategory ∧ IsFiltered P.FullSubcategory := by
  exact ⟨pointedEtale_essentiallySmall R K, pointedEtale_filtered R K⟩

end Algebra
