/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.PointComplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated

/-!

# The open–closed triangle in `Dᵇc(X)`

The open–closed triangle `j_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶` of an open immersion `j` and a closed
immersion `i` onto its complement is distinguished in the triangulated category `Dᵇc(X)` itself
(`ProEtale.CondensedRing.exists_distTriang_openImmersionLowerShriek_lowerStar`), with the
extension by zero `j_!`; in particular for `i = x`, `j = X ∖ {x}`
(`ProEtale.CondensedRing.exists_distTriang_pointComplι_rationalPoint`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The open–closed triangle in `Dᵇc(X)` -/

section Triangle

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X) [IsClosedImmersion i.left]

/-- **The open–closed localization triangle in `Dᵇc(X)`**: for an open immersion `j : U ⟶ X` and
a closed immersion `i : Z ⟶ X` onto its complement, the counit `j_! Lj^* K ⟶ K` of the extension
by zero and the unit `K ⟶ Ri_* Li^* K` of `Li^* ⊣ Ri_*` extend to a distinguished triangle of the
triangulated category `Dᵇc(X)`. The distinguished triangles of the full subcategory are those whose
image in the ambient derived category is distinguished, so this is
`exists_distTriang_openImmersionLowerShriek_openClosed`. -/
theorem exists_distTriang_openImmersionLowerShriek_lowerStar
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ, Triangle.mk
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K)
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) δ ∈
      distTriang (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openImmersionLowerShriek_openClosed j i hcompl K
  obtain ⟨δ₀, rfl⟩ := WeilBoundedConstructible.exists_eq_map_comp_commShiftIso
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).fullyFaithfulι
    δ
  exact ⟨δ₀, hδ⟩

/-- **The open–closed triangle of a rational point**: with `j : X ∖ {x} ⟶ X` the open complement
of a rational point `x`, the triangle `j_! Lj^* K ⟶ K ⟶ Rx_* Lx^* K ⟶` is distinguished in
`Dᵇc(X)`. -/
theorem exists_distTriang_pointComplι_rationalPoint (x : RationalPoint X)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ, Triangle.mk
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
          (pointComplι x)).counit.app K)
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).unit.app K) δ ∈
      distTriang (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  exists_distTriang_openImmersionLowerShriek_lowerStar (pointComplι x) x
    (isCompl_range_pointComplι x) K

end Triangle

end AlgebraicGeometry.ProEtale.CondensedRing
