/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentSpecialFibre

/-!

# Topological invariance on the special fibre of a component

Let `c` be contracting at `y`, `F` a fixed locus of `c` and `j : B ⟶ F` with a rational point `b`
of `B` over `y`, such that `B ⊂ F ⊂ C` is a closed immersion. The factorization
`r : B'' ⟶ F'` (`ProEtale.CondensedRing.Correspondence.IsContractingAt.componentSpecialLift`) of
the special fibre of `componentModelHom` through the special fixed locus is a finite universal
homeomorphism, so by topological invariance the unit of `L r^* ⊣ R r_*` is an isomorphism
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.isIso_unit_componentSpecialLift`).

## Implementation notes

This theorem has its own module, which no other module needs. Writing the `.olean` of a module
runs Lean's library-suggestion extensions (`symbolFrequency`, `sineQuaNon`) over the statement of
every theorem, at a cost proportional to the unshared size of the statement. This statement stays
small because the specialized correspondence is stated over the named complex
`Correspondence.specialComplex` rather than `(specialization …).obj K`, which would otherwise be
repeated inside every `Dᵇc` of the statement.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [Algebra k k']
  {F : c.FixedLocus} {B : Over (Spec (.of k))} (j : B ⟶ F.F) {b : RationalPoint B}
  (hb : b ≫ j ≫ F.ι = y) [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Topological invariance on the special fibre of a component**: if `B ⊂ F ⊂ C` is a closed
immersion, the factorization `r : B'' ⟶ F'` of `b''` through the special fixed locus is a finite
universal homeomorphism, so the unit `𝟭 ⟶ Lr^* ⋙ Rr_*` of `Lr^* ⊣ Rr_*` is an isomorphism and
`Lr^* : Dᵇc(F') ⥤ Dᵇc(B'')` is an equivalence. -/
theorem isIso_unit_componentSpecialLift [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated B.hom] [IsClosedImmersion (j ≫ F.ι).left] :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (hc.componentSpecialLift k' j hb)).unit :=
  have := hc.isClosedImmersion_componentSpecialLift k' j hb
  have := hc.isUniversalHomeomorphism_componentSpecialLift k' j hb
  isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction ℓ _


end AlgebraicGeometry.ProEtale.CondensedRing.Correspondence.IsContractingAt
