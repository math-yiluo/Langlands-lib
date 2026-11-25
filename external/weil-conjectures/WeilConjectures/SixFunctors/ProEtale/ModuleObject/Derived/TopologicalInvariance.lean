/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar

/-!

# Topological invariance of the bounded constructible derived category

For a finite universal homeomorphism `r : X ⟶ X'` of schemes over `Spec k`, the derived pullback
`Lr^* : Dᵇc(X') ⥤ Dᵇc(X)` is an equivalence with inverse `Rr_*`: the unit of `Lr^* ⊣ Rr_*` is an
isomorphism (blueprint `lemma-comparison-via-relative-frobenius--1`).

## Main statements

- `ProEtale.CondensedRing.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction`: the unit
  `𝟭 ⟶ Lr^* ⋙ Rr_*` is an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Topological invariance -/

section TopologicalInvariance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom]
  (r : X ⟶ X') [IsFinite r.left] [IsUniversalHomeomorphism r.left]

omit [IsFinite r.left] in
/-- **Topological invariance** of the bounded constructible derived category: for a finite
universal homeomorphism `r`, the unit `𝟭 ⟶ Lr^* ⋙ Rr_*` of the adjunction `Lr^* ⊣ Rr_*` is an
isomorphism, so that `Lr^*` is an equivalence with inverse `Rr_*` (blueprint
`lemma-comparison-via-relative-frobenius--1`). -/
theorem isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ r).unit := by
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism (Profinite.padicAlgClRingObj ℓ) r.left
  have : ((r.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).leftDerivedFunctor.IsEquivalence :=
    Functor.isEquivalence_of_iso
      (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm
  let hFF : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := (boundedConstructible _).ι)
      (((ObjectProperty.fullyFaithfulι _).comp
        (Functor.FullyFaithful.ofFullyFaithful _)).ofIso
        (boundedConstructibleUpperStarCompatibility _ ℓ r).symm)
  have := hFF.full
  have := hFF.faithful
  exact (boundedConstructibleUpperStarLowerStarAdjunction ℓ r).unit_isIso_of_L_fully_faithful

end TopologicalInvariance

end AlgebraicGeometry.ProEtale.CondensedRing
