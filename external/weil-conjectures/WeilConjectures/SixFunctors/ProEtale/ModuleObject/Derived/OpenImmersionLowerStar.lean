/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar

/-!

# The derived pushforward along an open immersion is fully faithful on `Dᵇc`

Let `Λ` be a commutative condensed ring and `j : U ⟶ X` an open immersion. On the unbounded
derived categories of module objects over `Λ`, the derived pushforward `Rj_*` is fully faithful
(`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful`).
The same holds on bounded constructible complexes, for every restriction of `Rj_*` to them
(`isIso_counit_of_isOpenImmersion_of_lowerStarCompatibility`), in particular for the `ℓ`-adic
coefficient rings
(`isIso_counit_boundedConstructibleUpperStarLowerStarAdjunction_of_isOpenImmersion`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section BoundedConstructible

/-- For an open immersion `j`, every restriction `F : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` of the derived
pushforward `Rj_*` is fully faithful: the counit of an adjunction `G ⊣ F` is an isomorphism. -/
lemma isIso_counit_of_isOpenImmersion_of_lowerStarCompatibility {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {G : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(U)⟦Λ⟧} {F : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧} (adj : G ⊣ F)
    (e : F ⋙ (boundedConstructible _).ι ≅ (boundedConstructible _).ι ⋙ R((j)_*⟦Λ⟧)) :
    IsIso adj.counit := by
  have hR := (derivedUpperStarLowerStarAdjunction Λ j).fullyFaithfulROfIsIsoCounit
  have h : (F ⋙ (boundedConstructible _).ι).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulι _).comp hR).ofIso e.symm
  have h' := h.ofCompFaithful
  have := h'.full
  have := h'.faithful
  exact adj.counit_isIso_of_R_fully_faithful

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

namespace ContinuousMapRingObj

/-- For an open immersion `j`, the counit `Lj^* Rj_* ⟶ 𝟭` on bounded constructible complexes is
an isomorphism (`E`-coefficient). -/
instance isIso_counit_boundedConstructibleUpperStarLowerStarAdjunction_of_isOpenImmersion
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ E j).counit :=
  isIso_counit_of_isOpenImmersion_of_lowerStarCompatibility _ j.left _
    (boundedConstructibleLowerStarCompatibility ℓ E j)

end ContinuousMapRingObj

namespace PadicIntegersRingObj

/-- For an open immersion `j`, the counit `Lj^* Rj_* ⟶ 𝟭` on bounded constructible complexes is
an isomorphism (`𝒪_E`-coefficient). -/
instance isIso_counit_boundedConstructibleUpperStarLowerStarAdjunction_of_isOpenImmersion
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ E j).counit :=
  isIso_counit_of_isOpenImmersion_of_lowerStarCompatibility _ j.left _
    (boundedConstructibleLowerStarCompatibility ℓ E j)

end PadicIntegersRingObj

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
