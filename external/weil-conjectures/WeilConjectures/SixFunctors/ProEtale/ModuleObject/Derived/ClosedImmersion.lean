/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion

/-!

# Full faithfulness of `Ri_*` on bounded constructible complexes

Let `Λ` be a commutative condensed ring, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` an open
immersion. This file proves:

* the derived pushforward `Ri_*` is fully faithful, i.e. the counit `Li^* Ri_* ⟶ 𝟭` is an
  isomorphism, on bounded constructible complexes
  (`ProEtale.CondensedRing.isIso_boundedConstructibleUpperStarLowerStarAdjunction_counit`), as it
  is on `D(Mod_{Λ_Z})`
  (`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion`,
  in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionFullyFaithful`);
* `Lj^* Ri_* = 0` on bounded constructible complexes when the ranges of `i` and `j` are disjoint
  (`ProEtale.CondensedRing.isZero_boundedConstructibleUpperStar_obj_lowerStar_obj`), by adjunction
  from `Li^* j_! = 0`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

include ℓ k

/-- The derived pushforward `Ri_*` along a closed immersion is fully faithful on bounded
constructible complexes: the counit `Li^* Ri_* ⟶ 𝟭` is an isomorphism. -/
instance isIso_boundedConstructibleUpperStarLowerStarAdjunction_counit
    {Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ i).counit := by
  have h : (boundedConstructibleLowerStar ℓ i ⋙ (boundedConstructible _).ι).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (Functor.FullyFaithful.ofFullyFaithful _)).ofIso
      (boundedConstructibleLowerStarCompatibility ℓ i).symm
  have h' := h.ofCompFaithful
  have := h'.full
  have := h'.faithful
  exact (boundedConstructibleUpperStarLowerStarAdjunction ℓ i).counit_isIso_of_R_fully_faithful

/-- **`Lj^* Ri_*` vanishes on bounded constructible complexes** when the ranges of the open
immersion `j` and of `i` are disjoint: by the adjunctions `j_! ⊣ Lj^*` and `Li^* ⊣ Ri_*`, a
morphism `M ⟶ Lj^* Ri_* N` is a morphism `Li^* j_! M ⟶ N`, and `Li^* j_! = 0`
(`ProEtale.CondensedRing.isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek`). -/
lemma isZero_boundedConstructibleUpperStar_obj_lowerStar_obj
    {Z U X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X)
    (hji : Disjoint (Set.range j.left.base) (Set.range i.left.base)) (N :
        Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
      ((boundedConstructibleLowerStar ℓ i).obj N)) := by
  set adjj := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j
  set adji := boundedConstructibleUpperStarLowerStarAdjunction ℓ i
  rw [IsZero.iff_id_eq_zero]
  refine (adjj.homEquiv _ _).symm.injective ((adji.homEquiv _ _).symm.injective ?_)
  exact (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ j i hji
    _).eq_of_src _ _

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
