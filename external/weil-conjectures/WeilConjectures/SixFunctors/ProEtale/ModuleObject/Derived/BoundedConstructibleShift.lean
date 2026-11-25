/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing

/-!
# The bounded constructible pullback and pushforward commute with the shifts

The bounded constructible derived categories `Dᵇc(X)⟦Λ⟧` are stable under the shifts of the
ambient derived categories (`ProEtale.CondensedRing.isStableUnderShift_boundedConstructible`), so
they carry shift structures for which the inclusions commute with the shifts. The restricted
functors `Lf^*`, `Rf_*` and `j_!`, defined by lifting the ambient ones, inherit shift structures
for which their comparison isomorphisms with the ambient functors commute with the shifts.

This file shows that the adjunctions `Lf^* ⊣ Rf_*` and `j_! ⊣ Lj^*` and the composition and
identity isomorphisms of `Lf^*` and `Rf_*` on bounded constructible complexes commute with the
shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section Functors

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] (f : X ⟶ Y)

/-- The derived pullback on bounded constructible complexes commutes with the shifts. -/
noncomputable instance : (boundedConstructibleUpperStar Λ ℓ f).CommShift ℤ := by
  delta boundedConstructibleUpperStar
  infer_instance

instance : NatTrans.CommShift (boundedConstructibleUpperStarCompatibility Λ ℓ f).hom ℤ := by
  unfold boundedConstructibleUpperStarCompatibility boundedConstructibleUpperStar
  infer_instance

/-- The composition isomorphism of the derived pullback on bounded constructible complexes
commutes with the shifts. -/
instance commShift_boundedConstructibleUpperStarComp_hom (g : Y ⟶ Z) :
    NatTrans.CommShift (boundedConstructibleUpperStarComp Λ ℓ f g).hom ℤ := by
  unfold boundedConstructibleUpperStarComp
  infer_instance

/-- The identity isomorphism of the derived pullback on bounded constructible complexes
commutes with the shifts. -/
instance commShift_boundedConstructibleUpperStarId_hom (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    NatTrans.CommShift (boundedConstructibleUpperStarId Λ ℓ X).hom ℤ := by
  unfold boundedConstructibleUpperStarId
  infer_instance

/-- The derived pushforward on bounded constructible complexes commutes with the shifts. -/
noncomputable instance : (boundedConstructibleLowerStar ℓ f).CommShift ℤ := by
  delta boundedConstructibleLowerStar
  infer_instance

instance : NatTrans.CommShift (boundedConstructibleLowerStarCompatibility ℓ f).hom ℤ := by
  unfold boundedConstructibleLowerStarCompatibility boundedConstructibleLowerStar
  infer_instance

/-- The derived pushforward along a proper morphism on bounded constructible complexes commutes
with the shifts. -/
noncomputable instance [IsProper f.left] :
    (boundedConstructibleLowerStarOfIsProper ℓ f).CommShift ℤ := by
  delta boundedConstructibleLowerStarOfIsProper
  infer_instance

instance [IsProper f.left] :
    NatTrans.CommShift (boundedConstructibleLowerStarOfIsProperCompatibility ℓ f).hom ℤ := by
  unfold boundedConstructibleLowerStarOfIsProperCompatibility
    boundedConstructibleLowerStarOfIsProper
  infer_instance

/-- The adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes commutes with the shifts. -/
instance commShift_boundedConstructibleUpperStarLowerStarAdjunction :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).CommShift ℤ :=
  Adjunction.commShift_restrictFullyFaithful _ _ _ _ _

/-- The composition isomorphism of the derived pushforward on bounded constructible complexes,
a conjugate of that of the pullback, commutes with the shifts. -/
instance commShift_boundedConstructibleLowerStarComp_hom (g : Y ⟶ Z) :
    NatTrans.CommShift (boundedConstructibleLowerStarComp ℓ f g).hom ℤ := by
  unfold boundedConstructibleLowerStarComp
  infer_instance

/-- The identity isomorphism of the derived pushforward on bounded constructible complexes,
a conjugate of that of the pullback, commutes with the shifts. -/
instance commShift_boundedConstructibleLowerStarId_hom (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    NatTrans.CommShift (boundedConstructibleLowerStarId ℓ X).hom ℤ := by
  unfold boundedConstructibleLowerStarId
  infer_instance

end Functors

section OpenImmersion

variable {U X V : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
  [IsSeparated V.hom] (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The extension by zero on bounded constructible complexes commutes with the shifts. -/
noncomputable instance : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).CommShift ℤ := by
  delta boundedConstructibleOpenImmersionLowerShriek
  infer_instance

instance :
    NatTrans.CommShift (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).hom ℤ := by
  unfold boundedConstructibleOpenImmersionLowerShriekCompatibility
    boundedConstructibleOpenImmersionLowerShriek
  infer_instance

/-- The adjunction `j_! ⊣ Lj^*` on bounded constructible complexes commutes with the shifts. -/
instance commShift_boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).CommShift ℤ :=
  Adjunction.commShift_restrictFullyFaithful _ _ _ _ _

/-- The composition isomorphism of the extension by zero on bounded constructible complexes,
a conjugate of that of the pullback, commutes with the shifts. -/
instance commShift_boundedConstructibleOpenImmersionLowerShriekComp_hom (j' : X ⟶ V)
    [IsOpenImmersion j'.left] [IsOpenImmersion (j ≫ j').left] :
    NatTrans.CommShift (boundedConstructibleOpenImmersionLowerShriekComp Λ ℓ j j').hom ℤ := by
  unfold boundedConstructibleOpenImmersionLowerShriekComp
  infer_instance

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing
