/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence

/-!
# The bounded constructible lower shriek commutes with the shifts

The derived lower shriek `Rf_!^c = i_! ⋙ Rp_*` attached to a compactification `c = (i, p)` on
bounded constructible complexes is a composite of functors commuting with the shifts, and its
comparison isomorphism with the ambient lower shriek `Rf_!(c)⟦Λ⟧` commutes with the shifts.

This file shows that the isomorphisms identifying the lower shrieks of two compactifications
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl`) and
the identification `Rf_! ≅ Rf_*` of a proper morphism
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl`) commute with the
shifts: they are assembled from units and counits of adjunctions commuting with the shifts,
composition and identity isomorphisms of pullbacks and pushforwards, and their conjugates.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The ambient lower shriek -/

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

set_option synthInstance.maxSize 1024 in
-- the instance problems for the composite with the right derived functor are large
/-- The derived lower shriek on the derived categories of module objects commutes with the
shifts: it is the composite of the functor induced by the exact extension by zero and a right
derived functor. -/
noncomputable instance : (R(f)_!⟦Λ⟧).CommShift ℤ := by
  delta rightDerivedLowerShriek
  infer_instance

/-- The derived lower shriek on the derived categories of module objects is triangulated. -/
instance : (R(f)_!⟦Λ⟧).IsTriangulated := by
  unfold rightDerivedLowerShriek
  infer_instance

end Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The lower shriek of a compactification -/

section OfCompactification

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

noncomputable instance (c : Compactification f.left) :
    (boundedConstructibleLowerShriekOfCompactification ℓ c).CommShift ℤ := by
  delta boundedConstructibleLowerShriekOfCompactification
  infer_instance

instance (c : Compactification f.left) :
    NatTrans.CommShift
      (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c).hom ℤ := by
  unfold boundedConstructibleLowerShriekOfCompactificationCompatibility
    boundedConstructibleLowerShriekOfCompactification
  infer_instance

variable (f)

/-- The derived lower shriek on bounded constructible complexes commutes with the shifts. -/
noncomputable instance : (boundedConstructibleLowerShriek ℓ f).CommShift ℤ := by
  delta boundedConstructibleLowerShriek
  infer_instance

instance : NatTrans.CommShift (boundedConstructibleLowerShriekCompatibility ℓ f).hom ℤ := by
  unfold boundedConstructibleLowerShriekCompatibility boundedConstructibleLowerShriek
  infer_instance

end OfCompactification

/-! ### The pullback comparison of a square -/

section Square

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison of a commutative square commutes with the shifts. -/
instance commShift_boundedConstructiblePullbackSquareComparison_hom (sq : CommSq g' f' f g) :
    NatTrans.CommShift (boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom ℤ := by
  have : NatTrans.CommShift (eqToHom (show boundedConstructibleUpperStar Λ ℓ (f' ≫ g) =
      boundedConstructibleUpperStar Λ ℓ (g' ≫ f) by rw [sq.w])) ℤ :=
    NatTrans.CommShift.eqToHom_congrArg (fun m : X' ⟶ Y ↦ boundedConstructibleUpperStar Λ ℓ m)
      sq.w.symm
  unfold boundedConstructiblePullbackSquareComparison
  dsimp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  infer_instance

end Square

/-! ### The extension-by-zero base change and the exchange morphism -/

section Exchange

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]

section BaseChange

variable {j : X ⟶ Z} {g : Z' ⟶ Z} {j' : X' ⟶ Z'} {g' : X' ⟶ X}
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]

set_option synthInstance.maxSize 1024 in
/-- The extension-by-zero base change morphism commutes with the shifts. -/
instance commShift_boundedConstructibleOpenImmersionLowerShriekBaseChange'
    (sq : CommSq g' j' j g) :
    NatTrans.CommShift (boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq) ℤ := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange'_def]
  unfold boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep'
    boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep'
    boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep'
  dsimp only [Functor.squareTransport, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

instance commShift_boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'_hom
    (sq : IsPullback g' j' j g) :
    NatTrans.CommShift (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq).hom
      ℤ := by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq
  unfold boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'
  dsimp only [Iso.symm_hom, asIso_inv]
  exact NatTrans.CommShift.of_isIso _ ℤ

end BaseChange

variable {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

set_option synthInstance.maxSize 1024 in
/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square commutes with the
shifts. -/
instance commShift_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
    (sq : IsPullback p i' j p') :
    NatTrans.CommShift
      (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq) ℤ := by
  unfold boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep'
  dsimp only [Functor.squareTransport, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

end Exchange

/-! ### Independence of the compactification -/

section Refinement

variable {X Z Z₁ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- The comparison `Rf_!^{c₁} ≅ Rf_!^c` along a refinement commutes with the shifts. -/
instance commShift_boundedConstructibleLowerShriekRefinementIso'_hom
    (sq : IsPullback (𝟙 X) i i₁ h) {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq)] :
    NatTrans.CommShift (boundedConstructibleLowerShriekRefinementIso' ℓ sq wp).hom ℤ := by
  have : NatTrans.CommShift (eqToHom (show boundedConstructibleLowerStar ℓ (h ≫ p₁) =
      boundedConstructibleLowerStar ℓ p by rw [wp])) ℤ :=
    NatTrans.CommShift.eqToHom_congrArg (fun m : Z ⟶ Y ↦ boundedConstructibleLowerStar ℓ m) wp
  unfold boundedConstructibleLowerShriekRefinementIso'
  dsimp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, asIso_hom, eqToIso.hom]
  infer_instance

end Refinement

section Independence

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The independence of the lower shriek from the compactification commutes with the shifts. -/
instance commShift_boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom
    (c₁ c₂ : Compactification f.left) :
    NatTrans.CommShift
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₂).hom ℤ := by
  rw [boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_def]
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

end Independence

/-! ### The lower shriek of a proper morphism -/

section Proper

/-- The identity isomorphism `D((𝟙 X)_!) ≅ 𝟭` of the extension by zero along the identity
commutes with the shifts. -/
instance commShift_derivedOpenImmersionLowerShriekId_hom (X : Scheme.{u}) :
    NatTrans.CommShift (derivedOpenImmersionLowerShriekId Λ X).hom ℤ := by
  unfold derivedOpenImmersionLowerShriekId
  infer_instance

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y) [IsProper f.left]

instance commShift_boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_hom :
    NatTrans.CommShift (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso Λ ℓ f).hom ℤ := by
  unfold boundedConstructibleOpenImmersionLowerShriekOfIsProperIso
  infer_instance

instance commShift_boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_hom :
    NatTrans.CommShift
      (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ f).hom ℤ := by
  have : NatTrans.CommShift (Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso (Profinite.padicAlgClRingObj ℓ) ℓ
          f)
      (boundedConstructibleLowerStarOfIsProper ℓ (Compactification.ofIsProper f.left).overG) ≪≫
      Functor.leftUnitor _).hom ℤ := inferInstance
  exact this

/-- The identification `Rf_! ≅ Rf_*` of a proper morphism commutes with the shifts. -/
instance commShift_boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_hom :
    NatTrans.CommShift (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom ℤ := by
  rw [boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq]
  infer_instance

end Proper

end AlgebraicGeometry.ProEtale.CondensedRing
