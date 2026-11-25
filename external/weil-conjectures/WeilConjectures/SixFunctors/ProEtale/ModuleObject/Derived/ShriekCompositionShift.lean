/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.OpenImmersionBaseChange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionPadicAlgCl

/-!
# The composition isomorphism of the bounded constructible lower shriek commutes with the shifts

The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on bounded constructible `ℚ̄_ℓ`-sheaves
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`) commutes with the
shifts (`ProEtale.CondensedRing.commShift_boundedConstructibleLowerShriekComp_padicAlgCl_hom`).
Like the isomorphisms of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekShift`, it is assembled
from units and counits of adjunctions commuting with the shifts and from composition isomorphisms
of pullbacks and pushforwards; here through the comparison of the extensions by zero along a
refinement of compactifications and the exchange of extension by zero and proper pushforward.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

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
instance commShift_boundedConstructibleOpenImmersionLowerShriekBaseChange
    (sq : CommSq g' j' j g) :
    NatTrans.CommShift (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq) ℤ := by
  unfold boundedConstructibleOpenImmersionLowerShriekBaseChange
    boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep
    boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep
    boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep
  dsimp only [Functor.squareTransport, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

instance commShift_boundedConstructibleOpenImmersionLowerShriekBaseChangeIso_hom
    (sq : IsPullback g' j' j g) :
    NatTrans.CommShift (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).hom
      ℤ := by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq
  unfold boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
  dsimp only [Iso.symm_hom, asIso_inv]
  exact NatTrans.CommShift.of_isIso _ ℤ

end BaseChange

variable {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

set_option synthInstance.maxSize 1024 in
/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square commutes with the
shifts. -/
instance commShift_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    (sq : IsPullback p i' j p') :
    NatTrans.CommShift
      (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ sq) ℤ := by
  unfold boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep
  dsimp only [Functor.squareTransport, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

end Exchange

/-! ### The comparison along a refinement -/

section Refinement

variable {X Z Z₁ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

instance commShift_boundedConstructibleUpperStarTriangleComparison_hom (w : i ≫ h = i₁) :
    NatTrans.CommShift (boundedConstructibleUpperStarTriangleComparison Λ ℓ w).hom ℤ := by
  have : NatTrans.CommShift (eqToHom (show boundedConstructibleUpperStar Λ ℓ i₁ =
      boundedConstructibleUpperStar Λ ℓ (i ≫ h) by rw [w])) ℤ :=
    NatTrans.CommShift.eqToHom_congrArg (fun m : X ⟶ Z₁ ↦ boundedConstructibleUpperStar Λ ℓ m)
      w.symm
  unfold boundedConstructibleUpperStarTriangleComparison
  dsimp only [Iso.trans_hom, eqToIso.hom]
  infer_instance

instance commShift_boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep :
    NatTrans.CommShift
      (boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep Λ ℓ (i := i) (i₁ := i₁))
      ℤ := by
  unfold boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep
  infer_instance

set_option synthInstance.maxSize 1024 in
instance commShift_boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep_hom
    (w : i ≫ h = i₁) :
    NatTrans.CommShift
      (boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep Λ ℓ w).hom ℤ := by
  -- the transported square is stated for `𝟭 ⋙ i_!`, the step for `i_!`
  have e : (boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep Λ ℓ w).hom =
      Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
          boundedConstructibleUpperStar Λ ℓ i₁)
        (Functor.leftUnitor (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i)).inv ≫
      (Functor.squareTransport (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁)
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i)
        (Functor.rightUnitor _ ≪≫ boundedConstructibleUpperStarTriangleComparison Λ ℓ w)).hom := by
    exact (Category.id_comp _).symm
  rw [e]
  dsimp only [Functor.squareTransport, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

instance commShift_boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep :
    NatTrans.CommShift
      (boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep Λ ℓ (i := i) (i₁ := i₁)
        (h := h)) ℤ := by
  unfold boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep
  infer_instance

/-- The comparison `i_! ⟶ i₁_! ⋙ Lh^*` of the extensions by zero along a refinement commutes with
the shifts. -/
instance commShift_boundedConstructibleOpenImmersionLowerShriekRefinement (w : i ≫ h = i₁) :
    NatTrans.CommShift (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ w) ℤ := by
  unfold boundedConstructibleOpenImmersionLowerShriekRefinement
  infer_instance



/-- The pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` along a refinement commutes with the
shifts. -/
instance commShift_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    (sq : IsPullback (𝟙 X) i i₁ h) :
    NatTrans.CommShift (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq)
      ℤ := by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement (Profinite.padicAlgClRingObj
      ℓ) ℓ sq
  have : NatTrans.CommShift (inv (boundedConstructibleOpenImmersionLowerShriekRefinement
      (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id)) ℤ := NatTrans.CommShift.of_isIso _ ℤ
  unfold boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
  infer_instance

/-- The comparison `Rf_!^{c₁} ≅ Rf_!^c` along a refinement commutes with the shifts. -/
instance commShift_boundedConstructibleLowerShriekRefinementIso_hom
    (sq : IsPullback (𝟙 X) i i₁ h) {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq)] :
    NatTrans.CommShift (boundedConstructibleLowerShriekRefinementIso ℓ sq wp).hom ℤ := by
  have : NatTrans.CommShift (eqToHom (show boundedConstructibleLowerStar ℓ (h ≫ p₁) =
      boundedConstructibleLowerStar ℓ p by rw [wp])) ℤ :=
    NatTrans.CommShift.eqToHom_congrArg (fun m : Z ⟶ Y ↦ boundedConstructibleLowerStar ℓ m) wp
  unfold boundedConstructibleLowerShriekRefinementIso
  dsimp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    asIso_hom, eqToIso.hom]
  infer_instance

end Refinement

/-! ### Independence of the compactification and composition -/

section Composition

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]

/-- The independence of the lower shriek from the compactification, through the pushforward
comparisons, commutes with the shifts. -/
instance commShift_boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_hom
    {f : X ⟶ Y} (c₁ c₂ : Compactification f.left) :
    NatTrans.CommShift
      (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁ c₂).hom ℤ := by
  unfold boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

set_option synthInstance.maxSize 1024 in
/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the bounded constructible lower
shriek commutes with the shifts. -/
instance commShift_boundedConstructibleLowerShriekComp_padicAlgCl_hom (f : X ⟶ Y) (g : Y ⟶ S) :
    NatTrans.CommShift (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom ℤ := by
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_def]
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, asIso_hom, asIso_inv]
  infer_instance

end Composition

end AlgebraicGeometry.ProEtale.CondensedRing
