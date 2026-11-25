/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardDataRings
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate

/-!
# The extension of scalars `E ⟶ ℚ̄_ℓ` is a coefficient change

The extension of scalars `T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` with the comparisons (Pull), (Shriek)
and (Push) of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility`
is a coefficient change of the bounded constructible six functors
(`ProEtale.CondensedRing.toPadicAlgClCoefficientChange`): the compatibilities are the
restrictions of those on the ambient derived categories
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The extension of scalars `E ⟶ ℚ̄_ℓ` as a coefficient change of the bounded constructible six
functors. -/
noncomputable def toPadicAlgClCoefficientChange :
    BoundedConstructibleCoefficientChange (Profinite.continuousMapRingObj E)
      (Profinite.padicAlgClRingObj ℓ) ℓ (continuousMapPushforwardData ℓ k E)
      (padicAlgClPushforwardData ℓ k)
      (fun X _ _ _ ↦ boundedConstructibleToPadicAlgCl X.left ℓ E)
      (fun f ↦ boundedConstructibleUpperStarToPadicAlgClIso ℓ E f) where
  pull_comp f g := by
    intro K
    ext1
    have h := squareCompatible_leftDerivedUpperStarComp
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left g.left K.obj
    simp only [Functor.pasteSquareIso_hom_app] at h
    simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.pasteSquareIso_hom_app,
      boundedConstructibleUpperStarComp_hom_app_hom, boundedConstructibleUpperStar_map_hom,
      boundedConstructibleUpperStarToPadicAlgClIso_hom_app_hom,
      boundedConstructibleToPadicAlgCl_map_hom, boundedConstructibleToPadicAlgCl_obj_obj,
      boundedConstructibleUpperStar_obj_obj, Over.comp_left]
    dsimp only [Functor.comp_obj] at h ⊢
    with_reducible exact h
  shriek j _ := boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E j
  isMateSquare_shriek_pull j _ := by
    intro K
    ext1
    have h := isMateSquare_derivedOpenImmersionShriekIso_derivedPullIso
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) j.left K.obj
    simp only [ObjectProperty.FullSubcategory.comp_hom,
      boundedConstructibleUpperStarToPadicAlgClIso_hom_app_hom,
      boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso_inv_app_hom,
      boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit_app_hom,
      boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_counit_app_hom,
      boundedConstructibleUpperStar_map_hom, boundedConstructibleToPadicAlgCl_map_hom,
      boundedConstructibleToPadicAlgCl_obj_obj, boundedConstructibleUpperStar_obj_obj,
      boundedConstructibleOpenImmersionLowerShriek_obj_obj]
    dsimp only [Functor.comp_obj] at h ⊢
    with_reducible exact h
  push p _ := boundedConstructibleLowerStarToPadicAlgClIso ℓ E p
  isMateSquare_pull_push p _ := by
    intro K
    ext1
    have h := NatTrans.congr_app (derivedPushHom_eq_mateEquiv
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p.left) K.obj
    simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
      Category.comp_id, Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h
    simp only [continuousMapPushforwardData, padicAlgClPushforwardData,
      ObjectProperty.FullSubcategory.comp_hom,
      boundedConstructibleLowerStarToPadicAlgClIso_hom_app_hom,
      boundedConstructibleUpperStarToPadicAlgClIso_inv_app_hom,
      boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom',
      ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom',
      boundedConstructibleLowerStar_map_hom, boundedConstructibleToPadicAlgCl_map_hom,
      boundedConstructibleToPadicAlgCl_obj_obj, boundedConstructibleUpperStar_obj_obj,
      boundedConstructibleLowerStar_obj_obj,
      ContinuousMapRingObj.boundedConstructibleLowerStar_obj_obj]
    dsimp only [Functor.comp_obj] at h ⊢
    with_reducible exact h

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- (Shriek) along the chosen compactification is the comparison pasted from (Shriek) for the open
immersion and (Push) for the proper morphism of the coefficient change `E ⟶ ℚ̄_ℓ`. -/
lemma boundedConstructibleLowerShriekToPadicAlgClIso_eq_shriekOfCompactification (f : X ⟶ Y) :
    boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f =
      (toPadicAlgClCoefficientChange ℓ E k).shriekOfCompactification
        (compactificationOverField f) := by
  dsimp only [boundedConstructibleLowerShriekToPadicAlgClIso,
    boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso,
    BoundedConstructibleCoefficientChange.shriekOfCompactification, Functor.pasteSquareIso,
    toPadicAlgClCoefficientChange, continuousMapPushforwardData, padicAlgClPushforwardData]
  -- the proper-only `Rp_*` of the shriek and the general one agree definitionally
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
