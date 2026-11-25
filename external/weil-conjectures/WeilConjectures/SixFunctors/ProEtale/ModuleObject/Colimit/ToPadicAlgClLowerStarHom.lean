/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents

/-!
# The extension of scalars `E ⟶ ℚ̄_ℓ` and the proper direct image on underlying complexes

The comparison `boundedConstructibleLowerStarToPadicAlgClHom` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility` and the
isomorphism `boundedConstructibleLowerStarToPadicAlgClIso` it induces, computed on the underlying
complexes (`boundedConstructibleLowerStarToPadicAlgClHom_app_hom`,
`boundedConstructibleLowerStarToPadicAlgClIso_hom_app_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

lemma boundedConstructibleToPadicAlgCl_map_hom (X : Scheme.{u})
    {K L : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧} (φ : K ⟶ L) :
    ((boundedConstructibleToPadicAlgCl X ℓ E).map φ).hom =
      (derivedExtendScalarsToPadicAlgCl X ℓ E).map φ.hom :=
  rfl

lemma boundedConstructibleToPadicAlgCl_obj_obj (X : Scheme.{u})
    (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleToPadicAlgCl X ℓ E).obj K).obj =
      (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj :=
  rfl

section Proper

variable (p : X ⟶ Y) [IsProper p.left]

omit [IsProper p.left] in
/-- The comparison `boundedConstructibleLowerStarToPadicAlgClHom` is, on the underlying
complexes, the derived (Push) comparison `derivedPushHom`. -/
lemma boundedConstructibleLowerStarToPadicAlgClHom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleLowerStarToPadicAlgClHom ℓ E p).app K).hom =
      (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p.left).app K.obj := by
  simp only [Functor.comp_obj, boundedConstructibleToPadicAlgCl_obj_obj,
    ContinuousMapRingObj.boundedConstructibleLowerStar_obj_obj,
    boundedConstructibleLowerStar_obj_obj, boundedConstructibleLowerStarToPadicAlgClHom,
    Functor.whiskeringRight_obj_obj, boundedConstructibleToPadicAlgClCompatibility,
    ObjectProperty.liftCompιIso, ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility,
    boundedConstructibleLowerStarCompatibility, Iso.refl_hom, Iso.refl_inv,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.comp_app, ObjectProperty.ι_obj,
    Functor.associator_hom_app, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.lift_obj_obj, Functor.associator_inv_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, ObjectProperty.homMk_hom]

lemma boundedConstructibleLowerStarToPadicAlgClIso_hom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleLowerStarToPadicAlgClIso ℓ E p).hom.app K).hom =
      (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p.left).app K.obj :=
  boundedConstructibleLowerStarToPadicAlgClHom_app_hom ℓ E p K

end Proper

end AlgebraicGeometry.ProEtale.CondensedRing
