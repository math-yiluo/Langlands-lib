/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsCompLevelwise
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClLowerStarHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-!
# The cocycle condition for (Push) along the finite subextensions

Let `ℓ` be a prime and `X` a scheme. This file

* retypes the cocone of categories `ProEtale.constructibleCocone X ℓ` (the bounded constructible
  `E`-complexes over the finite subextensions `E ⊆ ℚ̄_ℓ`, with vertex the bounded constructible
  `ℚ̄_ℓ`-complexes) on the categories `Dᵇc(X)⟦Λ⟧` of the six operations:
  `ProEtale.CondensedRing.boundedConstructibleCocone X ℓ`, with transition functors
  `boundedConstructibleExtendScalarsSubfield` and functors to the vertex
  `boundedConstructibleToPadicAlgCl`; it is a filtered 2-colimit for a noetherian `X`
  (`ProEtale.CondensedRing.boundedConstructibleCocone_isFilteredTwoColimit`);
* proves that the (Push) comparisons `Rg_*^E ⋙ T_Y ≅ T_Z ⋙ Rg_*^{ℚ̄_ℓ}` for a proper `g`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarToPadicAlgClIso`) satisfy the cocycle
  condition with respect to the (Push) isomorphisms `Rg_*^E ⋙ T_{E,F} ≅ T_{E,F} ⋙ Rg_*^F`
  between finite subextensions
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarToPadicAlgClIso_hom_app_eq`). This is the
  hypothesis `hcocycle` of `CategoryTheory.CategoryCocone.isIso_mateEquiv_of_isFilteredTwoColimit`,
  and it follows, on the underlying complexes, from the composition of the isomorphisms
  `Rf_* ⋙ D(Res) ≅ D(Res) ⋙ Rf_*` along `E ⊆ F ⊆ ℚ̄_ℓ`
  (`ProEtale.CondensedRing.derivedComapLowerStarIso_hom_app_comp`), of which the (Push)
  comparisons are the transposes along `L(Ext) ⊣ D(Res)`
  (`CategoryTheory.Adjunction.pushHomOfComapIso_app_eq_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-! ### The cocone of bounded constructible categories -/

section Cocone

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The cocone of categories `E ↦ Dᵇc(X)⟦E⟧` with vertex `Dᵇc(X)⟦ℚ̄_ℓ⟧`: the cocone
`ProEtale.constructibleCocone X ℓ`, typed on the categories `Dᵇc(X)⟦Λ⟧` of the six operations.
Its transition functors are the extensions of scalars `boundedConstructibleExtendScalarsSubfield`
and its functors to the vertex the extensions of scalars `boundedConstructibleToPadicAlgCl`. -/
noncomputable def boundedConstructibleCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧)
      (Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧) where
  T h := boundedConstructibleExtendScalarsSubfield X ℓ h
  Φ E := boundedConstructibleToPadicAlgCl X ℓ E
  iso h := constructibleToPadicAlgClCompIso X ℓ h

/-- **`ℚ̄_ℓ` is a 2-colimit**, on the categories `Dᵇc(X)⟦Λ⟧`: the cocone
`boundedConstructibleCocone X ℓ` is a filtered 2-colimit, being
`ProEtale.constructibleCocone X ℓ` (`ProEtale.constructibleCocone_isFilteredTwoColimit`). -/
theorem boundedConstructibleCocone_isFilteredTwoColimit [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructibleCocone X ℓ).IsFilteredTwoColimit :=
  constructibleCocone_isFilteredTwoColimit X ℓ

/-- The structure isomorphisms of `boundedConstructibleCocone` are, on the underlying complexes,
the transitivity isomorphisms `ProEtale.derivedExtendScalarsCompIso`. -/
lemma boundedConstructibleCocone_iso_hom_app_hom {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) :
    (((boundedConstructibleCocone X ℓ).iso h).hom.app K).hom =
      (derivedExtendScalarsCompIso X ℓ h).hom.app K.obj := by
  simp only [boundedConstructibleCocone, constructibleToPadicAlgClCompIso,
    Functor.fullyFaithfulCancelRight_hom_app, Iso.trans_hom, Iso.refl_hom, NatTrans.comp_app,
    NatTrans.id_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  erw [Category.id_comp]
  exact (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map_preimage _

/-- The inverses of the structure isomorphisms of `boundedConstructibleCocone` are, on the
underlying complexes, the inverses of the transitivity isomorphisms
`ProEtale.derivedExtendScalarsCompIso`. -/
lemma boundedConstructibleCocone_iso_inv_app_hom {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) :
    (((boundedConstructibleCocone X ℓ).iso h).inv.app K).hom =
      (derivedExtendScalarsCompIso X ℓ h).inv.app K.obj := by
  simp only [boundedConstructibleCocone, constructibleToPadicAlgClCompIso,
    Functor.fullyFaithfulCancelRight_inv_app, Iso.trans_inv, Iso.refl_inv, NatTrans.comp_app,
    NatTrans.id_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  erw [Category.comp_id]
  exact (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map_preimage _

end Cocone

/-! ### The cocycle condition -/

section Cocycle

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)

/-- The transitivity isomorphism `ProEtale.derivedExtendScalarsCompIso` of the derived extensions
of scalars `T_{E,F} ⋙ T_{F,Ω} ≅ T_{E,Ω}` is the inverse of the conjugate
`Mod.derivedExtendScalarsCompIso` of the composition isomorphism of the restrictions of
scalars. -/
lemma derivedExtendScalarsCompIso_eq_symm (X : Scheme.{u}) :
    derivedExtendScalarsCompIso X ℓ h =
      (Mod.derivedExtendScalarsCompIso (padicSubfieldRingObjMap X ℓ h)
        (padicSubfieldRingObjToPadicAlgCl X ℓ F) (padicSubfieldRingObjToPadicAlgCl X ℓ E)
        (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).symm :=
  Mod.leftDerivedFunctorCompIso_symm_trans_leftDerivedFunctorNatIso_eq _ _ _ _

/-- The inverse of `ProEtale.derivedExtendScalarsCompIso`, componentwise. -/
lemma derivedExtendScalarsCompIso_inv_app (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))) :
    (derivedExtendScalarsCompIso X ℓ h).inv.app K =
      (Mod.derivedExtendScalarsCompIso (padicSubfieldRingObjMap X ℓ h)
        (padicSubfieldRingObjToPadicAlgCl X ℓ F) (padicSubfieldRingObjToPadicAlgCl X ℓ E)
        (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).hom.app K := by
  exact congrArg (fun e ↦ e.inv.app K) (derivedExtendScalarsCompIso_eq_symm ℓ h X)

/-- `ProEtale.derivedExtendScalarsCompIso`, componentwise. -/
lemma derivedExtendScalarsCompIso_hom_app (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))) :
    (derivedExtendScalarsCompIso X ℓ h).hom.app K =
      (Mod.derivedExtendScalarsCompIso (padicSubfieldRingObjMap X ℓ h)
        (padicSubfieldRingObjToPadicAlgCl X ℓ F) (padicSubfieldRingObjToPadicAlgCl X ℓ E)
        (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).inv.app K := by
  exact congrArg (fun e ↦ e.hom.app K) (derivedExtendScalarsCompIso_eq_symm ℓ h X)

/-- **(Push) along `E ⊆ F ⊆ ℚ̄_ℓ`**, on the unbounded derived categories: the comparison for
`E ⊆ ℚ̄_ℓ` is the composite of the comparisons for `E ⊆ F` and `F ⊆ ℚ̄_ℓ`, up to the transitivity
isomorphisms `ProEtale.derivedExtendScalarsCompIso`. The (Push) comparisons are the transposes of
the isomorphisms `Rf_* ⋙ D(Res) ≅ D(Res) ⋙ Rf_*` along `L(Ext) ⊣ D(Res)`, and these compose
(`derivedComapLowerStarIso_hom_app_comp`). -/
lemma derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))) :
    (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app K =
      (derivedExtendScalarsCompIso Y ℓ h).inv.app
          (R((f)_*⟦Profinite.continuousMapRingObj E⟧).obj K) ≫
        (derivedExtendScalarsToPadicAlgCl Y ℓ F).map
          ((derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ h) f).app K) ≫
        (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) f).app
          ((derivedExtendScalarsSubfield X ℓ h).obj K) ≫
        R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          ((derivedExtendScalarsCompIso X ℓ h).hom.app K) := by
  -- (Push) is the transpose, along `L(Ext) ⊣ D(Res)`, of the isomorphism
  -- `Rf_* ⋙ D(Res) ≅ D(Res) ⋙ Rf_*`; these isomorphisms compose along `E ⊆ F ⊆ ℚ̄_ℓ`, and
  -- transposes of composites are composites.
  have H := derivedPushHom_app_eq_comp_of_comp_eq (Profinite.padicSubfieldRingObjMap ℓ h)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f
    (Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl ℓ h) K
  have hA := derivedExtendScalarsCompIso_inv_app ℓ h Y
    (R((f)_*⟦Profinite.continuousMapRingObj E⟧).obj K)
  have hD := derivedExtendScalarsCompIso_hom_app ℓ h X K
  with_reducible exact H.trans ((eq_whisker hA _).symm.trans (whisker_eq _ (whisker_eq _
    (whisker_eq _ (R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).congr_map hD.symm)))))

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- **The cocycle condition for (Push)**: the (Push) isomorphisms
`α_E : Rg_*^E ⋙ T_{E,Ω} ≅ T_{E,Ω} ⋙ Rg_*^{ℚ̄_ℓ}` for a proper `g` are compatible with the (Push)
isomorphisms `Rg_*^E ⋙ T_{E,F} ≅ T_{E,F} ⋙ Rg_*^F` between finite subextensions and with the
structure isomorphisms of the cocones `boundedConstructibleCocone`. This is the hypothesis
`hcocycle` of `CategoryTheory.CategoryCocone.isIso_mateEquiv_of_isFilteredTwoColimit`. -/
theorem boundedConstructibleLowerStarToPadicAlgClIso_hom_app_eq
    (X : Dᵇc(Z.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleLowerStarToPadicAlgClIso ℓ E g).hom.app X =
      ((boundedConstructibleCocone Y.left ℓ).iso h).inv.app
          ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g).obj X) ≫
        (boundedConstructibleToPadicAlgCl Y.left ℓ F).map
          ((asIso (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h g)).hom.app X) ≫
        (boundedConstructibleLowerStarToPadicAlgClIso ℓ F g).hom.app
          ((boundedConstructibleExtendScalarsSubfield Z.left ℓ h).obj X) ≫
        (boundedConstructibleLowerStar ℓ g).map
          (((boundedConstructibleCocone Z.left ℓ).iso h).hom.app X) := by
  have h₁ := boundedConstructibleLowerStarToPadicAlgClIso_hom_app_hom ℓ E g X
  have h₂ := derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app ℓ h g.left X.obj
  have hA : (((boundedConstructibleCocone Y.left ℓ).iso h).inv.app
      ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g).obj X)).hom =
        (derivedExtendScalarsCompIso Y.left ℓ h).inv.app
          (R((g.left)_*⟦Profinite.continuousMapRingObj E⟧).obj X.obj) :=
    boundedConstructibleCocone_iso_inv_app_hom Y.left ℓ h
      ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g).obj X)
  have hB := boundedConstructibleLowerStarExtendScalarsSubfield_app_hom ℓ h g X
  have hC : ((boundedConstructibleLowerStarToPadicAlgClIso ℓ F g).hom.app
      ((boundedConstructibleExtendScalarsSubfield Z.left ℓ h).obj X)).hom =
        (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) g.left).app
          ((derivedExtendScalarsSubfield Z.left ℓ h).obj X.obj) :=
    boundedConstructibleLowerStarToPadicAlgClIso_hom_app_hom ℓ F g
      ((boundedConstructibleExtendScalarsSubfield Z.left ℓ h).obj X)
  have hD := boundedConstructibleCocone_iso_hom_app_hom Z.left ℓ h X
  have hΦ : ((boundedConstructibleToPadicAlgCl Y.left ℓ F).map
      ((asIso (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h g)).hom.app X)).hom =
        (derivedExtendScalarsToPadicAlgCl Y.left ℓ F).map
          ((derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ h) g.left).app X.obj) := by
    exact congrArg (derivedExtendScalarsToPadicAlgCl Y.left ℓ F).map hB
  have hG : ((boundedConstructibleLowerStar ℓ g).map
      (((boundedConstructibleCocone Z.left ℓ).iso h).hom.app X)).hom =
        R((g.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          ((derivedExtendScalarsCompIso Z.left ℓ h).hom.app X.obj) := by
    exact congrArg R((g.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map hD
  ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  refine h₁.trans (h₂.trans ?_)
  dsimp only [Functor.comp_obj]
  with_reducible exact (eq_whisker hA.symm _).trans (whisker_eq _ ((eq_whisker hΦ.symm _).trans
    (whisker_eq _ ((eq_whisker hC.symm _).trans (whisker_eq _ hG.symm)))))

end Cocycle

end AlgebraicGeometry.ProEtale.CondensedRing
