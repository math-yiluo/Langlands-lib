/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation
public import WeilConjectures.WeilSheaf.Native.NativeCondensedModelTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-!
# The condensed model of `ℓ`-adic sheaves commutes monoidally with pullback

Let `f : Z ⟶ Y` be a morphism of schemes and `E_X : AdicSheaf ℓ X ≌ Mod_{Λ_X}` the condensed model
of `ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`), `E_X` being
`forgetAb ⋙ comap κ_X` on the underlying abelian sheaves. We construct an isomorphism
`E_Y ⋙ f^* ≅ f^*ᵃ ⋙ E_Z` (`AlgebraicGeometry.ProEtale.condensedModUpperStarIso`) whose
underlying map of abelian sheaves is the identification
`f^*(U M) ≅ U(f^* M)` of `AlgebraicGeometry.ProEtale.sheafComposeForget₂CompUpperStarIso`, the
condensed pullback `f^*` of module objects being identified with `mapMod(f^*) ⋙ comap α_f⁻¹`
(`CategoryTheory.Mod.extendScalarsIsoComapInv`).

This isomorphism is monoidal: it carries the pullback–tensor comparison
`AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso` of `ℓ`-adic sheaves to the comonoidal
structure of the condensed pullback
(`AlgebraicGeometry.ProEtale.condensedModUpperStarIso_tensor`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory

section RelativeTensor

variable {C : Type*} [Category* C] [Abelian C] [IsGrothendieckAbelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

omit [MonoidalPreadditive C] in
/-- On the projection `M ⊗ N ⟶ M ⊗_R N`, the comparison `Mod.relativeTensorRightIso` is the
projection of the monoidal tensor product. -/
@[reassoc]
lemma Mod.tensorπ_relativeTensorRightIso_hom_app (M N : Mod C R) :
    Mod.tensorπ M N ≫ ((Mod.relativeTensorRightIso N).hom.app M).hom = Mod.tensorObjπ M N := by
  have h : colimit.ι ((Mod.tensorLeftDiagram R N).flip.obj M) WalkingParallelPair.one ≫
      (Mod.relativeTensorRightIso N).hom.app M = Mod.relativeTensorπ M N := by
    simp [Mod.relativeTensorRightIso, HasColimit.ι_isoOfNatIso_hom_assoc,
      Mod.relativeTensorCofork]
  exact congrArg Mod.Hom.hom h

omit [MonoidalPreadditive C] in
/-- On the projection `M ⊗ N ⟶ M ⊗_R N` of the monoidal tensor product, the inverse of
`Mod.relativeTensorRightIso` is the projection onto the coequalizer tensor product. -/
@[reassoc]
lemma Mod.tensorObjπ_relativeTensorRightIso_inv_app (M N : Mod C R) :
    Mod.tensorObjπ M N ≫ ((Mod.relativeTensorRightIso N).inv.app M).hom = Mod.tensorπ M N := by
  rw [← Mod.tensorπ_relativeTensorRightIso_hom_app, Category.assoc, ← Mod.comp_hom',
    Iso.hom_inv_id_app, Mod.id_hom', Category.comp_id]

end RelativeTensor

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {Z Y : Scheme.{u}} (f : Z ⟶ Y)

/-- The transpose of the ring identity: `α_f` followed by `κ_Z` agrees with `f^* κ_Y`, the
identification `f^* (U ℚ̄_ℓ,Y) ≅ U (f^* ℚ̄_ℓ,Y)` and `U` of the ring map `f^* ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,Z`
transposed from `ℚ̄_ℓ,Y ⟶ f_* ℚ̄_ℓ,Z`. -/
lemma condensedPullbackHom_comp_condensedRingObjIsoForgetAb_hom :
    condensedPullbackHom (Profinite.padicAlgClRingObj l) f ≫
        (condensedRingObjIsoForgetAb l Z).hom =
      (f)^*[Ab.{u + 1}].map (condensedRingObjIsoForgetAb l Y).hom ≫
        (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).hom.app
          (adicConstantSheaf l Y) ≫
        (weilCoefficientsForgetAb l Z).map
          (((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).homEquiv _ _).symm
            (adicConstantSheafToLowerStar l f)) := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, unitAlgHom_comp_map_condensedPullbackHom,
    condensedPushforwardHom_comp_map_condensedRingObjIsoForgetAb_hom,
    Functor.map_comp, Adjunction.unit_naturality_assoc, Functor.map_comp,
    unit_app_comp_lowerStar_map_sheafComposeForget₂CompUpperStarIso_hom_app_assoc]
  congr 1
  have h := (weilCoefficientsForgetAb l Y).map_comp
    ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).unit.app (adicConstantSheaf l Y))
    ((f)_*[WeilCoefficients.{u} l].map
      (((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).homEquiv _ _).symm
        (adicConstantSheafToLowerStar l f)))
  have e :=
    ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).homEquiv _ _).apply_symm_apply
      (adicConstantSheafToLowerStar l f)
  rw [Adjunction.homEquiv_unit] at e
  exact (congrArg (weilCoefficientsForgetAb l Y).map e).symm.trans h

/-- The ring objects: the identification `κ_Z : Λ_Z ≅ U ℚ̄_ℓ,Z` followed by `U` of the ring
isomorphism `ℚ̄_ℓ,Z ⟶ f^* ℚ̄_ℓ,Y` agrees with `α_f⁻¹ : Λ_Z ⟶ f^* Λ_Y` followed by `f^* κ_Y` and
the identification `f^* (U ℚ̄_ℓ,Y) ≅ U (f^* ℚ̄_ℓ,Y)`. -/
lemma condensedRingObjIsoForgetAb_hom_comp_map_adicUpperStarRingHom :
    (condensedRingObjIsoForgetAb l Z).hom ≫
        (weilCoefficientsForgetAb l Z).map (adicUpperStarRingHom l f) =
      inv (condensedPullbackHom (Profinite.padicAlgClRingObj l) f) ≫
        (f)^*[Ab.{u + 1}].map (condensedRingObjIsoForgetAb l Y).hom ≫
        (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).hom.app
          (adicConstantSheaf l Y) := by
  rw [IsIso.eq_inv_comp, ← Category.assoc,
    condensedPullbackHom_comp_condensedRingObjIsoForgetAb_hom, adicUpperStarRingHom,
    CategoryTheory.Functor.map_inv, Category.assoc, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

section

variable (Λ : Type (u + 1)) [CommRing Λ] {Z Y : Scheme.{u}} (f : Z ⟶ Y)

open Functor.LaxMonoidal in
/-- The identification `f^* (U M) ≅ U (f^* M)` of `sheafComposeForget₂CompUpperStarIso` is
compatible with the tensor products, in terms of the lax monoidal structures `μ` of the
pullbacks and of the underlying abelian sheaf functors `U`. -/
@[reassoc]
lemma μ_upperStar_comp_map_μ_comp_sheafComposeForget₂CompUpperStarIso
    (M N : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) :
    μ (f)^*[Ab.{u + 1}]
        ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M)
        ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj N) ≫
      (f)^*[Ab.{u + 1}].map
        (μ (sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) M N) ≫
      (sheafComposeForget₂CompUpperStarIso Λ f).hom.app (M ⊗ N) =
    ((sheafComposeForget₂CompUpperStarIso Λ f).hom.app M ⊗ₘ
        (sheafComposeForget₂CompUpperStarIso Λ f).hom.app N) ≫
      μ (sheafCompose (Scheme.ProEt.topology Z)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
        ((f)^*[ModuleCat.{u + 1} Λ].obj M) ((f)^*[ModuleCat.{u + 1} Λ].obj N) ≫
      (sheafCompose (Scheme.ProEt.topology Z)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        (μ (f)^*[ModuleCat.{u + 1} Λ] M N) := by
  have h := congrArg (fun k ↦ μ (f)^*[Ab.{u + 1}] _ _ ≫ k ≫
      (sheafCompose (Scheme.ProEt.topology Z)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        (μ (f)^*[ModuleCat.{u + 1} Λ] M N))
    (upperStar_map_μ_comp_sheafComposeForget₂CompUpperStarIso Λ f M N)
  simp only [Category.assoc, ← Functor.map_comp, Functor.Monoidal.δ_μ, Functor.Monoidal.μ_δ_assoc,
    CategoryTheory.Functor.map_id] at h
  exact h

end

/-- The identification `f^* (U M) ≅ U (f^* M)` is linear for the actions of `Λ_Z` on the
condensed pullback `mapMod(f^*) ⋙ comap α_f⁻¹` of the condensed model of `M` and on the
condensed model of `f^*ᵃ M`. -/
lemma condensedModUpperStarIso_linear (M : AdicSheaf l Y) :
    Mod.act (((adicSheafEquivCondensedMod l Y).functor ⋙
        (f)^*[Ab.{u + 1}].mapMod _ ⋙
          Mod.comap (asIso (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).inv).obj
            M).X ≫
        (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).hom.app M.X =
      condensedRingObj (Profinite.padicAlgClRingObj l) Z ◁
          (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).hom.app M.X ≫
        Mod.act (((adicUpperStar l f ⋙ (adicSheafEquivCondensedMod l Z).functor).obj M).X) := by
  change (inv (condensedPullbackHom (Profinite.padicAlgClRingObj l) f) ▷ _ ≫
      Functor.LaxMonoidal.μ (f)^*[Ab.{u + 1}] _ _ ≫
      (f)^*[Ab.{u + 1}].map ((condensedRingObjIsoForgetAb l Y).hom ▷ _ ≫
        Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l Y) (adicConstantSheaf l Y) M.X ≫
        (weilCoefficientsForgetAb l Y).map (Mod.act (A := adicConstantSheaf l Y) M.X))) ≫
      (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).hom.app M.X = _ ≫
    ((condensedRingObjIsoForgetAb l Z).hom ▷ _ ≫
      Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l Z) (adicConstantSheaf l Z)
        ((f)^*[WeilCoefficients.{u} l].obj M.X) ≫
      (weilCoefficientsForgetAb l Z).map (adicUpperStarRingHom l f ▷ _ ≫
        Functor.LaxMonoidal.μ (f)^*[WeilCoefficients.{u} l] (adicConstantSheaf l Y) M.X ≫
        (f)^*[WeilCoefficients.{u} l].map (Mod.act (A := adicConstantSheaf l Y) M.X)))
  have hσ := (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).hom.naturality
    (Mod.act (A := adicConstantSheaf l Y) M.X)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hσ
  simp only [Functor.map_comp, Category.assoc]
  rw [hσ, ← Functor.LaxMonoidal.μ_natural_left_assoc (f)^*[Ab.{u + 1}],
    μ_upperStar_comp_map_μ_comp_sheafComposeForget₂CompUpperStarIso_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc (weilCoefficientsForgetAb l Z),
    ← comp_whiskerRight_assoc (condensedRingObjIsoForgetAb l Z).hom,
    condensedRingObjIsoForgetAb_hom_comp_map_adicUpperStarRingHom, MonoidalCategory.tensorHom_def]
  erw [whisker_exchange_assoc]
  simp only [comp_whiskerRight, Category.assoc]
  rfl

/-- The condensed pullback `mapMod(f^*) ⋙ comap α_f⁻¹` commutes with the condensed models,
through `f^* (U M) ≅ U (f^* M)` on underlying abelian sheaves. -/
noncomputable def condensedModUpperStarIsoAux :
    (adicSheafEquivCondensedMod l Y).functor ⋙ (f)^*[Ab.{u + 1}].mapMod _ ⋙
        Mod.comap (asIso (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).inv ≅
      adicUpperStar l f ⋙ (adicSheafEquivCondensedMod l Z).functor :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk
      ((sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).app M.X)
      (condensedModUpperStarIso_linear l f M))
    (fun g ↦ Mod.hom_ext _ _
      ((sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).hom.naturality
        g.hom))

lemma condensedModUpperStarIsoAux_hom_app_hom (M : AdicSheaf l Y) :
    ((condensedModUpperStarIsoAux l f).hom.app M).hom =
      (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).hom.app M.X :=
  rfl

/-- **The condensed model commutes with pullback**: `E_Y ⋙ f^* ≅ f^*ᵃ ⋙ E_Z`. The condensed
pullback is `mapMod(f^*) ⋙ comap α_f⁻¹` (`CategoryTheory.Mod.extendScalarsIsoComapInv`), and on
underlying abelian sheaves the isomorphism is `f^*(U M) ≅ U(f^* M)`
(`AlgebraicGeometry.ProEtale.sheafComposeForget₂CompUpperStarIso`). -/
noncomputable def condensedModUpperStarIso :
    (adicSheafEquivCondensedMod l Y).functor ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f ≅
      adicUpperStar l f ⋙ (adicSheafEquivCondensedMod l Z).functor :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom (Profinite.padicAlgClRingObj l) f))) ≪≫
    condensedModUpperStarIsoAux l f

/-- The pullback–tensor comparison `f^*ᵃ(M ⊗ N) ≅ f^*ᵃ M ⊗ f^*ᵃ N` of `ℓ`-adic sheaves for the
monoidal tensor products, on the projections: it is the inverse of the tensorator of `f^*`. -/
lemma μ_comp_map_tensorObjπ_comp_adicUpperStarTensorLeftIso (M N : AdicSheaf l Y) :
    Functor.LaxMonoidal.μ (f)^*[WeilCoefficients.{u} l] M.X N.X ≫
        (f)^*[WeilCoefficients.{u} l].map (Mod.tensorObjπ M N) ≫
        ((adicUpperStar l f).map ((Mod.relativeTensorRightIso N).inv.app M) ≫
          (adicUpperStarTensorLeftIso l f N).hom.app M ≫
          (Mod.relativeTensorRightIso ((adicUpperStar l f).obj N)).hom.app
            ((adicUpperStar l f).obj M)).hom =
      Mod.tensorObjπ ((adicUpperStar l f).obj M) ((adicUpperStar l f).obj N) := by
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (f)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l f)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (f)^*ᵃ[l])
  have h := Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicUpperStarRingHom l f)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ f) _ _) M N
  rw [Mod.comp_hom', Mod.comp_hom', adicUpperStar_map_hom, ← Functor.map_comp_assoc,
    Mod.tensorObjπ_relativeTensorRightIso_inv_app]
  erw [reassoc_of% h]
  rw [IsIso.hom_inv_id_assoc]
  exact Mod.tensorπ_relativeTensorRightIso_hom_app _ _

/-- The isomorphism `condensedModUpperStarIso` is the comparison `Ext_{α_f} ≅ comap α_f⁻¹`
followed by `condensedModUpperStarIsoAux`. -/
lemma condensedModUpperStarIso_hom_app (M : AdicSheaf l Y) :
    (condensedModUpperStarIso l f).hom.app M =
      (Mod.extendScalarsIsoComapInv
          (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).hom.app
          (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj M)) ≫
        (condensedModUpperStarIsoAux l f).hom.app M :=
  rfl

-- The rewrites take place in module objects over the heavy condensed coefficient rings.
/-- The key computation behind `condensedModUpperStarIso_tensor`, after precomposition with the
comparison `comap α_f⁻¹ ≅ Ext_{α_f}` and the tensorator of the condensed pullback. -/
lemma condensedModUpperStarIso_tensor_aux (M N : AdicSheaf l Y) :
    ((Mod.extendScalarsIsoComapInv
          (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).inv.app
          (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj M)) ⊗ₘ
        (Mod.extendScalarsIsoComapInv
          (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).inv.app
          (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj N))) ≫
      Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
        ((adicSheafEquivCondensedMod l Y).functor.obj M)
        ((adicSheafEquivCondensedMod l Y).functor.obj N) ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
        (adicSheafEquivCondensedModTensorIso l Y M N).hom ≫
      (condensedModUpperStarIso l f).hom.app (M ⊗ N) ≫
      (adicSheafEquivCondensedMod l Z).functor.map
        ((adicUpperStar l f).map ((Mod.relativeTensorRightIso N).inv.app M) ≫
          (adicUpperStarTensorLeftIso l f N).hom.app M ≫
          (Mod.relativeTensorRightIso ((adicUpperStar l f).obj N)).hom.app
            ((adicUpperStar l f).obj M)) =
    ((condensedModUpperStarIsoAux l f).hom.app M ⊗ₘ
        (condensedModUpperStarIsoAux l f).hom.app N) ≫
      (adicSheafEquivCondensedModTensorIso l Z ((adicUpperStar l f).obj M)
        ((adicUpperStar l f).obj N)).hom := by
  have hμ : Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
        ((adicSheafEquivCondensedMod l Y).functor.obj M)
        ((adicSheafEquivCondensedMod l Y).functor.obj N) =
      Functor.LaxMonoidal.μ
          (Mod.extendScalars (condensedPullbackHom (Profinite.padicAlgClRingObj l) f))
          (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj M))
          (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj N)) ≫
        (Mod.extendScalars (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).map
          (Functor.LaxMonoidal.μ ((f)^*[Ab.{u + 1}].mapMod _)
            ((adicSheafEquivCondensedMod l Y).functor.obj M)
            ((adicSheafEquivCondensedMod l Y).functor.obj N)) :=
    Functor.LaxMonoidal.comp_μ _ _ _ _
  have hext := Functor.Monoidal.transport_μ
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).symm
    (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj M))
    (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj N))
  simp only [Iso.symm_hom, Iso.symm_inv] at hext
  have hc : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
      (adicSheafEquivCondensedModTensorIso l Y M N).hom =
      (Mod.extendScalars (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).map
        (((f)^*[Ab.{u + 1}].mapMod _).map (adicSheafEquivCondensedModTensorIso l Y M N).hom) :=
    rfl
  rw [hμ, hext, hc, condensedModUpperStarIso_hom_app]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app,
    MonoidalCategory.id_tensorHom_id, Category.id_comp, ← NatTrans.naturality_assoc,
    ← NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc]
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.tensorObjπ _ _)]
  simp only [Mod.comp_hom', Mod.comap_map_hom, Functor.mapMod_map_hom, Functor.comp_obj]
  rw [Mod.tensorObjπ_tensorHom_hom_assoc, tensorObjπ_adicSheafEquivCondensedModTensorIso_hom_hom]
  have h₂ : Mod.tensorObjπ
      ((Mod.comap (asIso (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).inv).obj
        (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj M)))
      ((Mod.comap (asIso (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).inv).obj
        (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj N))) ≫
      (Functor.LaxMonoidal.μ
        (Mod.comap (asIso (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).inv)
        (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj M))
        (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj N))).hom =
      Mod.tensorObjπ
        (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj M))
        (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj N)) :=
    Mod.tensorπ_comapTensorIso_hom_hom _ _ _
  have h₃ : Mod.tensorObjπ
      (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj M))
      (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj N)) ≫
      (Functor.LaxMonoidal.μ ((f)^*[Ab.{u + 1}].mapMod _)
        ((adicSheafEquivCondensedMod l Y).functor.obj M)
        ((adicSheafEquivCondensedMod l Y).functor.obj N)).hom =
      Functor.LaxMonoidal.μ (f)^*[Ab.{u + 1}]
          ((adicSheafEquivCondensedMod l Y).functor.obj M).X
          ((adicSheafEquivCondensedMod l Y).functor.obj N).X ≫
        (f)^*[Ab.{u + 1}].map (Mod.tensorObjπ ((adicSheafEquivCondensedMod l Y).functor.obj M)
          ((adicSheafEquivCondensedMod l Y).functor.obj N)) :=
    Functor.tensorπ_mapModTensorIso_hom_hom _ _ _
  have h₄ : Mod.tensorObjπ
      (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj M))
      (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj N)) ≫
      (Functor.LaxMonoidal.μ ((f)^*[Ab.{u + 1}].mapMod _)
        ((adicSheafEquivCondensedMod l Y).functor.obj M)
        ((adicSheafEquivCondensedMod l Y).functor.obj N)).hom ≫
      (f)^*[Ab.{u + 1}].map (adicSheafEquivCondensedModTensorIso l Y M N).hom.hom =
      Functor.LaxMonoidal.μ (f)^*[Ab.{u + 1}]
          ((weilCoefficientsForgetAb l Y).obj M.X) ((weilCoefficientsForgetAb l Y).obj N.X) ≫
        (f)^*[Ab.{u + 1}].map
          (Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l Y) M.X N.X) ≫
        (f)^*[Ab.{u + 1}].map ((weilCoefficientsForgetAb l Y).map (Mod.tensorObjπ M N)) := by
    rw [reassoc_of% h₃, ← Functor.map_comp, ← Functor.map_comp,
      tensorObjπ_adicSheafEquivCondensedModTensorIso_hom_hom]
    rfl
  have hσ := (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).hom.naturality
    (Mod.tensorObjπ M N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hσ
  rw [reassoc_of% h₂]
  rw [reassoc_of% h₄]
  rw [condensedModUpperStarIsoAux_hom_app_hom, condensedModUpperStarIsoAux_hom_app_hom,
    condensedModUpperStarIsoAux_hom_app_hom, reassoc_of% hσ,
    μ_upperStar_comp_map_μ_comp_sheafComposeForget₂CompUpperStarIso_assoc]
  have h₅ : (weilCoefficientsForgetAb l Z).map
        (Functor.LaxMonoidal.μ (f)^*[WeilCoefficients.{u} l] M.X N.X) ≫
      (weilCoefficientsForgetAb l Z).map
        ((f)^*[WeilCoefficients.{u} l].map (Mod.tensorObjπ M N)) ≫
      ((adicSheafEquivCondensedMod l Z).functor.map
        ((adicUpperStar l f).map ((Mod.relativeTensorRightIso N).inv.app M) ≫
          (adicUpperStarTensorLeftIso l f N).hom.app M ≫
          (Mod.relativeTensorRightIso ((adicUpperStar l f).obj N)).hom.app
            ((adicUpperStar l f).obj M))).hom =
      (weilCoefficientsForgetAb l Z).map
        (Mod.tensorObjπ ((adicUpperStar l f).obj M) ((adicUpperStar l f).obj N)) := by
    rw [← μ_comp_map_tensorObjπ_comp_adicUpperStarTensorLeftIso, Functor.map_comp,
      Functor.map_comp]
    rfl
  rw [h₅]
  rfl

/-- The isomorphism `condensedModUpperStarIso` carries the tensorator of the condensed pullback,
followed by the monoidal comparison of the condensed model on `Y`, to the pullback–tensor
comparison of `ℓ`-adic sheaves followed by the monoidal comparison of the condensed model on
`Z`. -/
lemma condensedModUpperStarIso_μ (M N : AdicSheaf l Y) :
    Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
        ((adicSheafEquivCondensedMod l Y).functor.obj M)
        ((adicSheafEquivCondensedMod l Y).functor.obj N) ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
        (adicSheafEquivCondensedModTensorIso l Y M N).hom ≫
      (condensedModUpperStarIso l f).hom.app (M ⊗ N) ≫
      (adicSheafEquivCondensedMod l Z).functor.map
        ((adicUpperStar l f).map ((Mod.relativeTensorRightIso N).inv.app M) ≫
          (adicUpperStarTensorLeftIso l f N).hom.app M ≫
          (Mod.relativeTensorRightIso ((adicUpperStar l f).obj N)).hom.app
            ((adicUpperStar l f).obj M)) =
    ((condensedModUpperStarIso l f).hom.app M ⊗ₘ (condensedModUpperStarIso l f).hom.app N) ≫
      (adicSheafEquivCondensedModTensorIso l Z ((adicUpperStar l f).obj M)
        ((adicUpperStar l f).obj N)).hom := by
  rw [← Iso.cancel_iso_inv_left (tensorIso
    ((Mod.extendScalarsIsoComapInv
      (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).app
        (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj M)))
    ((Mod.extendScalarsIsoComapInv
      (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).app
        (((f)^*[Ab.{u + 1}].mapMod _).obj ((adicSheafEquivCondensedMod l Y).functor.obj N))))]
  rw [tensorIso_inv, Iso.app_inv, Iso.app_inv, condensedModUpperStarIso_tensor_aux,
    tensorHom_comp_tensorHom_assoc, condensedModUpperStarIso_hom_app,
    condensedModUpperStarIso_hom_app, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc]

/-- **The condensed model commutes monoidally with pullback.** For `ℓ`-adic sheaves `M`, `N` on
`Y`, the isomorphism `condensedModUpperStarIso` carries the pullback–tensor comparison
`f^*ᵃ(M ⊗ N) ≅ f^*ᵃ M ⊗ f^*ᵃ N` of `ℓ`-adic sheaves (`adicUpperStarTensorLeftIso`, with the
coequalizer tensor identified with the monoidal one by `Mod.relativeTensorRightIso`) to the
comonoidal structure `δ` of the condensed pullback, up to the monoidal comparisons
`adicSheafEquivCondensedModTensorIso` of the condensed models. -/
lemma condensedModUpperStarIso_tensor (M N : AdicSheaf l Y) :
    (condensedModUpperStarIso l f).hom.app ((Mod.tensorLeft N).obj M) ≫
        (adicSheafEquivCondensedMod l Z).functor.map
          ((adicUpperStarTensorLeftIso l f N).hom.app M ≫
            (Mod.relativeTensorRightIso ((adicUpperStar l f).obj N)).hom.app
              ((adicUpperStar l f).obj M)) ≫
        (adicSheafEquivCondensedModTensorIso l Z ((adicUpperStar l f).obj M)
          ((adicUpperStar l f).obj N)).inv =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
          ((adicSheafEquivCondensedMod l Y).functor.map
              ((Mod.relativeTensorRightIso N).hom.app M) ≫
            (adicSheafEquivCondensedModTensorIso l Y M N).inv) ≫
        Functor.OplaxMonoidal.δ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
          ((adicSheafEquivCondensedMod l Y).functor.obj M)
          ((adicSheafEquivCondensedMod l Y).functor.obj N) ≫
        ((condensedModUpperStarIso l f).hom.app M ⊗ₘ (condensedModUpperStarIso l f).hom.app N) := by
  have hnat : ((adicSheafEquivCondensedMod l Y).functor ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
        ((Mod.relativeTensorRightIso N).hom.app M) ≫
        (condensedModUpperStarIso l f).hom.app (M ⊗ N) =
      (condensedModUpperStarIso l f).hom.app ((Mod.tensorLeft N).obj M) ≫
        (adicUpperStar l f ⋙ (adicSheafEquivCondensedMod l Z).functor).map
          ((Mod.relativeTensorRightIso N).hom.app M) :=
    (condensedModUpperStarIso l f).hom.naturality _
  have hθ : (condensedModUpperStarIso l f).hom.app ((Mod.tensorLeft N).obj M) =
      ((adicSheafEquivCondensedMod l Y).functor ⋙
          CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
          ((Mod.relativeTensorRightIso N).hom.app M) ≫
        (condensedModUpperStarIso l f).hom.app (M ⊗ N) ≫
        (adicUpperStar l f ⋙ (adicSheafEquivCondensedMod l Z).functor).map
          ((Mod.relativeTensorRightIso N).inv.app M) := by
    rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hA := condensedModUpperStarIso_μ l f M N
  rw [hθ]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hA ⊢
  congr 1
  rw [← Iso.cancel_iso_hom_left (Functor.Monoidal.μIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
      ((adicSheafEquivCondensedMod l Y).functor.obj M)
      ((adicSheafEquivCondensedMod l Y).functor.obj N) ≪≫
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).mapIso
      (adicSheafEquivCondensedModTensorIso l Y M N))]
  simp only [Iso.trans_hom, Functor.Monoidal.μIso_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% hA, Iso.hom_inv_id, Category.comp_id, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.Monoidal.μ_δ_assoc]

end AlgebraicGeometry.ProEtale
