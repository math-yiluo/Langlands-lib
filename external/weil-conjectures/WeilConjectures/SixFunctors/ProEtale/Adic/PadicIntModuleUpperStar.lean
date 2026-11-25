/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafPadicIntExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-!
# Pullback of `ℤ_ℓ,X`-modules along weakly étale morphisms

For a weakly étale `g : W ⟶ X`, the pullback `g^*` of abelian sheaves is the restriction along
the localization functor `W_proét ⥤ X_proét`, which sends `ℤ_ℓ,X` to `ℤ_ℓ,W`; the comparison
`g^* ℤ_ℓ,X ≅ ℤ_ℓ,W` is a morphism of ring objects
(`AlgebraicGeometry.ProEtale.isMonHom_upperStarPadicIntAbSheafHom`). This gives the pullback
of `ℤ_ℓ`-modules `AlgebraicGeometry.ProEtale.padicIntModUpperStar`, left adjoint to the
pushforward `AlgebraicGeometry.ProEtale.padicIntModLowerStar`.

Restriction of scalars from `ℓ`-adic sheaves to `ℤ_ℓ`-modules commutes with the pushforwards
(`AlgebraicGeometry.ProEtale.adicLowerStarRestrictPadicIntIso`): the inclusions `ℤ_ℓ ⟶ ℚ̄_ℓ` are
compatible with the comparisons `ℤ_ℓ,X ⟶ g_* ℤ_ℓ,W` and `ℚ̄_ℓ,X ⟶ g_* ℚ̄_ℓ,W`, as one checks on
sections. Taking conjugates, **extension of scalars commutes with the pullback**
(`AlgebraicGeometry.ProEtale.padicIntModUpperStarCompAdicSheafExtendScalarsIso`):
`g^* (ℚ̄_ℓ ⊗ M) ≅ ℚ̄_ℓ ⊗ g^* M`. Finally the extension of scalars of `ℤ_ℓ,W` is `ℚ̄_ℓ,W`
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsRegularIso`), from the general
`CategoryTheory.Mod.extendScalarsObjRegularIso` (`S ⊗_R R ≅ S`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped Obj

namespace CategoryTheory

namespace Mod

variable {C : Type*} [Category* C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

/-- `φ : R ⟶ S` as an `R`-linear map from the regular `R`-module to `S`. -/
noncomputable def regularHomComap : regular R ⟶ (comap φ).obj (regular S) :=
  homMk φ (by
    rw [act_comap_obj, ← Category.assoc]
    exact (IsMonHom.mul_hom (f := φ)).trans (by
      rw [tensorHom_def']
      rfl))

/-- **Extension of scalars of the regular module**: `S ⊗_R R ≅ S`. -/
noncomputable def extendScalarsObjRegularIso : extendScalarsObj φ (regular R) ≅ regular S where
  hom := extendHom φ (regularHomComap φ)
  inv := regularLift _ (η[R] ≫ extendUnitHom φ (regular R))
  hom_inv_id := by
    refine extendScalarsObj_hom_ext φ ?_
    have h : φ ≫ (regularLift _ (η[R] ≫ extendUnitHom φ (regular R))).hom =
        extendUnitHom φ (regular R) := by
      rw [regularLift, homMk_hom]
      rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, whiskerLeft_comp_assoc,
        whiskerLeft_extendUnitHom_smul, ← smul_extendUnitHom]
      erw [MonObj.mul_one_assoc]
      rw [Iso.inv_hom_id_assoc]
    rw [comp_hom', extendπ_extendHom_assoc, regularHomComap, homMk_hom]
    erw [act_hom]
    rw [← whiskerLeft_comp_assoc, h, whiskerLeft_extendUnitHom_smul']
    exact (Category.comp_id _).symm
  inv_hom_id := by
    refine regular_hom_ext ?_
    rw [comp_hom', ← Category.assoc, one_comp_regularLift, Category.assoc,
      extendUnitHom_extendHom, regularHomComap, homMk_hom]
    exact (IsMonHom.one_hom (f := φ)).trans (Category.comp_id _).symm

end Mod

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The inclusion `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` of ring objects is, sectionwise, the inclusion of the
continuous functions to `ℤ_ℓ` into the locally finite functions to `ℚ̄_ℓ`. -/
lemma padicIntSheafToAdicConstantSheaf_eq :
    padicIntSheafToAdicConstantSheaf X l = integralToAdicConstantSheaf X l := by
  have hpq : Functor.whiskerRight
      (continuousMapRingPresheafToPadicAlgCl X l (padicIntToPadicAlgCl l)
      (continuous_padicIntToPadicAlgCl l)
      ⟨⊥, inferInstance, fun t ↦ IntermediateField.algebraMap_mem ⊥ (t : ℚ_[l])⟩)
        (forget₂ RingCat.{u + 1} Ab.{u + 1}) ≫ padicAlgClPresheafToAdicConstantSheaf X l =
      (sheafToPresheaf _ _).map (integralToAdicConstantSheaf X l) := by
    ext U x
    rfl
  rw [padicIntSheafToAdicConstantSheaf, padicIntSheafToPadicAlgClSheaf,
    continuousMapRingSheafToPadicAlgClSheaf, Sheaf.sheafComposeToSheafify,
    padicAlgClSheafToAdicConstantSheaf, Adjunction.homEquiv_counit, Category.assoc,
    ← Functor.map_comp_assoc, hpq]
  erw [(sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).counit.naturality]
  rw [Sheaf.sheafifyRingPresheafIso, asIso_inv, IsIso.inv_hom_id_assoc, Functor.id_map]

variable {X} {W : Scheme.{u}} (g : W ⟶ X) [h : WeaklyEtale g]

/-- For a weakly étale `g : W ⟶ X`, the comparison `g^* ℤ_ℓ,X ≅ ℤ_ℓ,W`: the pullback is the
restriction along the localization functor, under which `ℤ_ℓ,X` restricts to `ℤ_ℓ,W`. -/
noncomputable def upperStarPadicIntAbSheafHom :
    (g)^*[Ab.{u + 1}].obj (padicIntAbSheaf X l) ⟶ padicIntAbSheaf W l :=
  (upperStarIsoLocalizationRestriction Ab.{u + 1} g h).hom.app (padicIntAbSheaf X l)

/-- The comparison `g^* ℤ_ℓ,X ⟶ ℤ_ℓ,W` is an isomorphism. -/
instance : IsIso (upperStarPadicIntAbSheafHom l g) := by
  unfold upperStarPadicIntAbSheafHom
  infer_instance

/-- The comparison `g^* ℤ_ℓ,X ≅ ℤ_ℓ,W` is a morphism of ring objects. -/
instance isMonHom_upperStarPadicIntAbSheafHom :
    IsMonHom (upperStarPadicIntAbSheafHom l g) := by
  have := NatTrans.isMonHom_app (upperStarIsoSheafPushforward Ab.{u + 1} g h).hom
    (padicIntAbSheaf X l)
  exact IsMonHom.of_eq (hf := this) _ rfl
    (Sheaf.monObjObj_sheafPushforwardContinuous_eq (MorphismProperty.Over.map ⊤ h)
      (padicIntSheaf X l))

/-- The morphism of ring objects `ℤ_ℓ,X ⟶ g_* ℤ_ℓ,W` adjoint to `g^* ℤ_ℓ,X ≅ ℤ_ℓ,W`. -/
noncomputable def padicIntAbSheafToLowerStar :
    padicIntAbSheaf X l ⟶ (g)_*[Ab.{u + 1}].obj (padicIntAbSheaf W l) :=
  (upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _ (upperStarPadicIntAbSheafHom l g)

/-- The comparison `ℤ_ℓ,X ⟶ g_* ℤ_ℓ,W` is a morphism of ring objects. -/
instance : IsMonHom (padicIntAbSheafToLowerStar l g) := by
  rw [padicIntAbSheafToLowerStar, Adjunction.homEquiv_unit]
  have : IsMonHom ((upperStarLowerStarAdjunction Ab.{u + 1} g).unitAlgHom (padicIntAbSheaf X l)) :=
    inferInstance
  have : IsMonHom ((g)_*[Ab.{u + 1}].map (upperStarPadicIntAbSheafHom l g)) := inferInstance
  exact CategoryTheory.instIsMonHomComp _ _

/-- The adjoint `g^* ℤ_ℓ,X ⟶ ℤ_ℓ,W` of `ℤ_ℓ,X ⟶ g_* ℤ_ℓ,W` is an isomorphism. -/
instance : IsIso (((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).symm
    (padicIntAbSheafToLowerStar l g)) := by
  rw [padicIntAbSheafToLowerStar, Equiv.symm_apply_apply]
  infer_instance

/-- The adjoint `g^* ℤ_ℓ,X ⟶ ℤ_ℓ,W` of `ℤ_ℓ,X ⟶ g_* ℤ_ℓ,W` is a morphism of ring objects. -/
instance : IsMonHom (((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).symm
    (padicIntAbSheafToLowerStar l g)) := by
  rw [padicIntAbSheafToLowerStar, Equiv.symm_apply_apply]
  infer_instance

/-- The pullback `g^*` of `ℤ_ℓ`-modules along a weakly étale `g : W ⟶ X`: the pullback of the
underlying abelian sheaf, a module over `ℤ_ℓ,W ≅ g^* ℤ_ℓ,X`. -/
noncomputable def padicIntModUpperStar :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l) ⥤
      Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (padicIntAbSheaf W l) :=
  (upperStarLowerStarAdjunction Ab.{u + 1} g).modLeft (padicIntAbSheafToLowerStar l g)

/-- The pushforward `g_*` of `ℤ_ℓ`-modules along a weakly étale `g : W ⟶ X`. -/
noncomputable def padicIntModLowerStar :
    Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (padicIntAbSheaf W l) ⥤
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l) :=
  (upperStarLowerStarAdjunction Ab.{u + 1} g).modRight (padicIntAbSheafToLowerStar l g)

/-- The adjunction `g^* ⊣ g_*` on `ℤ_ℓ`-modules. -/
noncomputable def padicIntModUpperStarLowerStarAdjunction :
    padicIntModUpperStar l g ⊣ padicIntModLowerStar l g :=
  (upperStarLowerStarAdjunction Ab.{u + 1} g).modAdjunction _

/-- The morphism `ℤ_ℓ,X ⟶ g_* ℤ_ℓ,W` is the unit of the adjunction between the restriction along
the localization functor and the pushforward. -/
lemma padicIntAbSheafToLowerStar_eq :
    padicIntAbSheafToLowerStar l g =
      (localizationRestrictionLowerStarAdjunction Ab.{u + 1} g h).unit.app _ := by
  rw [padicIntAbSheafToLowerStar, Adjunction.homEquiv_unit, upperStarPadicIntAbSheafHom]
  exact Adjunction.unit_leftAdjointUniq_hom_app _ _ _

/-- The inclusions `ℤ_ℓ ⟶ ℚ̄_ℓ` on `X` and on `W` are compatible with the comparisons
`ℤ_ℓ,X ⟶ g_* ℤ_ℓ,W` and `ℚ̄_ℓ,X ⟶ g_* ℚ̄_ℓ,W`. -/
lemma padicIntSheafToAdicConstantSheaf_comp_map_adicConstantSheafToLowerStar :
    padicIntSheafToAdicConstantSheaf X l ≫
        (weilCoefficientsForgetAb l X).map (adicConstantSheafToLowerStar l g) =
      padicIntAbSheafToLowerStar l g ≫
        (g)_*[Ab.{u + 1}].map (padicIntSheafToAdicConstantSheaf W l) := by
  rw [padicIntAbSheafToLowerStar_eq, padicIntSheafToAdicConstantSheaf_eq,
    padicIntSheafToAdicConstantSheaf_eq]
  ext U x
  rfl

/-- The pushforward of sheaves of `ℚ̄_ℓ`-modules commutes with the forgetful functor to abelian
sheaves, strictly. -/
noncomputable abbrev lowerStarCompWeilCoefficientsForgetAbIso :
    (g)_*[WeilCoefficients.{u} l] ⋙ weilCoefficientsForgetAb l X ≅
      weilCoefficientsForgetAb l W ⋙ (g)_*[Ab.{u + 1}] :=
  Iso.refl _

/-- The identification `g_* ⋙ forget = forget ⋙ g_*` is monoidal. -/
instance : NatTrans.IsMonoidal (lowerStarCompWeilCoefficientsForgetAbIso l g).hom :=
  Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ProEt.topology X) (ProEt.topology W)
    (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})

/-- The restriction of scalars to `ℤ_ℓ,X` of the pushforward of an `ℓ`-adic sheaf, as the
`mapMod` of the composite `g_* ⋙ forget` followed by a restriction of scalars. -/
noncomputable def adicLowerStarCompRestrictPadicIntIso :
    (g)_*ᵃ[l] ⋙ AdicSheaf.restrictPadicInt X l ≅
      (weilCoefficientsForgetAb l W ⋙ (g)_*[Ab.{u + 1}]).mapMod (adicConstantSheaf l W) ⋙
        Mod.comap (padicIntSheafToAdicConstantSheaf X l ≫
          (weilCoefficientsForgetAb l X).map (adicConstantSheafToLowerStar l g) ≫
            Functor.compAlgHom (g)_*[WeilCoefficients.{u} l] (weilCoefficientsForgetAb l X)
              (lowerStarCompWeilCoefficientsForgetAbIso l g).hom (adicConstantSheaf l W)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((weilCoefficientsForgetAb l X).mapModComapIso (adicConstantSheafToLowerStar l g)) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso _ _
      (lowerStarCompWeilCoefficientsForgetAbIso l g).hom (adicConstantSheaf l W)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Mod.comapComp _ _).symm _ ≪≫ (Mod.comapComp _ _).symm)

/-- The pushforward of the restriction of scalars to `ℤ_ℓ,W` of an `ℓ`-adic sheaf, as the
`mapMod` of the composite `forget ⋙ g_*` followed by a restriction of scalars. -/
noncomputable def restrictPadicIntCompPadicIntModLowerStarIso :
    AdicSheaf.restrictPadicInt W l ⋙ padicIntModLowerStar l g ≅
      (weilCoefficientsForgetAb l W ⋙ (g)_*[Ab.{u + 1}]).mapMod (adicConstantSheaf l W) ⋙
        Mod.comap (padicIntAbSheafToLowerStar l g ≫
          (g)_*[Ab.{u + 1}].map (padicIntSheafToAdicConstantSheaf W l) ≫
            Functor.compAlgHom (weilCoefficientsForgetAb l W) (g)_*[Ab.{u + 1}]
              (𝟙 (weilCoefficientsForgetAb l W ⋙ (g)_*[Ab.{u + 1}])) (adicConstantSheaf l W)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((g)_*[Ab.{u + 1}].mapModComapIso (padicIntSheafToAdicConstantSheaf W l)) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso _ _
      (𝟙 (weilCoefficientsForgetAb l W ⋙ (g)_*[Ab.{u + 1}])) (adicConstantSheaf l W)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Mod.comapComp _ _).symm _ ≪≫ (Mod.comapComp _ _).symm)

/-- **Restriction of scalars commutes with the pushforward**: for a weakly étale `g : W ⟶ X`,
restricting the scalars of `g_* F` to `ℤ_ℓ,X` is pushing forward `F` with its scalars restricted
to `ℤ_ℓ,W`. -/
noncomputable def adicLowerStarRestrictPadicIntIso :
    (g)_*ᵃ[l] ⋙ AdicSheaf.restrictPadicInt X l ≅
      AdicSheaf.restrictPadicInt W l ⋙ padicIntModLowerStar l g :=
  adicLowerStarCompRestrictPadicIntIso l g ≪≫ Functor.isoWhiskerLeft _ (Mod.comapCongr (by
    simp only [Functor.compAlgHom, Iso.refl_hom, NatTrans.id_app]
    exact padicIntSheafToAdicConstantSheaf_comp_map_adicConstantSheafToLowerStar l g)) ≪≫
    (restrictPadicIntCompPadicIntModLowerStarIso l g).symm

/-- **Extension of scalars commutes with the pullback**: for a weakly étale `g : W ⟶ X` and a
`ℤ_ℓ,X`-module `M`, `g^* (ℚ̄_ℓ ⊗ M) ≅ ℚ̄_ℓ ⊗ g^* M`. This is the conjugate of
`AlgebraicGeometry.ProEtale.adicLowerStarRestrictPadicIntIso`. -/
noncomputable def padicIntModUpperStarCompAdicSheafExtendScalarsIso :
    padicIntModUpperStar l g ⋙ adicSheafExtendScalars W l ≅
      adicSheafExtendScalars X l ⋙ (g)^*ᵃ[l] :=
  Adjunction.pullIsoOfComapIso (adicSheafExtendScalarsRestrictAdjunction W l)
    (adicSheafExtendScalarsRestrictAdjunction X l) (padicIntModUpperStarLowerStarAdjunction l g)
    (adicUpperStarLowerStarAdjunction l g) (adicLowerStarRestrictPadicIntIso l g)

variable (W) in
/-- **The extension of scalars of `ℤ_ℓ,W` is `ℚ̄_ℓ,W`**: `ℚ̄_ℓ ⊗_{ℤ_ℓ} ℤ_ℓ,W ≅ ℚ̄_ℓ,W`. -/
noncomputable def adicSheafExtendScalarsRegularIso :
    (adicSheafExtendScalars W l).obj (Mod.regular (padicIntAbSheaf W l)) ≅ AdicSheaf.unit l W :=
  (Mod.extendScalars (freePadicIntSheafToAdicConstantSheaf W l)).mapIso
      ((weilCoefficientsFree W l).mapModRegularIso _) ≪≫
    Mod.extendScalarsObjRegularIso _

end AlgebraicGeometry.ProEtale
