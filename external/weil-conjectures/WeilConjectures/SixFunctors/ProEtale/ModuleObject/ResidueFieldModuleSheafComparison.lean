/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldModuleSheafEquivalenceUpperLowerStar

/-!
# Residue field module sheaves, pushforward and pullback

For a morphism of schemes `a : A ⟶ B`, regarding `𝔽_{E,X}`-module objects as pro-étale sheaves of
`𝔽_E`-modules (`ProEtale.residueFieldModuleSheaf`) commutes with the pushforward and with the
pullback:

- `ProEtale.residueFieldModuleSheafLowerStarIso`:
  `a_* ⋙ residueFieldModuleSheaf B ≅ residueFieldModuleSheaf A ⋙ a_*`;
- `ProEtale.residueFieldModuleSheafUpperStarIso`:
  `a^* ⋙ residueFieldModuleSheaf A ≅ residueFieldModuleSheaf B ⋙ a^*`.

Both are obtained with `CategoryTheory.Sheaf.isoOfSheafComposeForget₂` from the identifications of
the underlying abelian sheaves (`ProEtale.residueFieldModuleSheafLowerStarForgetIso` and
`ProEtale.residueFieldModuleSheafUpperStarForgetIso`), which commute with the actions of `𝔽_E`
since the coefficient morphisms send constant sections to constant sections
(`ProEtale.sectionActRingHom_lowerStar_residueFieldSectionRingHom` and
`ProEtale.upperStarUnitHom_comp_sectionActRingHom_residueFieldSectionRingHom`).

## Implementation notes

The ring object `Profinite.continuousMapRingObj (integersResidueField ℓ E)` elaborates with the
ring structure of `𝔽_E` coming from its field structure, while the constant sections
(`ProEtale.continuousMapCoefficientSectionRingHom`) use its commutative ring structure. The two
are definitionally equal, but kernel checks comparing the pullback of module objects
(`ProEtale.CondensedRing.upperStar`) along the two forms time out. The comparisons for the
pullback are therefore stated for the commutative-ring form, with a single instance of
`IsTopologicalRing 𝔽_E` (`ProEtale.isTopologicalRing_residueField`), and only the final
isomorphism `ProEtale.residueFieldModuleSheafUpperStarIso` is restated for the usual form, with the
global instance `PadicAlgCl.isTopologicalRing_integersResidueField` used everywhere else.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {A B : Scheme.{u}} (a : A ⟶ B)

variable {ℓ E} in
omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The action of the constant section `c` of `𝔽_{E,B}` on the pushforward `a_* N` is the
pushforward of the action of the constant section `c` of `𝔽_{E,A}` on `N`. -/
lemma sectionActRingHom_lowerStar_residueFieldSectionRingHom
    (N : Mod (Sheaf (ProEt.topology A) Ab.{u + 1}) (residueFieldRingObj A ℓ E))
    (c : ResidueFieldCoeff.{u} ℓ E) :
    (Mod.sectionActRingHom
        ((a)_*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧.obj N)
        (residueFieldSectionRingHom B ℓ E c)).asHom =
      (a)_*[Ab.{u + 1}].map
        (Mod.sectionActRingHom N (residueFieldSectionRingHom A ℓ E c)).asHom := by
  rw [residueFieldSectionRingHom_apply, residueFieldSectionRingHom_apply,
    sectionActRingHom_lowerStar_continuousMapCoefficientSectionRingHom]
  rfl

variable {ℓ E} in
omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The identification `lowerStarForgetIso` intertwines the actions of the constant sections. -/
@[reassoc]
lemma sectionActRingHom_comp_lowerStarForgetIso_inv_app
    (N : Mod (Sheaf (ProEt.topology A) Ab.{u + 1}) (residueFieldRingObj A ℓ E))
    (c : ResidueFieldCoeff.{u} ℓ E) :
    (Mod.sectionActRingHom
        ((a)_*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧.obj N)
        (residueFieldSectionRingHom B ℓ E c)).asHom ≫
      (lowerStarForgetIso (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E))
        a).inv.app N =
    (lowerStarForgetIso (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E))
        a).inv.app N ≫
      (a)_*[Ab.{u + 1}].map
        (Mod.sectionActRingHom N (residueFieldSectionRingHom A ℓ E c)).asHom := by
  rw [sectionActRingHom_lowerStar_residueFieldSectionRingHom, lowerStarForgetIso, Iso.refl_inv,
    NatTrans.id_app]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable (Λ : Type (u + 1)) [CommRing Λ] in
/-- The identification `lowerStarSheafComposeForget₂Iso` intertwines the multiplications by
scalars. -/
@[reassoc]
lemma lowerStar_map_sheafCompose_map_smulEnd_comp_lowerStarSheafComposeForget₂Iso_inv_app
    (F : Sheaf (ProEt.topology A) (ModuleCat.{u + 1} Λ)) (c : Λ) :
    (a)_*[Ab.{u + 1}].map ((sheafCompose (ProEt.topology A)
        (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).map (Sheaf.smulEnd F c)) ≫
      (lowerStarSheafComposeForget₂Iso a Λ).inv.app F =
    (lowerStarSheafComposeForget₂Iso a Λ).inv.app F ≫
      (sheafCompose (ProEt.topology B) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).map
        (Sheaf.smulEnd ((a)_*[ModuleCat.{u + 1} Λ].obj F) c) := by
  rw [← lowerStar_map_smulEnd, Iso.refl_inv, NatTrans.id_app]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable {ℓ E} in
omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The pushforward of the action of the constant section `c` corresponds to the multiplication
by `c` on the pushforward of `residueFieldModuleSheaf A ℓ E`. -/
@[reassoc]
lemma lowerStar_map_sectionActRingHom_comp_residueFieldModuleSheafCompForgetIso_inv_app
    (N : Mod (Sheaf (ProEt.topology A) Ab.{u + 1}) (residueFieldRingObj A ℓ E))
    (c : ResidueFieldCoeff.{u} ℓ E) :
    (a)_*[Ab.{u + 1}].map (Mod.sectionActRingHom N (residueFieldSectionRingHom A ℓ E c)).asHom ≫
      (a)_*[Ab.{u + 1}].map ((residueFieldModuleSheafCompForgetIso A).inv.app N) ≫
        (lowerStarSheafComposeForget₂Iso a (ResidueFieldCoeff.{u} ℓ E)).inv.app
          ((residueFieldModuleSheaf A ℓ E).obj N) =
    (a)_*[Ab.{u + 1}].map ((residueFieldModuleSheafCompForgetIso A).inv.app N) ≫
      (lowerStarSheafComposeForget₂Iso a (ResidueFieldCoeff.{u} ℓ E)).inv.app
          ((residueFieldModuleSheaf A ℓ E).obj N) ≫
        (sheafCompose (ProEt.topology B)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
          (Sheaf.smulEnd ((a)_*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)].obj
            ((residueFieldModuleSheaf A ℓ E).obj N)) c) := by
  rw [← Functor.map_comp_assoc, sectionActRingHom_comp_residueFieldModuleSheafCompForgetIso_inv_app,
    Functor.map_comp, Category.assoc,
    lowerStar_map_sheafCompose_map_smulEnd_comp_lowerStarSheafComposeForget₂Iso_inv_app]

/-- **Pushforward of residue field module sheaves**: regarding `𝔽_{E,X}`-module objects as
pro-étale sheaves of `𝔽_E`-modules commutes with the pushforward along `a : A ⟶ B`. On
underlying abelian sheaves it is `residueFieldModuleSheafLowerStarForgetIso`
(`ProEtale.sheafCompose_map_residueFieldModuleSheafLowerStarIso_hom_app`). -/
noncomputable def residueFieldModuleSheafLowerStarIso :
    (a)_*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧ ⋙
        residueFieldModuleSheaf B ℓ E ≅
      residueFieldModuleSheaf A ℓ E ⋙ (a)_*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)] :=
  Sheaf.isoOfSheafComposeForget₂ (J := ProEt.topology B) (Λ := ResidueFieldCoeff.{u} ℓ E)
    (residueFieldModuleSheafLowerStarForgetIso ℓ E a) fun N c ↦ by
    simp only [residueFieldModuleSheafLowerStarForgetIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
    dsimp only [Functor.comp_obj]
    rewrite [sheafCompose_map_smulEnd_comp_residueFieldModuleSheafCompForgetIso_hom_app_assoc,
      sectionActRingHom_comp_lowerStarForgetIso_inv_app_assoc]
    simp only [lowerStar_map_sectionActRingHom_comp_residueFieldModuleSheafCompForgetIso_inv_app]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- On underlying abelian sheaves, `residueFieldModuleSheafLowerStarIso` is
`residueFieldModuleSheafLowerStarForgetIso`. -/
@[simp]
lemma sheafCompose_map_residueFieldModuleSheafLowerStarIso_hom_app
    (N : Mod (Sheaf (ProEt.topology A) Ab.{u + 1}) (residueFieldRingObj A ℓ E)) :
    (sheafCompose (ProEt.topology B)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
        ((residueFieldModuleSheafLowerStarIso ℓ E a).hom.app N) =
      (residueFieldModuleSheafLowerStarForgetIso ℓ E a).hom.app N :=
  Sheaf.sheafCompose_map_isoOfSheafComposeForget₂_hom_app (J := ProEt.topology B)
    (Λ := ResidueFieldCoeff.{u} ℓ E) _ _ N

/-! ### The pullback -/

section Sections

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [T2Space T]
  [TotallyDisconnectedSpace T] {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- The unit `g^* M ⟶ T_{X'} ⊗_{g^* T_X} g^* M` intertwines the pullback of the action of the
global section given by `f : X → T` with the action of the global section given by `f ∘ g`. -/
@[reassoc]
lemma upperStarUnitHom_comp_sectionActRingHom_continuousMapCoefficientSectionRingHom
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X)) (f : C(X, T)) :
    upperStarUnitHom (Profinite.continuousMapRingObj.{u} T) g M ≫
        (Mod.sectionActRingHom ((g)^*⟦Profinite.continuousMapRingObj.{u} T⟧.obj M)
          (continuousMapCoefficientSectionRingHom X' T (f.comp g.base.hom))).asHom =
      (g)^*[Ab.{u + 1}].map
          (Mod.sectionActRingHom M (continuousMapCoefficientSectionRingHom X T f)).asHom ≫
        upperStarUnitHom (Profinite.continuousMapRingObj.{u} T) g M := by
  change upperStarUnitHom (Profinite.continuousMapRingObj.{u} T) g M ≫
      Mod.sectionAct _ (continuousMapCoefficientSectionRingHom X' T (f.comp g.base.hom)).hom =
    (g)^*[Ab.{u + 1}].map
        (Mod.sectionAct M.X (continuousMapCoefficientSectionRingHom X T f).hom) ≫ _
  rw [← ε_comp_upperStar_map_continuousMapCoefficientSectionRingHom_hom T g f, ← Category.assoc,
    ← Mod.sectionAct_comap, ← Mod.sectionAct_mapMod]
  exact (Mod.sectionAct_comp (Mod.extendUnit (condensedPullbackHom _ g)
    (((g)^*[Ab.{u + 1}].mapMod _).obj M)).hom _).symm

end Sections

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- `𝔽_E` is a topological ring. This restatement of
`PadicAlgCl.isTopologicalRing_integersResidueField` for `E : FiniteIntermediateField ℓ` is used as
a local instance so that all the instances of `IsTopologicalRing 𝔽_E` occurring below are
syntactically equal, which avoids expensive kernel unfoldings. The final isomorphism
`ProEtale.residueFieldModuleSheafUpperStarIso` is stated with the global instance. -/
theorem isTopologicalRing_residueField :
    IsTopologicalRing (integersResidueField ℓ E) :=
  inferInstance

attribute [local instance high] isTopologicalRing_residueField

/- The condensed ring `C(-, 𝔽_E)`, with its ring structure taken through the commutative ring
structure of `𝔽_E` as in `ProEtale.continuousMapCoefficientSectionRingHom`; it is definitionally
`Profinite.continuousMapRingObj (integersResidueField ℓ E)`. -/
set_option hygiene false in
local notation "residueFieldCommRingObj" =>
  @Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E) _ CommRing.toRing _

variable {ℓ E} in
omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The unit `a^* M ⟶ (a^* M)` of the pullback of module objects intertwines the pullback of the
action of the constant section `c` of `𝔽_{E,B}` with the action of the constant section `c`
of `𝔽_{E,A}`. -/
@[reassoc]
lemma upperStarUnitHom_comp_sectionActRingHom_residueFieldSectionRingHom
    (M : Mod (Sheaf (ProEt.topology B) Ab.{u + 1})
      (condensedRingObj (residueFieldCommRingObj) B))
    (c : ResidueFieldCoeff.{u} ℓ E) :
    upperStarUnitHom (residueFieldCommRingObj) a M ≫
        (Mod.sectionActRingHom
          ((a)^*⟦residueFieldCommRingObj⟧.obj M)
          (residueFieldSectionRingHom A ℓ E c)).asHom =
      (a)^*[Ab.{u + 1}].map (Mod.sectionActRingHom M (residueFieldSectionRingHom B ℓ E c)).asHom ≫
        upperStarUnitHom (residueFieldCommRingObj) a M := by
  have h := upperStarUnitHom_comp_sectionActRingHom_continuousMapCoefficientSectionRingHom
    (integersResidueField ℓ E) a M (algebraMap _ _ (ULift.ringEquiv c))
  rw [show (algebraMap (integersResidueField ℓ E) C(B, integersResidueField ℓ E)
      (ULift.ringEquiv c)).comp a.base.hom = algebraMap _ _ (ULift.ringEquiv c) from
    ContinuousMap.ext fun _ ↦ rfl] at h
  rw [residueFieldSectionRingHom_apply, residueFieldSectionRingHom_apply]
  exact h

variable {ℓ E} in
omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The identification `upperStarForgetIso` intertwines the actions of the constant sections. -/
@[reassoc]
lemma sectionActRingHom_comp_upperStarForgetIso_inv_app
    (M : Mod (Sheaf (ProEt.topology B) Ab.{u + 1})
      (condensedRingObj (residueFieldCommRingObj) B))
    (c : ResidueFieldCoeff.{u} ℓ E) :
    (Mod.sectionActRingHom
        ((a)^*⟦residueFieldCommRingObj⟧.obj M)
        (residueFieldSectionRingHom A ℓ E c)).asHom ≫
      (upperStarForgetIso (residueFieldCommRingObj)
        a).inv.app M =
    (upperStarForgetIso (residueFieldCommRingObj) a).inv.app M ≫
      (a)^*[Ab.{u + 1}].map
        (Mod.sectionActRingHom M (residueFieldSectionRingHom B ℓ E c)).asHom := by
  have h := upperStarUnitHom_comp_sectionActRingHom_residueFieldSectionRingHom a M c
  rw [← upperStarForgetIso_hom_app] at h
  rw [← cancel_epi ((upperStarForgetIso
      (residueFieldCommRingObj) a).hom.app M),
    reassoc_of% h, Iso.hom_inv_id_app_assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]

variable (Λ : Type (u + 1)) [CommRing Λ] in
/-- The pullback of the multiplication by `c` is the multiplication by `c`. -/
lemma upperStar_map_smulEnd (F : Sheaf (ProEt.topology B) (ModuleCat.{u + 1} Λ)) (c : Λ) :
    (a)^*[ModuleCat.{u + 1} Λ].map (Sheaf.smulEnd F c) =
      Sheaf.smulEnd ((a)^*[ModuleCat.{u + 1} Λ].obj F) c := by
  apply ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, lowerStar_map_smulEnd]
  exact ((ProEtale.upperStarLowerStarAdjunction _ a).unit.naturality _).symm.trans
    (Sheaf.smulEnd_comp c _)

variable (Λ : Type (u + 1)) [CommRing Λ] in
/-- The identification `sheafComposeForget₂CompUpperStarIso` intertwines the multiplications by
scalars. -/
@[reassoc]
lemma upperStar_map_sheafCompose_map_smulEnd_comp_sheafComposeForget₂CompUpperStarIso_hom_app
    (F : Sheaf (ProEt.topology B) (ModuleCat.{u + 1} Λ)) (c : Λ) :
    (a)^*[Ab.{u + 1}].map ((sheafCompose (ProEt.topology B)
        (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).map (Sheaf.smulEnd F c)) ≫
      (sheafComposeForget₂CompUpperStarIso Λ a).hom.app F =
    (sheafComposeForget₂CompUpperStarIso Λ a).hom.app F ≫
      (sheafCompose (ProEt.topology A) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).map
        (Sheaf.smulEnd ((a)^*[ModuleCat.{u + 1} Λ].obj F) c) := by
  rw [← upperStar_map_smulEnd]
  exact (sheafComposeForget₂CompUpperStarIso Λ a).hom.naturality (Sheaf.smulEnd F c)

variable {ℓ E} in
omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The pullback of the action of the constant section `c` corresponds to the multiplication by
`c` on the pullback of `residueFieldModuleSheaf B ℓ E`. -/
@[reassoc]
lemma upperStar_map_sectionActRingHom_comp_residueFieldModuleSheafCompForgetIso_inv_app
    (M : Mod (Sheaf (ProEt.topology B) Ab.{u + 1})
      (condensedRingObj (residueFieldCommRingObj) B))
    (c : ResidueFieldCoeff.{u} ℓ E) :
    (a)^*[Ab.{u + 1}].map (Mod.sectionActRingHom M (residueFieldSectionRingHom B ℓ E c)).asHom ≫
      (a)^*[Ab.{u + 1}].map ((residueFieldModuleSheafCompForgetIso B).inv.app M) ≫
        (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) a).hom.app
          ((residueFieldModuleSheaf B ℓ E).obj M) =
    (a)^*[Ab.{u + 1}].map ((residueFieldModuleSheafCompForgetIso B).inv.app M) ≫
      (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) a).hom.app
          ((residueFieldModuleSheaf B ℓ E).obj M) ≫
        (sheafCompose (ProEt.topology A)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
          (Sheaf.smulEnd ((a)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)].obj
            ((residueFieldModuleSheaf B ℓ E).obj M)) c) := by
  rw [← Functor.map_comp_assoc, sectionActRingHom_comp_residueFieldModuleSheafCompForgetIso_inv_app,
    Functor.map_comp, Category.assoc,
    upperStar_map_sheafCompose_map_smulEnd_comp_sheafComposeForget₂CompUpperStarIso_hom_app]

/-- The identification of the underlying abelian sheaves of the two composites in
`residueFieldModuleSheafUpperStarIso`. -/
noncomputable def residueFieldModuleSheafUpperStarForgetIso :
    ((a)^*⟦residueFieldCommRingObj⟧ ⋙
        residueFieldModuleSheaf A ℓ E) ⋙ sheafCompose (ProEt.topology A)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1}) ≅
      (residueFieldModuleSheaf B ℓ E ⋙ (a)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]) ⋙
        sheafCompose (ProEt.topology A)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1}) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (residueFieldModuleSheafCompForgetIso A) ≪≫
    (upperStarForgetIso (residueFieldCommRingObj) a).symm ≪≫
    Functor.isoWhiskerRight (residueFieldModuleSheafCompForgetIso B).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafComposeForget₂CompUpperStarIso _ a) ≪≫
    (Functor.associator _ _ _).symm

/-- The isomorphism `residueFieldModuleSheafUpperStarIso`, stated for the commutative-ring form of
`C(-, 𝔽_E)` (see the implementation notes). -/
noncomputable def residueFieldModuleSheafUpperStarIsoAux :
    (a)^*⟦residueFieldCommRingObj⟧ ⋙
        residueFieldModuleSheaf A ℓ E ≅
      residueFieldModuleSheaf B ℓ E ⋙ (a)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)] :=
  Sheaf.isoOfSheafComposeForget₂ (J := ProEt.topology A) (Λ := ResidueFieldCoeff.{u} ℓ E)
    (residueFieldModuleSheafUpperStarForgetIso ℓ E a) fun M c ↦ by
    simp only [residueFieldModuleSheafUpperStarForgetIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
    dsimp only [Functor.comp_obj]
    rewrite [sheafCompose_map_smulEnd_comp_residueFieldModuleSheafCompForgetIso_hom_app_assoc,
      sectionActRingHom_comp_upperStarForgetIso_inv_app_assoc]
    simp only [upperStar_map_sectionActRingHom_comp_residueFieldModuleSheafCompForgetIso_inv_app]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- On underlying abelian sheaves, `residueFieldModuleSheafUpperStarIsoAux` is
`residueFieldModuleSheafUpperStarForgetIso`. -/
@[simp]
lemma sheafCompose_map_residueFieldModuleSheafUpperStarIsoAux_hom_app
    (M : Mod (Sheaf (ProEt.topology B) Ab.{u + 1})
      (condensedRingObj (residueFieldCommRingObj) B)) :
    (sheafCompose (ProEt.topology A)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
        ((residueFieldModuleSheafUpperStarIsoAux ℓ E a).hom.app M) =
      (residueFieldModuleSheafUpperStarForgetIso ℓ E a).hom.app M :=
  Sheaf.sheafCompose_map_isoOfSheafComposeForget₂_hom_app (J := ProEt.topology A)
    (Λ := ResidueFieldCoeff.{u} ℓ E) _ _ M

/-- **Pullback of residue field module sheaves**: regarding `𝔽_{E,X}`-module objects as
pro-étale sheaves of `𝔽_E`-modules commutes with the pullback along `a : A ⟶ B`. On
underlying abelian sheaves it is `residueFieldModuleSheafUpperStarForgetIso`
(`ProEtale.sheafCompose_map_residueFieldModuleSheafUpperStarIsoAux_hom_app`). -/
noncomputable def residueFieldModuleSheafUpperStarIso :
    (a)^*⟦@Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E) _ _
        (PadicAlgCl.isTopologicalRing_integersResidueField ℓ E)⟧ ⋙
        residueFieldModuleSheaf A ℓ E ≅
      residueFieldModuleSheaf B ℓ E ⋙ (a)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)] :=
  residueFieldModuleSheafUpperStarIsoAux ℓ E a

end AlgebraicGeometry.ProEtale
