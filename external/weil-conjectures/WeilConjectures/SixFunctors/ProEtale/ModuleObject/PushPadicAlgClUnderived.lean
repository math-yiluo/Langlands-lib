/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClColimit

/-!
# Pushforward commutes with `ℚ̄_ℓ ⊗_E -`, given the finite stages

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, and `f : X ⟶ Y` a quasi-compact
quasi-separated morphism of schemes. For an `E_X`-module object `M`:

* `ℚ̄_ℓ,X ⊗_{E_X} M = colim_{F ⊇ E} F_X ⊗_{E_X} M` as abelian sheaves
  (`AlgebraicGeometry.ProEtale.isColimitPadicAlgClExtendScalarsCocone`), since
  `ℚ̄_ℓ,X = colim_F F_X` (`AlgebraicGeometry.ProEtale.isColimitPadicAlgClRingObjCocone`);
* the underived comparisons (Push) for `E ⊆ F` and `E ⊆ ℚ̄_ℓ` are compatible with the maps
  `F_X ⊗_{E_X} M ⟶ ℚ̄_ℓ,X ⊗_{E_X} M`
  (`ProEtale.CondensedRing.extendChangeHom_comp_pushHom_app`);
* hence, `f_*` commuting with filtered colimits, (Push) for `E ⊆ ℚ̄_ℓ` is an isomorphism at `M` as
  soon as (Push) for every finite `F ⊇ E` is
  (`ProEtale.CondensedRing.isIso_pushHom_padicSubfieldRingObjToPadicAlgCl_app`);
* and the underlying abelian sheaf of `ℚ̄_ℓ,X ⊗_{E_X} M` is `f_*`-acyclic as soon as those of all
  the `F_X ⊗_{E_X} M` are (`ProEtale.rightAcyclic_lowerStar_extendScalars_padicAlgCl`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace CondensedRing

section General

variable {Λ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ₁] [IsCommMonObj Λ₁] [MonObj Λ₂] [IsCommMonObj Λ₂] {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [IsCommMonObj Λ₁] in
/-- (Push) is compatible with the units of extension of scalars:
`(f_* M ⟶ Λ₁,Y ⊗ f_* M ⟶ f_*(Λ₁,X ⊗ M)) = f_*(M ⟶ Λ₁,X ⊗ M)`. -/
@[reassoc]
lemma extendUnitHom_comp_pushHom_app_hom (a : Λ ⟶ Λ₁) [IsMonHom a]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.extendUnitHom (coefficientMap a Y) ((f)_*⟦_⟧.obj M) ≫ ((pushHom a f).app M).hom =
      (f)_*[Ab.{u + 1}].map (Mod.extendUnitHom (coefficientMap a X) M) := by
  have h := unit_mateEquiv_symm (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (TwoSquare.mk _ _ _ _ (comapLowerStarIso a f).inv) M
  have h' := congrArg Mod.Hom.hom h
  refine h'.symm.trans ?_
  change (f)_*[Ab.{u + 1}].map _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

omit [IsCommMonObj Λ] [IsCommMonObj Λ₁] [IsCommMonObj Λ₂] in
/-- The components of `comapLowerStarIso` are the identity on underlying abelian sheaves. -/
lemma comapLowerStarIso_inv_app_hom (c : Λ₁ ⟶ Λ₂) [IsMonHom c]
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₂ X)) :
    ((comapLowerStarIso c f).inv.app N).hom = 𝟙 _ := by
  have h := congrArg Mod.Hom.hom ((comapLowerStarIso c f).hom_inv_id_app N)
  have h₁ : ((comapLowerStarIso c f).hom.app N).hom = 𝟙 _ :=
    Mod.comapMapModComapIso_hom_app_hom _ _ _ _ _ _ N
  erw [Mod.comp_hom', h₁, Category.id_comp] at h
  exact h

omit [IsCommMonObj Λ] [IsCommMonObj Λ₁] [IsCommMonObj Λ₂] in
/-- Composing with a component of `comapLowerStarIso` does not change the underlying morphism. -/
@[reassoc (attr := simp)]
lemma comp_comapLowerStarIso_inv_app_hom (c : Λ₁ ⟶ Λ₂) [IsMonHom c]
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₂ X)) {W}
    (g : W ⟶ ((Mod.comap (coefficientMap c X) ⋙ (f)_*⟦Λ₁⟧).obj N).X) :
    g ≫ ((comapLowerStarIso c f).inv.app N).hom = g := by
  rw [comapLowerStarIso_inv_app_hom f c N]
  exact Category.comp_id g

set_option linter.unusedSectionVars false in
-- Omitting `[IsCommMonObj Λ₁]` makes the elaboration of the proof time out.
/-- (Push) is compatible with the change of target ring: for `a = b ≫ c`, the composite
`Λ₁,Y ⊗ f_* M ⟶ Λ₂,Y ⊗ f_* M ⟶ f_*(Λ₂,X ⊗ M)` is
`Λ₁,Y ⊗ f_* M ⟶ f_*(Λ₁,X ⊗ M) ⟶ f_*(Λ₂,X ⊗ M)`. -/
lemma extendChangeHom_comp_pushHom_app (a : Λ ⟶ Λ₂) (b : Λ ⟶ Λ₁) (c : Λ₁ ⟶ Λ₂) [IsMonHom a]
    [IsMonHom b] [IsMonHom c] (hY : coefficientMap b Y ≫ coefficientMap c Y = coefficientMap a Y)
    (hX : coefficientMap b X ≫ coefficientMap c X = coefficientMap a X)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.extendChangeHom (coefficientMap c Y) hY ((f)_*⟦_⟧.obj M) ≫ ((pushHom a f).app M).hom =
      ((pushHom b f).app M).hom ≫
        (f)_*[Ab.{u + 1}].map (Mod.extendChangeHom (coefficientMap c X) hX M) := by
  have key : Mod.extendChange (coefficientMap c Y) hY ((f)_*⟦_⟧.obj M) ≫
      (Mod.comap (coefficientMap c Y)).map ((pushHom a f).app M) =
      (pushHom b f).app M ≫ ((f)_*⟦Λ₁⟧).map (Mod.extendChange (coefficientMap c X) hX M) ≫
        (comapLowerStarIso c f).inv.app _ := by
    refine Mod.extendScalarsObj_hom_ext' ?_
    rw [Mod.comp_hom', Mod.comp_hom', Mod.comp_hom']
    refine Eq.trans ?_ (congrArg (fun k ↦ Mod.extendUnitHom (coefficientMap b Y) ((f)_*⟦_⟧.obj M) ≫
      ((pushHom b f).app M).hom ≫ k) (comp_comapLowerStarIso_inv_app_hom f c _
        ((f)_*⟦Λ₁⟧.map (Mod.extendChange (coefficientMap c X) hX M)).hom)).symm
    change Mod.extendUnitHom _ _ ≫ Mod.extendChangeHom _ hY _ ≫ ((pushHom a f).app M).hom =
      Mod.extendUnitHom _ _ ≫ ((pushHom b f).app M).hom ≫
        (f)_*[Ab.{u + 1}].map (Mod.extendChangeHom _ hX M)
    refine (Mod.extendUnitHom_extendChangeHom_assoc (coefficientMap c Y) hY _ _).trans ?_
    refine (extendUnitHom_comp_pushHom_app_hom f a M).trans ?_
    refine ((f)_*[Ab.{u + 1}].congr_map
      (Mod.extendUnitHom_extendChangeHom (coefficientMap c X) hX M).symm).trans ?_
    rw [Functor.map_comp]
    exact (extendUnitHom_comp_pushHom_app_hom_assoc f b M _).symm
  have h := congrArg Mod.Hom.hom key
  rw [Mod.comp_hom', Mod.comp_hom', Mod.comp_hom'] at h
  exact h.trans (congrArg (fun k ↦ ((pushHom b f).app M).hom ≫ k)
    (comp_comapLowerStarIso_inv_app_hom f c _
      ((f)_*⟦Λ₁⟧.map (Mod.extendChange (coefficientMap c X) hX M)).hom))

end General

end CondensedRing

/-! ### `ℚ̄_ℓ,X ⊗_{E_X} M` as a filtered colimit -/

section Colimit

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The finite subextensions `F ⊇ E`, as a full subcategory of all finite subextensions. -/
abbrev PadicSubfieldAbove : Type :=
  ObjectProperty.FullSubcategory (fun F : PadicAlgCl.FiniteIntermediateField ℓ ↦ E ≤ F)

lemma exists_padicSubfieldAbove (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ G : PadicSubfieldAbove ℓ E, Nonempty (F ⟶ (ObjectProperty.ι _).obj G) :=
  ⟨⟨IsFiltered.max F E, leOfHom (IsFiltered.rightToMax F E)⟩, ⟨IsFiltered.leftToMax F E⟩⟩

instance : IsFiltered (PadicSubfieldAbove ℓ E) :=
  IsFiltered.of_exists_of_isFiltered_of_fullyFaithful (ObjectProperty.ι _)
    (exists_padicSubfieldAbove ℓ E)

instance : (ObjectProperty.ι fun F : PadicAlgCl.FiniteIntermediateField ℓ ↦ E ≤ F).Final :=
  Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ (exists_padicSubfieldAbove ℓ E)

variable (X : Scheme.{u})

/-- The diagram `F ↦ F_X` over the finite subextensions `F ⊇ E`. -/
noncomputable abbrev padicSubfieldAboveRingObjFunctor :
    PadicSubfieldAbove ℓ E ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  ObjectProperty.ι _ ⋙ Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X

noncomputable instance (F : PadicSubfieldAbove ℓ E) :
    MonObj ((padicSubfieldAboveRingObjFunctor ℓ E X).obj F) :=
  inferInstanceAs (MonObj (padicSubfieldRingObj X ℓ F.obj))

instance {F G : PadicSubfieldAbove ℓ E} (g : F ⟶ G) :
    IsMonHom ((padicSubfieldAboveRingObjFunctor ℓ E X).map g) :=
  inferInstanceAs (IsMonHom (padicSubfieldRingObjMap X ℓ (leOfHom ((ObjectProperty.ι _).map g))))

instance (F : PadicSubfieldAbove ℓ E) :
    IsMonHom (padicSubfieldRingObjMap X ℓ F.property ≫ (𝟙 _ :
      padicSubfieldRingObj X ℓ F.obj ⟶ (padicSubfieldAboveRingObjFunctor ℓ E X).obj F)) :=
  inferInstanceAs (IsMonHom (padicSubfieldRingObjMap X ℓ F.property ≫ 𝟙 _))

lemma padicSubfieldRingObjMap_comp_padicSubfieldAboveRingObjFunctor_map
    {F G : PadicSubfieldAbove ℓ E} (g : F ⟶ G) :
    padicSubfieldRingObjMap X ℓ F.property ≫ (padicSubfieldAboveRingObjFunctor ℓ E X).map g =
      padicSubfieldRingObjMap X ℓ G.property := by
  exact (coefficientMap_comp _ _ X).symm

/-- `ℚ̄_ℓ,X = colim_{F ⊇ E} F_X`. -/
noncomputable def isColimitPadicSubfieldAboveRingObjCocone :
    IsColimit (Mod.algCocone (padicSubfieldAboveRingObjFunctor ℓ E X)
      (fun F ↦ padicSubfieldRingObjToPadicAlgCl X ℓ F.obj)
      (fun g ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ
        (leOfHom ((ObjectProperty.ι _).map g)))) :=
  (Functor.Final.isColimitWhiskerEquiv (ObjectProperty.ι _) _).symm
    (isColimitPadicAlgClRingObjCocone X ℓ)

/-- **`ℚ̄_ℓ,X ⊗_{E_X} M = colim_{F ⊇ E} F_X ⊗_{E_X} M`** as abelian sheaves, for every
`E_X`-module `M`. -/
noncomputable def isColimitPadicAlgClExtendScalarsCocone
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :
    IsColimit (Mod.extendScalarsColimitCocone (padicSubfieldAboveRingObjFunctor ℓ E X)
      (fun F ↦ padicSubfieldRingObjMap X ℓ F.property)
      (padicSubfieldRingObjMap_comp_padicSubfieldAboveRingObjFunctor_map ℓ E X) M
      (fun F ↦ padicSubfieldRingObjToPadicAlgCl X ℓ F.obj)
      (fun g ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ
        (leOfHom ((ObjectProperty.ι _).map g)))
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)
      (fun F ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ F.property)) :=
  Mod.isColimitExtendScalarsColimitCocone _ _ _ _ _ _ _ _
    (isColimitPadicSubfieldAboveRingObjCocone ℓ E X)

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The underlying abelian sheaf of `ℚ̄_ℓ,X ⊗_{E_X} M` is `f_*`-acyclic as soon as those of the
`F_X ⊗_{E_X} M`, `F ⊇ E` finite, are. -/
lemma rightAcyclic_lowerStar_extendScalars_padicAlgCl
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (h : ∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (hF : E ≤ F),
      ((f)_*[Ab.{u + 1}]).rightAcyclic
        ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).obj M).X) :
    ((f)_*[Ab.{u + 1}]).rightAcyclic
      ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj M).X :=
  (rightAcyclic_lowerStar_of_isColimit f (isColimitPadicAlgClExtendScalarsCocone ℓ E X M)
    fun F ↦ h F.obj F.property :)

end Colimit

namespace CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}}
  (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- **(Push) for `E ⟶ ℚ̄_ℓ` is an isomorphism at `M` as soon as (Push) for every finite
`F ⊇ E` is**: both sides of `ℚ̄_ℓ,Y ⊗ f_* M ⟶ f_*(ℚ̄_ℓ,X ⊗ M)` are the filtered colimits of the
two sides of the `F_Y ⊗ f_* M ⟶ f_*(F_X ⊗ M)`. -/
theorem isIso_pushHom_padicSubfieldRingObjToPadicAlgCl_app
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (h : ∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (hF : E ≤ F),
      IsIso ((pushHom (Profinite.padicSubfieldRingObjMap ℓ hF) f).app M)) :
    IsIso ((pushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app M) := by
  have := preservesColimitsOfShape_lowerStar f (PadicSubfieldAbove ℓ E)
  let hY := isColimitPadicAlgClExtendScalarsCocone ℓ E Y ((f)_*⟦_⟧.obj M)
  let hX := isColimitOfPreserves (f)_*[Ab.{u + 1}] (isColimitPadicAlgClExtendScalarsCocone ℓ E X M)
  have hτ (F : PadicSubfieldAbove ℓ E) :
      IsIso ((pushHom (Profinite.padicSubfieldRingObjMap ℓ F.property) f).app M).hom :=
    have := h F.obj F.property
    (Mod.forget _).map_isIso ((pushHom (Profinite.padicSubfieldRingObjMap ℓ F.property) f).app M)
  let τ : Mod.extendScalarsColimitDiagram (padicSubfieldAboveRingObjFunctor ℓ E Y)
      (fun F ↦ padicSubfieldRingObjMap Y ℓ F.property)
      (padicSubfieldRingObjMap_comp_padicSubfieldAboveRingObjFunctor_map ℓ E Y)
      ((f)_*⟦_⟧.obj M) ≅
      Mod.extendScalarsColimitDiagram (padicSubfieldAboveRingObjFunctor ℓ E X)
        (fun F ↦ padicSubfieldRingObjMap X ℓ F.property)
        (padicSubfieldRingObjMap_comp_padicSubfieldAboveRingObjFunctor_map ℓ E X) M ⋙
        (f)_*[Ab.{u + 1}] :=
    NatIso.ofComponents
      (fun F ↦ asIso ((pushHom (Profinite.padicSubfieldRingObjMap ℓ F.property) f).app M).hom)
      fun {F G} g ↦ extendChangeHom_comp_pushHom_app f _ _
        (Profinite.padicSubfieldRingObjMap ℓ (leOfHom ((ObjectProperty.ι _).map g)))
        (coefficientMap_comp _ _ Y).symm (coefficientMap_comp _ _ X).symm M
  have heq : ((pushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app M).hom =
      (hY.coconePointsIsoOfNatIso hX τ).hom := hY.hom_ext fun F ↦ by
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact extendChangeHom_comp_pushHom_app f _ _
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F.obj)
      (padicSubfieldRingObjMap_comp_toPadicAlgCl Y ℓ F.property)
      (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ F.property) M
  have : IsIso ((Mod.forget _).map
      ((pushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app M)) := by
    change IsIso ((pushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app M).hom
    rw [heq]
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget _)

end CondensedRing

end AlgebraicGeometry.ProEtale
