/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldModuleSheafEquivalenceLift
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Reduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Constant sections and the pushforward of residue field module objects

This file collects ingredients for comparing `ProEtale.residueFieldModuleSheaf` (an
`𝔽_{E,X}`-module object regarded as a pro-étale sheaf of `𝔽_E`-modules) with the pushforward and
pullback along a morphism of schemes `g : X' ⟶ X`.

## Main results

- `ProEtale.ε_comp_upperStar_map_continuousMapCoefficientSectionRingHom_hom`: for a Hausdorff
  totally disconnected topological ring `T`, the canonical coefficient morphism
  `α_g : g^* T_X ⟶ T_{X'}` sends the global section given by `f : X → T` to the one given by
  `f ∘ g`.
- `ProEtale.continuousMapCoefficientSectionRingHom_hom_comp_condensedPushforwardHom`: the same for
  `η_g : T_X ⟶ g_* T_{X'}`.
- `ProEtale.sectionActRingHom_lowerStar_continuousMapCoefficientSectionRingHom`: the action of the
  section given by `f` on the pushforward `g_* M` of a module object is the pushforward of the
  action of the section given by `f ∘ g`.
- `ProEtale.residueFieldModuleSheafLowerStarForgetIso`: the underlying abelian sheaves of
  `g_* ⋙ residueFieldModuleSheaf` and `residueFieldModuleSheaf ⋙ g_*` agree; a natural isomorphism
  of the sheaves of `𝔽_E`-modules is obtained from it by
  `CategoryTheory.Sheaf.isoOfSheafComposeForget₂` once it is checked to commute with the actions
  of `𝔽_E`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory MonObj Functor.LaxMonoidal

open scoped CategoryTheory.Obj


namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

/-! ### Constant sections and the coefficient morphisms -/

section Sections

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [T2Space T]
  [TotallyDisconnectedSpace T] {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- The pullback of the global section of `T_X` given by a continuous map `f : X → T` is the
global section of `T_{X'}` given by `f ∘ g`. -/
lemma Γ_map_condensedPullbackHom_continuousMapCoefficientSectionRingHom (f : C(X, T)) :
    Γ.map (condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g)
        (Γ.mapFunctor (g)^*[Ab.{u + 1}] (continuousMapCoefficientSectionRingHom X T f)) =
      continuousMapCoefficientSectionRingHom X' T (f.comp g.base.hom) := by
  have sq := upperStar_map_continuousMapComparison_comp_continuousMapPullbackHom g T
  have sq' : (g)^*[Ab.{u + 1}].map (inv (continuousMapComparison X T)) ≫
      condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g =
      continuousMapPullbackHom g T ≫ inv (continuousMapComparison X' T) := by
    rw [← cancel_epi ((g)^*[Ab.{u + 1}].map (continuousMapComparison X T)),
      ← Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, ← Category.assoc, sq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [continuousMapCoefficientSectionRingHom, continuousMapCoefficientSectionRingHom,
    RingHom.comp_apply, RingHom.comp_apply, Γ.mapFunctor_map, Γ.map_map, Γ.map_congr sq',
    ← Γ.map_map, Γ_map_continuousMapPullbackHom_mapFunctor]

/-- The pullback of the global section of `T_X` given by a continuous map `f : X → T` is the
global section of `T_{X'}` given by `f ∘ g`, on morphisms. -/
lemma ε_comp_upperStar_map_continuousMapCoefficientSectionRingHom_hom (f : C(X, T)) :
    ε (g)^*[Ab.{u + 1}] ≫ (g)^*[Ab.{u + 1}].map (continuousMapCoefficientSectionRingHom X T f).hom ≫
        condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g =
      (continuousMapCoefficientSectionRingHom X' T (f.comp g.base.hom)).hom := by
  have h := congr_arg Γ.hom
    (Γ_map_condensedPullbackHom_continuousMapCoefficientSectionRingHom T g f)
  rw [Γ.map_hom, Γ.mapFunctor_hom, Category.assoc] at h
  exact h


/-- The global section of `T_{X}` given by a continuous map `f : X → T`, followed by
`η_g : T_X ⟶ g_* T_{X'}`, is the image under `g_*` of the global section of `T_{X'}` given by
`f ∘ g`. -/
lemma continuousMapCoefficientSectionRingHom_hom_comp_condensedPushforwardHom (f : C(X, T)) :
    (continuousMapCoefficientSectionRingHom X T f).hom ≫
        condensedPushforwardHom (Profinite.continuousMapRingObj.{u} T) g =
      ε (g)_*[Ab.{u + 1}] ≫
        (g)_*[Ab.{u + 1}].map
          (continuousMapCoefficientSectionRingHom X' T (f.comp g.base.hom)).hom := by
  set adj := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g
  have h := ε_comp_upperStar_map_continuousMapCoefficientSectionRingHom_hom T g f
  have h' : (g)^*[Ab.{u + 1}].map (continuousMapCoefficientSectionRingHom X T f).hom ≫
      condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g =
      Functor.OplaxMonoidal.η (g)^*[Ab.{u + 1}] ≫
        (continuousMapCoefficientSectionRingHom X' T (f.comp g.base.hom)).hom := by
    rw [← h, Functor.Monoidal.η_ε_assoc]
  calc _ = adj.homEquiv _ _
        ((g)^*[Ab.{u + 1}].map (continuousMapCoefficientSectionRingHom X T f).hom ≫
          condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g) := by
        have hn := adj.unit.naturality (continuousMapCoefficientSectionRingHom X T f).hom
        simp only [Functor.id_map, Functor.comp_map] at hn
        rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
        rfl
    _ = _ := by
        rw [h', Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
          adj.unit_app_unit_comp_map_η]

/-- The action of the global section given by `f : X → T` on the pushforward of a module object is
the pushforward of the action of the global section given by `f ∘ g`. -/
lemma sectionActRingHom_lowerStar_continuousMapCoefficientSectionRingHom
    (M : Mod (Sheaf (ProEt.topology X') Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X')) (f : C(X, T)) :
    (Mod.sectionActRingHom ((g)_*⟦Profinite.continuousMapRingObj.{u} T⟧.obj M)
        (continuousMapCoefficientSectionRingHom X T f)).asHom =
      (g)_*[Ab.{u + 1}].map (Mod.sectionActRingHom M
        (continuousMapCoefficientSectionRingHom X' T (f.comp g.base.hom))).asHom := by
  change Mod.sectionAct ((Mod.comap _).obj (((g)_*[Ab.{u + 1}].mapMod _).obj M)).X _ = _
  rw [Mod.sectionAct_comap, continuousMapCoefficientSectionRingHom_hom_comp_condensedPushforwardHom,
    Mod.sectionAct_mapMod]
  rfl

end Sections

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {A B : Scheme.{u}} (a : A ⟶ B)

variable {ℓ E} in
omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The constant global section of `𝔽_{E,X}` with value `c` is the global section of the constant
function `c`. -/
lemma residueFieldSectionRingHom_apply (X : Scheme.{u}) (c : ResidueFieldCoeff.{u} ℓ E) :
    residueFieldSectionRingHom X ℓ E c =
      continuousMapCoefficientSectionRingHom X (integersResidueField ℓ E)
        (algebraMap _ _ (ULift.ringEquiv c)) :=
  rfl

/-! ### The pushforward on underlying abelian sheaves -/

variable {ℓ E} in
/-- The underlying abelian sheaf of `residueFieldModuleSheaf X ℓ E` is the underlying sheaf of the
module object. -/
noncomputable abbrev residueFieldModuleSheafCompForgetIso (X : Scheme.{u}) :
    residueFieldModuleSheaf X ℓ E ⋙ sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1}) ≅
      Mod.forget (residueFieldRingObj X ℓ E) :=
  Sheaf.moduleLiftCompIso (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c))

variable {ℓ E} in
omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The identification `residueFieldModuleSheafCompForgetIso` intertwines the multiplication by
`c` with the action of the constant section `c`. -/
@[reassoc]
lemma sheafCompose_map_smulEnd_comp_residueFieldModuleSheafCompForgetIso_hom_app
    (X : Scheme.{u}) (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E))
    (c : ResidueFieldCoeff.{u} ℓ E) :
    (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
        (Sheaf.smulEnd ((residueFieldModuleSheaf X ℓ E).obj N) c) ≫
        (residueFieldModuleSheafCompForgetIso X).hom.app N =
      (residueFieldModuleSheafCompForgetIso X).hom.app N ≫
        (Mod.sectionActRingHom N (residueFieldSectionRingHom X ℓ E c)).asHom :=
  Sheaf.sheafCompose_map_smulEnd_moduleLift_obj_comp_moduleLiftCompIso_hom_app (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c)) N c

variable {ℓ E} in
omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The identification `residueFieldModuleSheafCompForgetIso` intertwines the action of the
constant section `c` with the multiplication by `c`. -/
@[reassoc]
lemma sectionActRingHom_comp_residueFieldModuleSheafCompForgetIso_inv_app
    (X : Scheme.{u}) (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E))
    (c : ResidueFieldCoeff.{u} ℓ E) :
    (Mod.sectionActRingHom N (residueFieldSectionRingHom X ℓ E c)).asHom ≫
        (residueFieldModuleSheafCompForgetIso X).inv.app N =
      (residueFieldModuleSheafCompForgetIso X).inv.app N ≫
        (sheafCompose (ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
          (Sheaf.smulEnd ((residueFieldModuleSheaf X ℓ E).obj N) c) :=
  Sheaf.moduleLiftCompIso_inv_app_comp_sheafCompose_map_smulEnd (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c)) N c

variable (Λ : Type (u + 1)) [CommRing Λ] in
/-- The pushforward of sheaves of `Λ`-modules commutes with taking underlying abelian sheaves. -/
noncomputable abbrev lowerStarSheafComposeForget₂Iso :
    (a)_*[ModuleCat.{u + 1} Λ] ⋙
        sheafCompose (ProEt.topology B) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ≅
      sheafCompose (ProEt.topology A) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ⋙
        (a)_*[Ab.{u + 1}] :=
  Iso.refl _

variable (Λ : Type (u + 1)) [CommRing Λ] in
/-- The pushforward of the multiplication by `c` is the multiplication by `c`. -/
lemma lowerStar_map_smulEnd (F : Sheaf (ProEt.topology A) (ModuleCat.{u + 1} Λ)) (c : Λ) :
    (a)_*[ModuleCat.{u + 1} Λ].map (Sheaf.smulEnd F c) =
      Sheaf.smulEnd ((a)_*[ModuleCat.{u + 1} Λ].obj F) c := by
  ext U x
  rfl

/-- The identification of the underlying abelian sheaves of the two composites in
`residueFieldModuleSheafLowerStarIso`: both are the pushforward of the underlying sheaf. -/
noncomputable def residueFieldModuleSheafLowerStarForgetIso :
    ((a)_*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧ ⋙
        residueFieldModuleSheaf B ℓ E) ⋙ sheafCompose (ProEt.topology B)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1}) ≅
      (residueFieldModuleSheaf A ℓ E ⋙ (a)_*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]) ⋙
        sheafCompose (ProEt.topology B)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1}) := by
  refine Functor.associator _ _ _ ≪≫ ?_
  refine Functor.isoWhiskerLeft _ (residueFieldModuleSheafCompForgetIso B) ≪≫ ?_
  refine (lowerStarForgetIso (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E))
    a).symm ≪≫ ?_
  refine Functor.isoWhiskerRight (residueFieldModuleSheafCompForgetIso A).symm _ ≪≫ ?_
  refine Functor.associator _ _ _ ≪≫ ?_
  exact Functor.isoWhiskerLeft _ (lowerStarSheafComposeForget₂Iso a _).symm ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale
