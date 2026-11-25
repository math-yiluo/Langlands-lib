/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeProEtale
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedModule
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedLimit
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity

/-!
# The comparison pullback of the sheaf of twisted sections

Let `f : V ⟶ Y` be weakly étale, quasi-compact and quasi-separated and `c` a linear descent
cocycle on the constant sheaf `M_V` of a `Λ`-module. The twisted sections of `c` over the
objects of the small pro-étale site of `Y` form a sheaf of `Λ`-modules
(`AlgebraicGeometry.proEtTwistedModuleSheaf`) whose restriction `ν_*` to the small étale site is
the étale sheaf of twisted sections (`AlgebraicGeometry.twistedModuleSheaf`). The adjoint
`ν^* (twistedModuleSheaf f c) ⟶ proEtTwistedModuleSheaf f c`
(`AlgebraicGeometry.comparisonUpperStarTwistedModuleSheafHom`) is an isomorphism
(`AlgebraicGeometry.isIso_comparisonUpperStarTwistedModuleSheafHom`): it suffices to check this
on the affine pro-étale site, a dense subsite, whose objects are limits `lim Dⱼ` of affine étale
`Y`-schemes. There the sections of `ν^*` are the colimit of the sections over the `Dⱼ`
(`AlgebraicGeometry.ProEtale.isColimit_comparisonUpperStar_mapCocone_of_isAffine`), and so are
the twisted sections: every twisted section over the limit comes from a finite stage
(`AlgebraicGeometry.IsTwistedSection.exists_of_isLimit`), and two twisted sections agreeing on
the limit agree at a finite stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {Y V : Scheme.{u}} (f : V ⟶ Y) {Λ : Type (u + 1)} [CommRing Λ] {M : Type (u + 1)}
  [AddCommGroup M] [Module Λ M] (c : ↥(pullback f f) → M ≃ₗ[Λ] M)


/-- The presheaf of `Λ`-modules of twisted sections of a linear cocycle on the small pro-étale
site of `Y`. -/
noncomputable def proEtTwistedModulePresheaf : Y.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj U := ModuleCat.of Λ (twistedSubmodule f c U.unop.hom)
  map {U U'} g := ModuleCat.ofHom
    { toFun σ := ⟨σ.1 ∘ (pullbackMapRight f g.unop.left (MorphismProperty.Over.w g.unop)).base,
        ((mem_twistedSubmodule f c).1 σ.2).comp g.unop.left (MorphismProperty.Over.w g.unop)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id U := by
    ext σ : 2
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (𝟙 U.unop.left) (Category.id_comp _)).base = σ.1
    rw [pullbackMapRight_id]
    rfl
  map_comp {U U' U''} g g' := by
    ext σ : 2
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (g'.unop.left ≫ g.unop.left) (by
        rw [Category.assoc, MorphismProperty.Over.w g.unop,
          MorphismProperty.Over.w g'.unop])).base =
      (σ.1 ∘ (pullbackMapRight f g.unop.left (MorphismProperty.Over.w g.unop)).base) ∘
        (pullbackMapRight f g'.unop.left (MorphismProperty.Over.w g'.unop)).base
    rw [pullbackMapRight_comp g.unop.left (MorphismProperty.Over.w g.unop) g'.unop.left
      (MorphismProperty.Over.w g'.unop)]
    rfl

lemma proEtTwistedModulePresheaf_map_coe {U U' : Y.ProEt} (g : U' ⟶ U)
    (σ : (proEtTwistedModulePresheaf f c).obj (op U)) :
    ((proEtTwistedModulePresheaf f c).map g.op σ).1 =
      σ.1 ∘ (pullbackMapRight f g.left (MorphismProperty.Over.w g)).base :=
  rfl

/-- The underlying presheaf of sets of `AlgebraicGeometry.proEtTwistedModulePresheaf` is the
presheaf of twisted sections. -/
noncomputable def proEtTwistedModulePresheafCompForgetIso :
    proEtTwistedModulePresheaf f c ⋙ forget (ModuleCat.{u + 1} Λ) ≅
      proEtTwistedSectionsPresheaf f (fun z ↦ c z) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- **The pro-étale sheaf of `Λ`-modules of twisted sections of a linear cocycle.** -/
noncomputable def proEtTwistedModuleSheaf :
    Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ) where
  obj := proEtTwistedModulePresheaf f c
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{u + 1} Λ)),
      Presheaf.isSheaf_of_iso_iff (proEtTwistedModulePresheafCompForgetIso f c)]
    exact isSheaf_proEtTwistedSectionsPresheaf f _



section Comparison

open ProEtale

/-- The étale sheaf of twisted sections is the restriction `ν_*` to the small étale site of the
pro-étale sheaf of twisted sections. -/
noncomputable def twistedModuleSheafIsoComparisonLowerStar :
    twistedModuleSheaf f c ≅
      (comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).obj (proEtTwistedModuleSheaf f c) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

/-- The comparison `ν^* (twistedModuleSheaf f c) ⟶ proEtTwistedModuleSheaf f c`, adjoint to the
identification of the étale twisted sections with `ν_*` of the pro-étale ones. -/
noncomputable def comparisonUpperStarTwistedModuleSheafHom :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj (twistedModuleSheaf f c) ⟶
      proEtTwistedModuleSheaf f c :=
  ((comparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ _).symm
    (twistedModuleSheafIsoComparisonLowerStar f c).hom

/-- The restriction to the small étale site of the comparison is an isomorphism, the unit of
`ν^* ⊣ ν_*` being an isomorphism. -/
lemma isIso_comparisonLowerStar_map_comparisonUpperStarTwistedModuleSheafHom :
    IsIso ((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).map
      (comparisonUpperStarTwistedModuleSheafHom f c)) := by
  have h := ((comparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ _).apply_symm_apply
    (twistedModuleSheafIsoComparisonLowerStar f c).hom
  rw [Adjunction.homEquiv_unit] at h
  have := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} Λ) Y
  have : IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app (twistedModuleSheaf f c) ≫
      (comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).map
        (comparisonUpperStarTwistedModuleSheafHom f c)) := by
    rw [comparisonUpperStarTwistedModuleSheafHom, h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((comparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app (twistedModuleSheaf f c)) _

/-- On étale `Y`-schemes the comparison is bijective. -/
lemma bijective_comparisonUpperStarTwistedModuleSheafHom_app_toProEt (U : Y.Etale) :
    Function.Bijective ((comparisonUpperStarTwistedModuleSheafHom f c).hom.app
      (op ((toProEt Y).obj U))) := by
  have := isIso_comparisonLowerStar_map_comparisonUpperStarTwistedModuleSheafHom f c
  have : IsIso (((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).map
      (comparisonUpperStarTwistedModuleSheafHom f c)).hom.app (op U)) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

/-- **Over a limit of affine étale `Y`-schemes the comparison is bijective.** For
`c₀.pt = lim Kⱼ` with affine étale `Kⱼ`, the sections of `ν^*` over `c₀.pt` are the colimit of
those over the `Kⱼ`, and so are the twisted sections: every twisted section over the limit comes
from a finite stage, and a twisted section over `Kⱼ` vanishing on the limit vanishes on some
`Kₖ`. -/
lemma bijective_comparisonUpperStarTwistedModuleSheafHom_app_of_isLimit [QuasiCompact f]
    [QuasiSeparated f] (hc : IsDescentCocycle f (fun z ↦ c z)) {J : Type u} [SmallCategory J]
    [IsCofiltered J] (K : J ⥤ Y.Etale) [∀ j, IsAffine (K.obj j).left]
    (c₀ : Cone (K ⋙ toProEt Y))
    (hc₀ : IsLimit ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone c₀)) :
    Function.Bijective ((comparisonUpperStarTwistedModuleSheafHom f c).hom.app (op c₀.pt)) := by
  classical
  obtain ⟨hcol⟩ := isColimit_comparisonUpperStar_mapCocone_of_isAffine
    (ModuleCat.{u + 1} Λ) (twistedModuleSheaf f c) K c₀ hc₀
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  -- the underlying limit of schemes
  let D : J ⥤ Scheme.{u} := (K ⋙ toProEt Y) ⋙ Scheme.ProEt.forget Y ⋙ Over.forget Y
  let p (j : J) : D.obj j ⟶ Y := (K.obj j).hom
  have hπ {i j : J} (g : i ⟶ j) : D.map g ≫ p j = p i :=
    MorphismProperty.Over.w (K.map g)
  let C := (Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone c₀
  have hπ' (j : J) : C.π.app j ≫ p j = c₀.pt.hom :=
    MorphismProperty.Over.w (c₀.π.app j)
  have : ∀ j, IsAffine (D.obj j) := fun j ↦ inferInstanceAs (IsAffine (K.obj j).left)
  have : ∀ {i j : J} (g : i ⟶ j), IsAffineHom (D.map g) := fun _ ↦ inferInstance
  have : ∀ j, CompactSpace (D.obj j) := fun j ↦ inferInstanceAs (CompactSpace (K.obj j).left)
  have : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j ↦
    inferInstanceAs (QuasiSeparatedSpace (K.obj j).left)
  have hθ (j : J) := bijective_comparisonUpperStarTwistedModuleSheafHom_app_toProEt f c (K.obj j)
  have hnat (j : J) (a : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
      (twistedModuleSheaf f c)).obj.obj (op ((toProEt Y).obj (K.obj j)))) :
      (comparisonUpperStarTwistedModuleSheafHom f c).hom.app (op c₀.pt)
          (((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
            (twistedModuleSheaf f c)).obj.map (c₀.π.app j).op a) =
        (proEtTwistedModuleSheaf f c).obj.map (c₀.π.app j).op
          ((comparisonUpperStarTwistedModuleSheafHom f c).hom.app _ a) :=
    NatTrans.naturality_apply (comparisonUpperStarTwistedModuleSheafHom f c).hom
      (c₀.π.app j).op a
  refine ⟨(injective_iff_map_eq_zero
    ((comparisonUpperStarTwistedModuleSheafHom f c).hom.app (op c₀.pt)).hom).2 fun x hx ↦ ?_,
    fun τ ↦ ?_⟩
  · obtain ⟨⟨j⟩, a, rfl⟩ := Concrete.isColimit_exists_rep _ hcol x
    have hx' := (hnat j a).symm.trans hx
    set b := (comparisonUpperStarTwistedModuleSheafHom f c).hom.app _ a
    have hb : b.1 ∘ (pullbackMapRight f (C.π.app j) (hπ' j)).base =
        (0 : ↥(pullback f (p j)) → M) ∘ (pullbackMapRight f (C.π.app j) (hπ' j)).base :=
      congrArg Subtype.val hx'
    have hEa : ∀ {i j} (g : i ⟶ j), IsAffineHom
        ((pullbackRightDiagram (D := D) f p hπ).map g) := fun g ↦
      MorphismProperty.of_isPullback (isPullback_pullbackMapRight (f := f) (D.map g) (hπ g)).flip
        inferInstance
    have : ∀ j, CompactSpace ((pullbackRightDiagram (D := D) f p hπ).obj j) :=
      fun j ↦ inferInstanceAs (CompactSpace ↥(pullback f (p j)))
    obtain ⟨j', g, hg⟩ := Scheme.exists_comp_eq_comp_of_isLimit_of_isLocallyConstant
      (isLimitPullbackRightCone f (C := C) (π := p) (hπ := hπ) (π' := c₀.pt.hom)
        (hπ' := hπ') hc₀) (φ₁ := b.1) (φ₂ := 0) b.2.1 (IsLocallyConstant.const 0) hb
    set a' := ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
      (twistedModuleSheaf f c)).obj.map ((toProEt Y).map (K.map g)).op a
    have ha' : (comparisonUpperStarTwistedModuleSheafHom f c).hom.app _ a' = 0 := by
      rw [NatTrans.naturality_apply (comparisonUpperStarTwistedModuleSheafHom f c).hom
        ((toProEt Y).map (K.map g)).op a]
      exact Subtype.ext hg
    have ha'0 : a' = 0 := (injective_iff_map_eq_zero
      ((comparisonUpperStarTwistedModuleSheafHom f c).hom.app _).hom).1 (hθ j').1 a' ha'
    have hw : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
          (twistedModuleSheaf f c)).obj.map (c₀.π.app j).op a =
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
          (twistedModuleSheaf f c)).obj.map (c₀.π.app j').op a' := by
      have hw' : c₀.π.app j' ≫ (toProEt Y).map (K.map g) = c₀.π.app j := c₀.w g
      simp only [a']
      rw [← hw', op_comp, Functor.map_comp]
      rfl
    refine hw.trans ?_
    rw [ha'0, map_zero]
  · obtain ⟨j, σ, hσ, hστ⟩ := IsTwistedSection.exists_of_isLimit hc hc₀
      p hπ c₀.pt.hom hπ' ((mem_twistedSubmodule f c).1 τ.2)
    obtain ⟨a, ha⟩ := (hθ j).2 ⟨σ, hσ⟩
    have ha' : (comparisonUpperStarTwistedModuleSheafHom f c).hom.app
        (op ((K ⋙ toProEt Y).obj j)) a = ⟨σ, hσ⟩ := ha
    refine ⟨((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
      (twistedModuleSheaf f c)).obj.map (c₀.π.app j).op a, ?_⟩
    rw [hnat, ha']
    exact Subtype.ext hστ

/-- **On the affine pro-étale site the comparison is bijective**: an object of the affine
pro-étale site is a cofiltered limit of affine étale `Y`-schemes. -/
lemma bijective_comparisonUpperStarTwistedModuleSheafHom_app_affineProEt [QuasiCompact f]
    [QuasiSeparated f] (hc : IsDescentCocycle f (fun z ↦ c z)) (X : Y.AffineProEt) :
    Function.Bijective ((comparisonUpperStarTwistedModuleSheafHom f c).hom.app
      (op ((AffineProEt.toProEt Y).obj X))) := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := X.prop
  have hEt (j : J) : Etale (t.app j) := (hts j).1.1
  have hAff (j : J) : IsAffine (D.obj j) :=
    MorphismProperty.ofObjectProperty_top_right_iff.mp (hts j).1.2
  have ht (i j : J) (g : i ⟶ j) : D.map g ≫ t.app j = t.app i := by
    rw [t.naturality g]
    simp
  let K : J ⥤ Y.Etale :=
    { obj j := MorphismProperty.Over.mk ⊤ (t.app j) (hEt j)
      map g := MorphismProperty.Over.homMk (D.map g) (ht _ _ g)
      map_id j := MorphismProperty.Over.Hom.ext (D.map_id j)
      map_comp g g' := MorphismProperty.Over.Hom.ext (D.map_comp g g') }
  let c₀ : Cone (K ⋙ toProEt Y) :=
    { pt := (AffineProEt.toProEt Y).obj X
      π :=
        { app j := MorphismProperty.Over.homMk (s.app j) (hts j).2
          naturality j j' g := by
            refine MorphismProperty.Over.Hom.ext ?_
            have := s.naturality g
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
            exact (Category.id_comp _).trans this } }
  have hc₀ : IsLimit ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone c₀) :=
    hs.ofIsoLimit (Cone.ext (Iso.refl _) fun j ↦ (Category.id_comp _).symm)
  have : ∀ j, IsAffine (K.obj j).left := hAff
  exact bijective_comparisonUpperStarTwistedModuleSheafHom_app_of_isLimit f c hc K c₀ hc₀

/-- **The comparison pullback of the étale sheaf of twisted sections is the pro-étale sheaf of
twisted sections**, for a linear descent cocycle along a quasi-compact quasi-separated `f`. -/
theorem isIso_comparisonUpperStarTwistedModuleSheafHom [QuasiCompact f] [QuasiSeparated f]
    (hc : IsDescentCocycle f (fun z ↦ c z)) :
    IsIso (comparisonUpperStarTwistedModuleSheafHom f c) := by
  refine Functor.IsCoverDense.iso_of_restrict_iso (G := AffineProEt.toProEt Y) _ ?_
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_comparisonUpperStarTwistedModuleSheafHom_app_affineProEt f c hc X.unop)

end Comparison

section Map

variable {f c} {M' : Type (u + 1)} [AddCommGroup M'] [Module Λ M']
  {c' : ↥(pullback f f) → M' ≃ₗ[Λ] M'} (φ : M →ₗ[Λ] M') (hφ : ∀ z m, φ (c z m) = c' z (φ m))

/-- An equivariant linear map of linear cocycles maps twisted sections to twisted sections. -/
noncomputable def twistedSubmoduleMap {T : Scheme.{u}} (π : T ⟶ Y) :
    twistedSubmodule f c π →ₗ[Λ] twistedSubmodule f c' π where
  toFun σ := ⟨φ ∘ σ.1, (σ.2.1.comp φ), fun w ↦ by
    simp only [Function.comp_apply]
    rw [((mem_twistedSubmodule f c).1 σ.2).2 w, hφ]⟩
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add φ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ ↦ map_smul φ _ _)

lemma coe_twistedSubmoduleMap {T : Scheme.{u}} (π : T ⟶ Y) (σ : twistedSubmodule f c π) :
    (twistedSubmoduleMap φ hφ π σ).1 = φ ∘ σ.1 :=
  rfl

/-- The morphism of étale sheaves of twisted sections induced by an equivariant linear map. -/
noncomputable def twistedModuleSheafMap : twistedModuleSheaf f c ⟶ twistedModuleSheaf f c' :=
  (fullyFaithfulSheafToPresheaf _ _).preimage
    { app U := ModuleCat.ofHom (twistedSubmoduleMap φ hφ U.unop.hom)
      naturality _ _ _ := rfl }

/-- The morphism of pro-étale sheaves of twisted sections induced by an equivariant linear
map. -/
noncomputable def proEtTwistedModuleSheafMap :
    proEtTwistedModuleSheaf f c ⟶ proEtTwistedModuleSheaf f c' :=
  (fullyFaithfulSheafToPresheaf _ _).preimage
    { app U := ModuleCat.ofHom (twistedSubmoduleMap φ hφ U.unop.hom)
      naturality _ _ _ := rfl }

lemma twistedModuleSheafMap_hom_app_apply (U : Y.Etaleᵒᵖ)
    (σ : (twistedModuleSheaf f c).obj.obj U) :
    ((twistedModuleSheafMap φ hφ).hom.app U σ).1 = φ ∘ σ.1 :=
  rfl

lemma proEtTwistedModuleSheafMap_hom_app_apply (U : Y.ProEtᵒᵖ)
    (σ : (proEtTwistedModuleSheaf f c).obj.obj U) :
    ((proEtTwistedModuleSheafMap φ hφ).hom.app U σ).1 = φ ∘ σ.1 :=
  rfl

/-- **Naturality of the comparison** in equivariant linear maps of cocycles. -/
lemma comparisonUpperStar_map_twistedModuleSheafMap_comp :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).map (twistedModuleSheafMap φ hφ) ≫
        comparisonUpperStarTwistedModuleSheafHom f c' =
      comparisonUpperStarTwistedModuleSheafHom f c ≫ proEtTwistedModuleSheafMap φ hφ := by
  rw [comparisonUpperStarTwistedModuleSheafHom, comparisonUpperStarTwistedModuleSheafHom,
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1

end Map

end AlgebraicGeometry
