/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisActionCounit

/-!
# The Galois action of a covering on sections

For weakly étale `s : Y' ⟶ Y` and `g : Y ⟶ X`, the unit transport
`g_* g^* ⟶ (s ≫ g)_* (s ≫ g)^*` of abelian pro-étale sheaves (the unit of `s^* ⊣ s_*` followed
by the composition isomorphisms) is computed on sections: through the identifications
`g^* ≅ j_g^*` with the restrictions along the localization functors, it is the restriction along
`V ×_X Y' ⟶ V ×_X Y` (`AlgebraicGeometry.ProEtale.baseChangeTransport`).

## Main results

- `AlgebraicGeometry.ProEtale.localizationUnitTransport_eq`: the unit transport for the
  restrictions `j^*` is the restriction along `baseChangeTransport`; the computation is carried
  out in the pro-étale sites, through the adjunctions `Over.map ⊣ Over.pullback` and the
  composition isomorphism `Over.pullbackComp`
  (`AlgebraicGeometry.ProEtale.map_unit_comp_pullbackComp_inv_comp_counit`).
- `AlgebraicGeometry.ProEtale.unitTransport_eq_baseChangeTransportSheafHom`: the same for the
  pullbacks `g^*`, by invariance of the unit transport under a change of left adjoints
  (`CategoryTheory.unitTransport_app_leftAdjointUniq`).
- `AlgebraicGeometry.ProEtale.galoisAction_eq_unitTransport`: the action of `σ` on `g_* g^* H`
  for a Galois covering is the unit transport along `ρ σ`, transported along `ρ σ ≫ g = g`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

universe u

/-- The conjugate `j_{s ≫ g}^* ≅ j_g^* ⋙ j_s^*` of the composition isomorphism of
pushforwards, for the restrictions along the localization functors. -/
noncomputable abbrev localizationRestrictionCompConjugate {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y)
    (g : Y ⟶ X) [WeaklyEtale s] [WeaklyEtale g] :
    localizationRestriction AddCommGrpCat.{u + 1} (s ≫ g) inferInstance ≅
      localizationRestriction AddCommGrpCat.{u + 1} g inferInstance ⋙
        localizationRestriction AddCommGrpCat.{u + 1} s inferInstance :=
  ((conjugateIsoEquiv (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1}
    (s ≫ g) inferInstance)
    ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g inferInstance).comp
      (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} s inferInstance))).symm
    (lowerStarComp AddCommGrpCat.{u + 1} s g).symm).symm

/-- The composition isomorphism of base changes is compatible with the counits of
`Over.map ⊣ Over.pullback`. -/
lemma map_pullbackComp_inv_app_comp_counit {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    [WeaklyEtale s] [WeaklyEtale g] (Z : X.ProEt) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (s ≫ g))).map
        ((MorphismProperty.Over.pullbackComp s g).inv.app Z) ≫
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ (s ≫ g) inferInstance
        trivial).counit.app Z =
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ s inferInstance trivial).counit.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj Z)) ≫
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial).counit.app
        Z := by
  rw [← cancel_epi ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (s ≫ g))).map
    ((MorphismProperty.Over.pullbackComp s g).hom.app Z)), ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  refine MorphismProperty.Over.Hom.ext ?_
  simp only [Functor.comp_obj, Functor.id_obj, MorphismProperty.Over.mapPullbackAdj_counit_app,
    MorphismProperty.Over.homMk_hom, Over.homMk_left, MorphismProperty.Comma.comp_hom,
    Comma.comp_left, MorphismProperty.Over.map_map_left,
    MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id, Category.id_comp]
  exact (pullbackLeftPullbackSndIso_inv_fst Z.hom g s).symm

/-- `Over.map` along `s ≫ g` is `Over.map` along `s` followed by `Over.map` along `g`. -/
lemma map_map_comp {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X) [WeaklyEtale s]
    [WeaklyEtale g] {A B : Y'.ProEt} (f : A ⟶ B) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (s ≫ g))).map f =
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).map
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).map f) :=
  rfl

/-- The unit of `Over.map ⊣ Over.pullback` along `s ≫ g`, written through the units along `s`
and `g` and the composition isomorphism of base changes, has the counit as a retraction. -/
lemma map_unit_comp_pullbackComp_inv_comp_counit {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y)
    (g : Y ⟶ X) [WeaklyEtale s] [WeaklyEtale g] (P : Y'.ProEt) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (s ≫ g))).map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ s inferInstance trivial).unit.app P ≫
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).map
          ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial).unit.app
            ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).obj P)) ≫
        (MorphismProperty.Over.pullbackComp s g).inv.app
          ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).obj
            ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).obj P))) ≫
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ (s ≫ g) inferInstance
        trivial).counit.app
          ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).obj
            ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).obj P)) = 𝟙 _ := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    map_pullbackComp_inv_app_comp_counit, map_map_comp, map_map_comp, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  have h := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ s inferInstance
    trivial).counit.naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial).unit.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).obj P))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h
  rw [Category.assoc, h]
  erw [Adjunction.left_triangle_components_assoc, Adjunction.left_triangle_components]
  rfl

-- the pushforwards of sheaves along the localization functors are large terms
/-- **The unit transport along `s` for the restrictions along the localization functors**, on
sections over `V`: it is the restriction along `V ×_X Y' ⟶ V ×_X Y`, the transpose of the
composition isomorphism of base changes. -/
lemma localizationUnitTransport_hom_app {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    [WeaklyEtale s] [WeaklyEtale g] (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
    (V : X.ProEt) :
    ((g)_*[AddCommGrpCat.{u + 1}].map
        ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} s
          inferInstance).unit.app
          ((localizationRestriction AddCommGrpCat.{u + 1} g inferInstance).obj H)) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} s g).hom.app _ ≫
      (s ≫ g)_*[AddCommGrpCat.{u + 1}].map
        ((localizationRestrictionCompConjugate s g).inv.app H)).hom.app (op V) =
      H.obj.map (((MorphismProperty.Over.mapComp (Q := ⊤) (inferInstance : WeaklyEtale s)
        (inferInstance : WeaklyEtale g)).hom.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (s ≫ g)).obj V) ≫
        (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).map
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).map
          ((MorphismProperty.Over.pullbackComp s g).hom.app V) ≫
        (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ s inferInstance trivial).counit.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)))).op := by
  simp only [lowerStar, Functor.sheafPushforwardContinuous, localizationRestriction,
    Functor.id_obj, ObjectProperty.lift_obj_obj, Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.whiskeringLeft_obj_obj, Functor.op_obj, localizationRestrictionLowerStarAdjunction,
    ObjectProperty.lift_map, Functor.comp_map, ObjectProperty.ι_map,
    Functor.whiskeringLeft_obj_map, lowerStarComp, Iso.symm_inv, conjugateIsoEquiv_symm_apply_hom,
    Iso.symm_hom, conjugateEquiv_symm_apply_app, ObjectProperty.homMk_hom,
    Functor.whiskerLeft_twice, Adjunction.comp_counit_app,
    ObjectProperty.FullSubcategory.comp_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.whiskerLeft_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.sheafPushforwardContinuous_unit_app_hom_app, Functor.op_map, Quiver.Hom.unop_op,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Functor.associator_inv_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Functor.associator_hom_app,
    Adjunction.sheafPushforwardContinuous_counit_app_hom_app, Category.id_comp, Functor.map_comp,
    op_comp]
  simp only [← Functor.map_comp, ← op_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (map_unit_comp_pullbackComp_inv_comp_counit s g)]
  refine congrArg (fun f ↦ H.obj.map (Quiver.Hom.op f)) (MorphismProperty.Over.Hom.ext ?_)
  simp only [MorphismProperty.Over.mapPullbackAdj_counit_app, MorphismProperty.Comma.comp_hom,
    Comma.comp_left, MorphismProperty.Over.map_map_left,
    MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id, Category.id_comp,
    MorphismProperty.Over.homMk_hom, Over.homMk_left, MorphismProperty.Over.mapComp_hom_app_left]
  exact (Category.id_comp _).symm

/-- The underlying morphism of `MorphismProperty.Over.homMk`. -/
@[simp]
private lemma overHomMk_left' {X : Scheme.{u}} {A B : X.ProEt} (f : A.left ⟶ B.left)
    (w : f ≫ B.hom = A.hom) (hf : (⊤ : MorphismProperty Scheme.{u}) f) :
    (MorphismProperty.Over.homMk f w hf).left = f :=
  rfl

/-- The underlying morphism of a composite in the pro-étale site. -/
@[simp]
private lemma proEtComp_left' {X : Scheme.{u}} {A B C : X.ProEt} (f : A ⟶ B) (h : B ⟶ C) :
    (f ≫ h).left = f.left ≫ h.left :=
  rfl

/-- The comparison `V ×_X Y' ⟶ V ×_X Y` induced by `s : Y' ⟶ Y` over `X`, for `s ≫ g = p₁`,
natural in `V`; for `p₁ = g` it is `ProEtale.baseChangeAction`. -/
noncomputable def baseChangeTransport {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    [WeaklyEtale g] {p₁ : Y' ⟶ X} [WeaklyEtale p₁] (hp : s ≫ g = p₁) :
    baseChangeFunctor p₁ ⟶ baseChangeFunctor g where
  app V := MorphismProperty.Over.homMk
    (pullback.map V.hom p₁ V.hom g (𝟙 _) s (𝟙 _) (by simp) (by simp [hp])) (by simp [hp])
    trivial
  naturality V W f := by
    refine MorphismProperty.Over.Hom.ext ?_
    apply pullback.hom_ext <;> simp

/-- For `s ≫ g = g`, `baseChangeTransport` is the action `ProEtale.baseChangeAction`. -/
lemma baseChangeTransport_self {X Y : Scheme.{u}} (s : Y ⟶ Y) (g : Y ⟶ X) [WeaklyEtale g]
    (hs : s ≫ g = g) : baseChangeTransport s g hs = baseChangeAction g s hs :=
  rfl

set_option linter.flexible false in
-- the components of the comparison are only reached after normalising with `simp`
/-- The transpose of the composition isomorphism of base changes is the comparison
`baseChangeTransport`. -/
lemma mapComp_hom_app_comp_map_pullbackComp_hom_app {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y)
    (g : Y ⟶ X) [WeaklyEtale s] [WeaklyEtale g] (V : X.ProEt) :
    (MorphismProperty.Over.mapComp (Q := ⊤) (inferInstance : WeaklyEtale s)
        (inferInstance : WeaklyEtale g)).hom.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (s ≫ g)).obj V) ≫
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).map
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).map
          ((MorphismProperty.Over.pullbackComp s g).hom.app V) ≫
        (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ s inferInstance trivial).counit.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)) =
      (baseChangeTransport s g rfl).app V := by
  refine MorphismProperty.Over.Hom.ext ?_
  apply pullback.hom_ext
  · simp [baseChangeTransport]
    exact (Category.id_comp _).trans (pullbackLeftPullbackSndIso_inv_fst V.hom g s)
  · simp [baseChangeTransport]
    exact (Category.id_comp _).trans (pullbackLeftPullbackSndIso_inv_fst_snd V.hom g s)

/-- The morphism `g_* j_g^* H ⟶ p₁_* j_{p₁}^* H` of restriction along `baseChangeTransport`. -/
noncomputable def baseChangeTransportSheafHom {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    [WeaklyEtale g] {p₁ : Y' ⟶ X} [WeaklyEtale p₁] (hp : s ≫ g = p₁)
    (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (g)_*[AddCommGrpCat.{u + 1}].obj
        ((localizationRestriction AddCommGrpCat.{u + 1} g inferInstance).obj H) ⟶
      (p₁)_*[AddCommGrpCat.{u + 1}].obj
        ((localizationRestriction AddCommGrpCat.{u + 1} p₁ inferInstance).obj H) :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op (baseChangeTransport s g hp)) H.obj)

-- the pushforwards of sheaves along the localization functors are large terms
/-- **(a1)** The unit transport along `s` for the restrictions along the localization functors
is the restriction along `baseChangeTransport`. -/
lemma localizationUnitTransport_eq {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    [WeaklyEtale s] [WeaklyEtale g] (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (g)_*[AddCommGrpCat.{u + 1}].map
        ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} s
          inferInstance).unit.app
          ((localizationRestriction AddCommGrpCat.{u + 1} g inferInstance).obj H)) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} s g).hom.app _ ≫
      (s ≫ g)_*[AddCommGrpCat.{u + 1}].map
        ((localizationRestrictionCompConjugate s g).inv.app H) =
      baseChangeTransportSheafHom s g rfl H := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ?_))
  rw [localizationUnitTransport_hom_app, mapComp_hom_app_comp_map_pullbackComp_hom_app]
  rfl

/-- The composition isomorphism `c` obtained from `r` by conjugation has `hom` the inverse
conjugate of `r.hom`. -/
lemma conjugateIsoEquiv_symm_symm_hom {C E : Type*} [Category C] [Category E]
    {L₁ : C ⥤ E} {R₁ : E ⥤ C} {L₂ : C ⥤ E} {R₂ : E ⥤ C} (A : L₁ ⊣ R₁) (B : L₂ ⊣ R₂)
    (r : R₂ ≅ R₁) :
    (((conjugateIsoEquiv A B).symm r.symm).symm).hom = (conjugateEquiv B A).symm r.hom := by
  rw [Equiv.eq_symm_apply]
  exact congrArg Iso.inv ((conjugateIsoEquiv A B).apply_symm_apply r.symm)

-- the pushforwards of sheaves along the localization functors are large terms
/-- **The abelian unit transport along `s`** of `g_* g^*`, transported along `s ≫ g = p₁`, is the
restriction along `baseChangeTransport`, through the identifications `g^* ≅ j_g^*`. -/
theorem unitTransport_eq_baseChangeTransportSheafHom {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y)
    (g : Y ⟶ X) [WeaklyEtale s] [WeaklyEtale g] {p₁ : Y' ⟶ X} [WeaklyEtale p₁]
    (hp : s ≫ g = p₁) (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (g)_*[AddCommGrpCat.{u + 1}].map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} s).unit.app
          ((g)^*[AddCommGrpCat.{u + 1}].obj H)) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} s g).hom.app _ ≫
      (s ≫ g)_*[AddCommGrpCat.{u + 1}].map
        ((upperStarComp AddCommGrpCat.{u + 1} s g).inv.app H) ≫ eqToHom (by rw [hp]) =
      (g)_*[AddCommGrpCat.{u + 1}].map
          ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g inferInstance).hom.app
            H) ≫
        baseChangeTransportSheafHom s g hp H ≫
        (p₁)_*[AddCommGrpCat.{u + 1}].map
          ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} p₁ inferInstance).inv.app
            H) := by
  subst hp
  have hc := conjugateIsoEquiv_symm_symm_hom
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (s ≫ g))
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} s))
    (lowerStarComp AddCommGrpCat.{u + 1} s g)
  have hc' := conjugateIsoEquiv_symm_symm_hom
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} (s ≫ g) inferInstance)
    ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g inferInstance).comp
      (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} s inferInstance))
    (lowerStarComp AddCommGrpCat.{u + 1} s g)
  rw [eqToHom_refl, Category.comp_id, unitTransport_app_leftAdjointUniq
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g inferInstance)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} s)
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} s inferInstance)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (s ≫ g))
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} (s ≫ g) inferInstance)
    (lowerStarComp AddCommGrpCat.{u + 1} s g).hom (upperStarComp AddCommGrpCat.{u + 1} s g)
    (localizationRestrictionCompConjugate s g) hc hc' H, ← localizationUnitTransport_eq]
  simp only [Category.assoc]
  rfl

/-- **(a2) The Galois action is the abelian unit transport**: the action of `σ` on `g_* g^* H`
is the unit of `(ρ σ)^* ⊣ (ρ σ)_*` followed by the composition isomorphisms and the transport
along `ρ σ ≫ g = g`. -/
theorem galoisAction_eq_unitTransport {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]
    [Surjective g] [QuasiCompact g] {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)
    (σ : Γ) [WeaklyEtale (ρ σ)] (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    galoisAction g hρ σ H =
      (g)_*[AddCommGrpCat.{u + 1}].map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (ρ σ)).unit.app
            ((g)^*[AddCommGrpCat.{u + 1}].obj H)) ≫
        (lowerStarComp AddCommGrpCat.{u + 1} (ρ σ) g).hom.app _ ≫
        (ρ σ ≫ g)_*[AddCommGrpCat.{u + 1}].map
          ((upperStarComp AddCommGrpCat.{u + 1} (ρ σ) g).inv.app H) ≫
        eqToHom (by rw [hρ σ]) := by
  rw [unitTransport_eq_baseChangeTransportSheafHom (ρ σ) g (hρ σ)]
  rfl

end AlgebraicGeometry.ProEtale
