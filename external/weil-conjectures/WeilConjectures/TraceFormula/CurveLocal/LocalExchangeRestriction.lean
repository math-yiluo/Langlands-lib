/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.TraceFormula.CurveLocal.ExchangeRestriction
public import WeilConjectures.TraceFormula.CurveLocal.ModelRestriction
public import WeilConjectures.TraceFormula.CurveLocal.SectionsRestrictionGlobal
public import WeilConjectures.TraceFormula.CurveLocal.SupportTriangleCounit

/-!

# The exchange restriction on the strictly local model is the supported restriction

On the strictly local model `M` of a curve (`AlgebraicGeometry.Etale.CurveLocalModel`), with
closed immersions `a : G ⟶ T`, `b : B ⟶ T` and `Y = G ×_T B`, this file compares two forms of
the supported restriction of blueprint `lemma-local-term-restriction-map--1`, (2), for a bounded
below complex `Q` on `T`:

* the classical `ρ_{a,b} : RΓ_G(T, Q) ⟶ RΓ_Y(B, b^* Q)`
  (`AlgebraicGeometry.Etale.sectionsWithSupportRestriction`), a map of localization triangles;
* derived global sections over `Y` of the étale exchange restriction
  `Lι'^* Ra^! Q ⟶ Ry_B^! Lb^* Q` (`AlgebraicGeometry.Etale.exchangeRestriction`).

Under the identifications `RΓ_G(T, Q) ≅ RΓ(G, Ra^! Q)` and `RΓ(Y, Ry_B^! N) ≅ RΓ_Y(B, N)`, the
first is the restriction from `G` to `Y` followed by the second.

## Proof

Let `ε : E = Ra_! Ra^! Q ⟶ Q` be the counit. By naturality of `ρ` in `Q`,
`ρ_Q = RΓ_G(ε)⁻¹ ≫ ρ_E ≫ RΓ_Y(b^* ε)`, where `RΓ_G(ε)` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedSectionsWithSupport_map_counit`). As `E` is supported
on `G` and `b^* E` on `Y`, the inclusions of sections with support are isomorphisms for them, so
`ρ_E` is the restriction `RΓ(T, E) ⟶ RΓ(B, b^* E)` up to isomorphisms. By definition of the
exchange restriction, `b^* ε` factors as compact-support base change, `Ry_!` of the exchange
restriction and the counit of `Ry_! ⊣ Ry^!`; and `RΓ_Y(B, Ry_! -) ≅ RΓ(Y, -)`. All remaining
factors are isomorphisms, the restrictions `RΓ(T, -) ⟶ RΓ(B, b^* -)` and `RΓ(G, -) ⟶ RΓ(Y, ι'^* -)`
because the schemes of the model are strictly local with a common closed point
(`AlgebraicGeometry.Etale.CurveLocalModel.isIso_globalSectionsRestriction_b`,
`AlgebraicGeometry.Etale.CurveLocalModel.isIso_globalSectionsRestriction_ιY`); they are absorbed
into the identifications.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

/-- **Transport of a morphism along a naturality square and a morphism of triangles.** Let
`g ≫ ρ = ρ' ≫ c` with `g` an isomorphism, and `m ≫ h = ρ' ≫ m'` with `m'` an isomorphism, so
that `ρ = g⁻¹ ≫ m ≫ h ≫ m'⁻¹ ≫ c`. If `c = c₁ ≫ F ≫ c₃` and `t ≫ r = g⁻¹ ≫ m ≫ h ≫ m'⁻¹ ≫ c₁`,
then `ρ = t ≫ r ≫ F ≫ c₃`. -/
lemma CategoryTheory.eq_comp_comp_comp_of_comp_eq_comp {C : Type*} [Category C]
    {X₀ X₁ Y₀ Y₁ W₀ W₁ V V' G : C} (g : X₀ ⟶ X₁) [IsIso g] (ρ : X₁ ⟶ Y₁) (ρ' : X₀ ⟶ Y₀)
    (c : Y₀ ⟶ Y₁) (hnat : g ≫ ρ = ρ' ≫ c) (m : X₀ ⟶ W₀) (h : W₀ ⟶ W₁) (m' : Y₀ ⟶ W₁)
    [IsIso m'] (hcomm : m ≫ h = ρ' ≫ m') (c₁ : Y₀ ⟶ V) (F : V ⟶ V') (c₃ : V' ⟶ Y₁)
    (hc : c = c₁ ≫ F ≫ c₃) (r : G ⟶ V) (t : X₁ ⟶ G)
    (ht : t ≫ r = inv g ≫ m ≫ h ≫ inv m' ≫ c₁) :
    ρ = t ≫ r ≫ F ≫ c₃ := by
  have hρ' : ρ' = m ≫ h ≫ inv m' := by
    rw [reassoc_of% hcomm, IsIso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% ht, ← cancel_epi g, hnat, hρ', hc]
  simp

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  (M : CurveLocalModel k)

/-- **The supported restriction through the exchange restriction**: on the strictly local
model, the classical supported restriction `ρ_{a,b} : RΓ_G(T, Q) ⟶ RΓ_Y(B, b^* Q)` is, through the
identifications `RΓ_G(T, Q) ≅ RΓ(G, Ra^! Q)` and `RΓ(Y, Ry_B^! Lb^* Q) ≅ RΓ_Y(B, b^* Q)`, the
restriction from `G` to `Y = G ×_T B` followed by derived global sections over `Y` of the étale
exchange restriction of the square `ι' ≫ a = y_B ≫ b`. -/
theorem exists_sectionsWithSupportRestriction_eq
    (Q : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ (t : ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).obj Q).obj₁ ≅
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.G).obj
          ((R(M.a)^![Λ]).obj Q.obj))
      (e : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.Y).obj
        ((R(M.yB)^![Λ]).obj ((L((M.b)^*[ModuleCat.{u + 1} Λ])).obj Q.obj)) ≅
        ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj
          ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} Λ]).obj Q)).obj₁),
      sectionsWithSupportRestriction (ModuleCat.{u + 1} Λ) M.b M.a M.yB M.openComplement_yB_le Q =
        t.hom ≫ globalSectionsRestriction (A := ModuleCat.{u + 1} Λ) M.ιY
            ((R(M.a)^![Λ]).obj Q.obj) ≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.Y).map
            ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) M.ιY).inv.app _ ≫
              exchangeRestriction Λ M.isPullback_ιY Q.obj) ≫ e.hom := by
  -- the source `E = Ra_! Ra^! Q` of the counit `ε : E ⟶ Q` is bounded below
  obtain ⟨n, hn⟩ := plus_rightDerivedUpperShriek_obj Λ M.a Q.obj Q.property
  have hE : DerivedCategory.TStructure.t.plus ((R(M.a)_![ModuleCat.{u + 1} Λ]).obj
      ((R(M.a)^![Λ]).obj Q.obj)) := by
    have : ((R(M.a)^![Λ]).obj Q.obj).IsGE n := hn
    have := ((M.a)_*[ModuleCat.{u + 1} Λ]).isGE_rightDerivedFunctor_obj
      ((R(M.a)^![Λ]).obj Q.obj) n
    exact ⟨n, DerivedCategory.TStructure.t.isGE_of_iso
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ M.a).app _).symm n⟩
  let E : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := ⟨_, hE⟩
  let ε : E ⟶ Q := ObjectProperty.homMk
    ((rightDerivedUpperShriekAdjunction Λ M.a).counit.app Q.obj)
  let φ := sectionsWithSupportTrianglePullback (ModuleCat.{u + 1} Λ) M.b M.a M.yB
    M.openComplement_yB_le
  -- naturality of the supported restriction along `ε`
  have hnat : ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).map ε).hom₁ ≫
      sectionsWithSupportRestriction (ModuleCat.{u + 1} Λ) M.b M.a M.yB M.openComplement_yB_le Q =
        (φ.app E).hom₁ ≫ ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).map
          ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} Λ]).map ε)).hom₁ :=
    congrArg TriangleMorphism.hom₁ (φ.naturality ε)
  have hg : IsIso ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).map ε).hom₁ :=
    isIso_rightDerivedSectionsWithSupport_map_counit Λ M.a Q.obj
  -- `E` is supported on `G`, and its pullback to `B` on `Y`
  have hEs : IsZero (((M.a.openComplement.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
      E.obj) :=
    isZero_mapDerivedCategory_upperStar_rightDerivedLowerShriek _ M.a _ subset_rfl _
  have hSs : IsZero (((M.yB.openComplement.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
      ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} Λ]).obj E).obj) :=
    isZero_mapDerivedCategory_upperStar_upperStar_rightDerivedLowerShriek _ M.a _ M.b (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact M.openComplement_yB_le x.2) _
  have hm : IsIso ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).obj E).mor₁ :=
    isIso_sectionsWithSupportTriangle_obj_mor₁ _ M.a E hEs
  have hm' : IsIso ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj
      ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} Λ]).obj E)).mor₁ :=
    isIso_sectionsWithSupportTriangle_obj_mor₁ _ M.yB _ hSs
  have hh : IsIso (φ.app E).hom₂ := by
    have : IsIso (globalSectionsRestriction M.b E.obj) := M.isIso_globalSectionsRestriction_b _
    rw [← rightDerivedPullback_ΓPullback_app] at this
    exact this
  -- `b^* ε` factors through the exchange restriction and the counit of `Ry_! ⊣ Ry^!`
  let K := (R(M.a)^![Λ]).obj Q.obj
  let NL := (L((M.b)^*[ModuleCat.{u + 1} Λ])).obj Q.obj
  let adjy := rightDerivedUpperShriekAdjunction Λ M.yB
  let lb := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) M.b
  let lι := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) M.ιY
  let σ := lowerShriekBaseChangeIso Λ M.isPullback_ιY
  let f := lι.inv.app K ≫ exchangeRestriction Λ M.isPullback_ιY Q.obj
  let c₁ := lb.inv.app E.obj ≫ σ.hom.app K ≫
    (R(M.yB)_![ModuleCat.{u + 1} Λ]).map (lι.hom.app K)
  have h₃ : ((M.b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map ε.hom =
      (c₁ ≫ (R(M.yB)_![ModuleCat.{u + 1} Λ]).map f) ≫ adjy.counit.app NL ≫
        lb.hom.app Q.obj := by
    have e₁ : (R(M.yB)_![ModuleCat.{u + 1} Λ]).map (lι.hom.app K) ≫
        (R(M.yB)_![ModuleCat.{u + 1} Λ]).map f =
          (R(M.yB)_![ModuleCat.{u + 1} Λ]).map (exchangeRestriction Λ M.isPullback_ιY Q.obj) := by
      rw [← Functor.map_comp, Iso.hom_inv_id_app_assoc]
    have e₂ : (R(M.yB)_![ModuleCat.{u + 1} Λ]).map
        (exchangeRestriction Λ M.isPullback_ιY Q.obj) ≫ adjy.counit.app NL =
          σ.inv.app K ≫ (L((M.b)^*[ModuleCat.{u + 1} Λ])).map ε.hom := by
      have := (adjy.homEquiv _ _).symm_apply_apply
        (σ.inv.app K ≫ (L((M.b)^*[ModuleCat.{u + 1} Λ])).map ε.hom)
      rw [Adjunction.homEquiv_counit] at this
      rw [exchangeRestriction_eq_homEquiv]
      exact this
    have e₃ := lb.hom.naturality ε.hom
    simp only [c₁, Category.assoc]
    rw [reassoc_of% e₁, reassoc_of% e₂, Iso.hom_inv_id_app_assoc, e₃, Iso.inv_hom_id_app_assoc]
  -- sections with support of `Ry_! f` are sections of `f` over `Y`
  let ν := rightDerivedLowerShriekCompSectionsWithSupportIso Λ M.yB
  let RΓY := rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) M.yB
  let c₃ := ν.inv.app ((R(M.yB)^![Λ]).obj
      ((L((M.b)^*[ModuleCat.{u + 1} Λ])).obj Q.obj)) ≫
    RΓY.map (adjy.counit.app NL) ≫ RΓY.map (lb.hom.app Q.obj)
  have hc : ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).map
      ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} Λ]).map ε)).hom₁ =
        (RΓY.map c₁ ≫ ν.hom.app _) ≫ (rightDerivedGlobalSections _ M.Y).map f ≫ c₃ := by
    have e₄ : RΓY.map ((R(M.yB)_![ModuleCat.{u + 1} Λ]).map f) =
        ν.hom.app _ ≫ (rightDerivedGlobalSections _ M.Y).map f ≫ ν.inv.app _ :=
      (NatIso.naturality_2 ν f).symm
    refine (congrArg RΓY.map h₃).trans ?_
    simp only [c₃, Functor.map_comp, Category.assoc, e₄]
  have hc₃₁ : IsIso (RΓY.map (adjy.counit.app NL)) :=
    isIso_rightDerivedSectionsWithSupport_map_counit Λ M.yB NL
  have hc₃₂ : IsIso (ν.inv.app ((R(M.yB)^![Λ]).obj
      ((L((M.b)^*[ModuleCat.{u + 1} Λ])).obj Q.obj))) :=
    (ν.app _).isIso_inv
  have hc₃ : IsIso c₃ :=
    IsIso.comp_isIso' hc₃₂ (IsIso.comp_isIso' hc₃₁ (Functor.map_isIso _ _))
  let J := inv ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).map ε).hom₁ ≫
    ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).obj E).mor₁ ≫ (φ.app E).hom₂ ≫
      inv ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj
        ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} Λ]).obj E)).mor₁ ≫
        RΓY.map c₁ ≫ ν.hom.app _
  have hJ : IsIso J := by
    dsimp only [J]
    infer_instance
  have := M.isIso_globalSectionsRestriction_ιY K
  have : IsIso ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} Λ] ⋙
      sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj E).mor₁ := hm'
  refine ⟨asIso J ≪≫ (asIso (globalSectionsRestriction M.ιY K)).symm, asIso c₃, ?_⟩
  refine eq_comp_comp_comp_of_comp_eq_comp _ _ _ _ hnat _ _ _ (φ.app E).comm₁ _ _ _ hc _ _ ?_
  rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]
  rfl

end AlgebraicGeometry.Etale.CurveLocalModel
