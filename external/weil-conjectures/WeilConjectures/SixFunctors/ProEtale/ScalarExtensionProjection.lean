/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictCoextendScalars
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.Adjunction.UnitProjection
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-!
# Extension of scalars of pro-étale sheaves as a tensor product

Let `S` be an algebra over a commutative ring `R`. For a pro-étale sheaf `K` of `R`-modules, the
extension of scalars `S ⊗_R K`, with scalars restricted back to `R`, is the tensor product
`K ⊗ S_X` with the sheaf `S_X = res (𝟙_)` of `R`-modules underlying the unit sheaf of
`S`-modules. The isomorphism is the projection map of the monoidal adjunction between extension
and restriction of scalars at the unit,
```
K ⊗ res 𝟙_ ──η ▷ _──▶ res (S ⊗_R K) ⊗ res 𝟙_ ──μ──▶ res ((S ⊗_R K) ⊗ 𝟙_) ──ρ──▶ res (S ⊗_R K)
```
so that its compatibility with the pullbacks `g^*` is a formal consequence of the monoidality
of the commutation `g^* (S ⊗_R -) ≅ S ⊗_R g^*`.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.sheafRestrictScalarsUnit`: the sheaf `S_X` of `R`-modules.
- `AlgebraicGeometry.ProEtale.sheafExtendScalarsProjection`: the projection map
  `K ⊗ S_X ⟶ res (S ⊗_R K)`, an isomorphism.
- `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsMap`: the base change map
  `g^* (res M) ⟶ res (g^* M)`, an isomorphism.
- `AlgebraicGeometry.ProEtale.upperStarSheafRestrictScalarsUnitMap`: the induced isomorphism
  `g^* S_X ⟶ S_Y`.
- `AlgebraicGeometry.ProEtale.sheafExtendScalarsProjection_upperStar`: the compatibility of the
  projection maps with `g^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section Projection

variable (X : Scheme.{u})

/-- The sheaf `S_X` of `R`-modules underlying the unit sheaf of `S`-modules on `X_proét`. -/
noncomputable abbrev sheafRestrictScalarsUnit : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R) :=
  (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).obj
    (𝟙_ _)

/-- The projection map `K ⊗ S_X ⟶ res (S ⊗_R K)` of the monoidal adjunction between extension
and restriction of scalars, at the unit: the composite of the unit of the adjunction, of the lax
monoidal structure of restriction of scalars and of the right unitor. -/
noncomputable def sheafExtendScalarsProjection :
    tensorRight (sheafRestrictScalarsUnit R S X) ⟶
      sheafExtendScalars (algebraMap R S) X ⋙
        sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) where
  app K := ((sheafExtendScalarsAdjunction (algebraMap R S) X).unit.app K ▷ _) ≫
    μ (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))) _ _ ≫
    (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map
      (ρ_ _).hom
  naturality K L f := by
    have h₁ : f ≫ (sheafExtendScalarsAdjunction (algebraMap R S) X).unit.app L =
        (sheafExtendScalarsAdjunction (algebraMap R S) X).unit.app K ≫
          (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map
            ((sheafExtendScalars (algebraMap R S) X).map f) :=
      (sheafExtendScalarsAdjunction (algebraMap R S) X).unit.naturality f
    have h₂ := μ_natural_left
      (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)))
      ((sheafExtendScalars (algebraMap R S) X).map f) (𝟙_ _)
    dsimp
    rw [← comp_whiskerRight_assoc, h₁, comp_whiskerRight_assoc, reassoc_of% h₂,
      Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    erw [rightUnitor_naturality]

end Projection

section Pullback

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The base change map `g^* (res M) ⟶ res (g^* M)` of restriction of scalars along the
pullback: the mate of the commutation `g^* (S ⊗_R -) ≅ S ⊗_R g^*` of
`AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso`. -/
noncomputable def upperStarRestrictScalarsMap :
    sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} R) g ⟶
      ProEtale.upperStar (ModuleCat.{u + 1} S) g ⋙
        sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) :=
  mateEquiv (sheafExtendScalarsAdjunction (algebraMap R S) X)
    (sheafExtendScalarsAdjunction (algebraMap R S) Y)
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv

/-- Coextension of scalars commutes with the direct image `g_*`, both being computed
objectwise. -/
noncomputable def lowerStarCompSheafComposeCoextendScalarsIso :
    ProEtale.lowerStar (ModuleCat.{u + 1} R) g ⋙
        sheafCompose (ProEt.topology X)
          (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} (algebraMap R S)) ≅
      sheafCompose (ProEt.topology Y)
          (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} (algebraMap R S)) ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} S) g :=
  Iso.refl _

/-- The mate of the identification `coext ∘ g_* = g_* ∘ coext` along the adjunctions
`res ⊣ coext` is the identification `g_* ∘ res = res ∘ g_*`. -/
lemma mateEquiv_symm_lowerStarCompSheafComposeCoextendScalarsIso :
    (mateEquiv (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Y) (algebraMap R S))
      (Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) (algebraMap R S))).symm
        (TwoSquare.mk _ _ _ _ (lowerStarCompSheafComposeCoextendScalarsIso R S g).inv) =
      TwoSquare.mk _ _ _ _
        (lowerStarCompSheafComposeRestrictScalarsIso (algebraMap R S) g).hom := by
  ext G U : 5
  simp only [Functor.comp_obj, mateEquiv_symm_apply, NatTrans.comp_app, Functor.id_obj,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_inv_app, Functor.associator_hom_app, CategoryTheory.Functor.map_id,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, sheafCompose_map_hom,
    Sheaf.restrictCoextendScalarsAdj_counit_app_hom_app,
    lowerStarCompSheafComposeCoextendScalarsIso, lowerStarCompSheafComposeRestrictScalarsIso,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  rw [ProEtale.lowerStar_map_hom_app, Sheaf.restrictCoextendScalarsAdj_unit_app_hom_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (ModuleCat.restrictCoextendScalarsAdj.{u + 1} (algebraMap R S)).left_triangle_components _

/-- The pullback commutes with restriction of scalars: the base change map
`g^* (res M) ⟶ res (g^* M)` is an isomorphism. -/
instance isIso_upperStarRestrictScalarsMap : IsIso (upperStarRestrictScalarsMap R S g) := by
  have hA : (mateEquiv (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g)
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g)
        (upperStarRestrictScalarsMap R S g)) =
      conjugateEquiv ((sheafExtendScalarsAdjunction (algebraMap R S) X).comp
          (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g))
        ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).comp
          (sheafExtendScalarsAdjunction (algebraMap R S) Y))
        (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv :=
    iterated_mateEquiv_conjugateEquiv _ _ _ _ _
  rw [sheafExtendScalarsCompUpperStarIso, conjugateIsoEquiv_symm_apply_inv,
    Equiv.apply_symm_apply] at hA
  have h := iterated_mateEquiv_conjugateEquiv_symm
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g)
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) (algebraMap R S))
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Y) (algebraMap R S))
    (TwoSquare.mk _ _ _ _ (lowerStarCompSheafComposeCoextendScalarsIso R S g).inv)
  rw [mateEquiv_symm_lowerStarCompSheafComposeCoextendScalarsIso] at h
  have h' : upperStarRestrictScalarsMap R S g =
      (mateEquiv (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g)
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g)).symm
        (TwoSquare.mk _ _ _ _
          (lowerStarCompSheafComposeRestrictScalarsIso (algebraMap R S) g).hom) :=
    (Equiv.eq_symm_apply _).2 hA
  rw [h', h]
  have : IsIso ((conjugateEquiv
      ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g).comp
        (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Y) (algebraMap R S)))
      ((Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) (algebraMap R S)).comp
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g))).symm
      (lowerStarCompSheafComposeCoextendScalarsIso R S g).inv) := inferInstance
  exact this

/-- The isomorphism `g^* S_X ⟶ S_Y`: the base change map `g^* (res 𝟙_) ⟶ res (g^* 𝟙_)`
followed by the unit comparison of the pullback. -/
noncomputable def upperStarSheafRestrictScalarsUnitMap :
    (ProEtale.upperStar (ModuleCat.{u + 1} R) g).obj (sheafRestrictScalarsUnit R S X) ⟶
      sheafRestrictScalarsUnit R S Y :=
  (upperStarRestrictScalarsMap R S g).app (𝟙_ _) ≫
    (sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map
      (η (ProEtale.upperStar (ModuleCat.{u + 1} S) g))

instance isIso_upperStarSheafRestrictScalarsUnitMap :
    IsIso (upperStarSheafRestrictScalarsUnitMap R S g) := by
  dsimp only [upperStarSheafRestrictScalarsUnitMap]
  infer_instance

/-- **The projection maps are compatible with the pullbacks**: for a sheaf `P` of `R`-modules on
`X`, the square
```
g^* (P ⊗ S_X) ──g^* π──▶ g^* res (S ⊗_R P) ──▶ res g^* (S ⊗_R P) ──▶ res (S ⊗_R g^* P)
      │                                                                     ‖
      δ                                                                     ‖
      ▼                                                                     ‖
g^* P ⊗ g^* S_X ──────▶ g^* P ⊗ S_Y ──────────────π──────────────▶ res (S ⊗_R g^* P)
```
commutes. -/
lemma sheafExtendScalarsProjection_upperStar
    (P : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (ProEtale.upperStar (ModuleCat.{u + 1} R) g).map ((sheafExtendScalarsProjection R S X).app P) ≫
        (upperStarRestrictScalarsMap R S g).app ((sheafExtendScalars (algebraMap R S) X).obj P) ≫
        (sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map
          ((sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.app P) =
      δ (ProEtale.upperStar (ModuleCat.{u + 1} R) g) P (sheafRestrictScalarsUnit R S X) ≫
        (_ ◁ upperStarSheafRestrictScalarsUnitMap R S g) ≫
        (sheafExtendScalarsProjection R S Y).app
          ((ProEtale.upperStar (ModuleCat.{u + 1} R) g).obj P) :=
  (sheafExtendScalarsAdjunction (algebraMap R S) X).map_unitProjection_comp_mateEquiv
    (sheafExtendScalarsAdjunction (algebraMap R S) Y) (sheafExtendScalarsCompUpperStarIso _ g)
    (NatTrans.IsMonoidal.δ_comp_tensorHom _) P

end Pullback

end AlgebraicGeometry.ProEtale
