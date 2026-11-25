/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic
public import WeilConjectures.TraceFormula.CurveLocal.DerivedFiniteEtaleTrace
public import WeilConjectures.TraceFormula.CurveLocal.SectionsRestriction

/-!
# Restriction of derived sections over the terminal étale objects

For a morphism of schemes `φ : Y ⟶ X`, the restriction of derived sections
`AlgebraicGeometry.Etale.sectionsRestriction` over the terminal étale objects `𝟙 X`, `𝟙 Y` and
the restriction map `AlgebraicGeometry.Etale.globalSectionsRestriction` (the derived unit followed
by the Leray isomorphism) agree up to the identifications of the global sections with the
sections over the terminal objects. In particular one vanishes when the other does
(`AlgebraicGeometry.Etale.sectionsRestriction_app_eq_zero_of_globalSectionsRestriction_eq_zero`).

The comparison rests on a general statement about right derived functors
(`CategoryTheory.Functor.rightDerivedPullback_app_eq_of_adjunction`): for an adjunction `L ⊣ R`
with `L` exact and an isomorphism `e : R ⋙ F ≅ F'`, the pullback map of right derived functors
along `L` induced by `F ⟶ F ∘ R ∘ L ≅ F' ∘ L` is `RF` of the derived unit followed by the
composition isomorphism `RF ∘ RR ≅ RF'`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite DerivedCategory

namespace CategoryTheory.Functor

variable {C C' D : Type*} [Category C] [Category C'] [Category D] [Abelian C] [Abelian C']
  [Abelian D] [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']

section Composition

variable (R : C' ⥤ C) {F : C ⥤ D} {F' : C' ⥤ D} [R.Additive] [F.Additive] [F'.Additive]
  [R.PreservesKInjectiveComplexes]

/-- The composition isomorphism `Functor.rightDerivedFunctorCompIso'` attached to
`e : R ⋙ F ≅ F'` is compatible with the units of the right derived functors. -/
@[reassoc]
lemma rightDerivedFunctorUnit_comp_rightDerivedFunctorCompIso'_hom_app (e : R ⋙ F ≅ F')
    (K : HomotopyCategory C' (ComplexShape.up ℤ)) :
    F.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        F.rightDerivedFunctor.map (R.rightDerivedFunctorUnit.app K) ≫
          (rightDerivedFunctorCompIso' R F e).hom.app (Qh.obj K) =
      Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) ≫
        F'.rightDerivedFunctorUnit.app K := by
  have hcomp : (R ⋙ F).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft Qh (rightDerivedFunctorCompIso R F).hom =
      rightDerivedFunctorCompUnit R F := by
    simp [rightDerivedFunctorCompIso]
  have hunit : (rightDerivedFunctorCompUnit R F).app K =
      F.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        F.rightDerivedFunctor.map (R.rightDerivedFunctorUnit.app K) := by
    have h := (mapHomotopyCategoryCompIso (Iso.refl (R ⋙ F)) (ComplexShape.up ℤ)).hom_inv_id_app K
    rw [mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
    simp only [rightDerivedFunctorCompUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id]
    erw [h, Functor.map_id, Category.id_comp]
  have hfac : rightDerivedFunctorCompUnit R F ≫ Functor.whiskerLeft Qh
      (rightDerivedFunctorCompIso' R F e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)) Qh ≫
        F'.rightDerivedFunctorUnit := by
    rw [← hcomp, Category.assoc, ← Functor.whiskerLeft_comp]
    simp only [rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    exact rightDerivedNatTrans_fac _ _ _ _ (HomotopyCategory.quasiIso C' (ComplexShape.up ℤ)) _
  have := NatTrans.congr_app hfac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, hunit,
    Category.assoc] at this
  exact this

end Composition

variable {L : C ⥤ C'} {R : C' ⥤ C} [L.Additive] [R.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [R.PreservesKInjectiveComplexes] (adj : L ⊣ R)
  {F : C ⥤ D} {F' : C' ⥤ D} [F.Additive] [F'.Additive] (e : R ⋙ F ≅ F') (α : F ⟶ L ⋙ F')

/-- Let `L ⊣ R` be an adjunction with `L` exact, `e : R ⋙ F ≅ F'` and `α : F ⟶ L ⋙ F'` the map
`F ⟶ F ∘ R ∘ L ≅ F' ∘ L` induced by the unit. Then the pullback map of right derived functors
`RF ⟶ RF' ∘ L` induced by `α` is `RF` of the derived unit `M ⟶ RR(L M)` followed by the
composition isomorphism `RF(RR(L M)) ≅ RF'(L M)`. -/
lemma rightDerivedPullback_app_eq_of_adjunction
    (hα : ∀ X, α.app X ≫ e.inv.app (L.obj X) = F.map (adj.unit.app X)) (M : DerivedCategory C) :
    (rightDerivedPullback L α).app M =
      F.rightDerivedFunctor.map ((adj.mapDerivedCategoryRightDerivedAdjunction).unit.app M) ≫
        (rightDerivedFunctorCompIso' R F e).hom.app (L.mapDerivedCategory.obj M) := by
  let γ : F.rightDerivedFunctor ⟶ L.mapDerivedCategory ⋙ F'.rightDerivedFunctor :=
    { app M := F.rightDerivedFunctor.map
          ((adj.mapDerivedCategoryRightDerivedAdjunction).unit.app M) ≫
        (rightDerivedFunctorCompIso' R F e).hom.app (L.mapDerivedCategory.obj M)
      naturality M N f := by
        have h₁ := (adj.mapDerivedCategoryRightDerivedAdjunction).unit.naturality f
        have h₂ := (rightDerivedFunctorCompIso' R F e).hom.naturality
          (L.mapDerivedCategory.map f)
        dsimp at h₁ h₂ ⊢
        rw [← F.rightDerivedFunctor.map_comp_assoc, h₁, F.rightDerivedFunctor.map_comp_assoc, h₂]
        simp only [assoc] }
  suffices h : rightDerivedPullback L α = γ from congr_app h M
  refine F.rightDerivedFunctor.rightDerived_ext F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ _ _ ?_
  ext H
  have hη : (adj.mapDerivedCategoryRightDerivedAdjunction).unit.app (Qh.obj H) =
      Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app H) ≫
        R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj H) ≫
          R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.inv.app H) := by
    have hunit := (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit H
    rw [← reassoc_of% hunit, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, comp_id]
    rfl
  have h₂ := (rightDerivedFunctorCompIso' R F e).hom.naturality
    (L.mapDerivedCategoryFactorsh.inv.app H)
  have h₃ := F.rightDerivedFunctorUnit.naturality
    ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app H)
  have h₄ := rightDerivedFunctorUnit_comp_rightDerivedFunctorCompIso'_hom_app R e
    ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj H)
  dsimp only [γ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.comp_map] at h₂ h₃ h₄ ⊢
  rw [hη]
  simp only [Functor.map_comp, assoc]
  rw [h₂, ← reassoc_of% h₃]
  erw [reassoc_of% h₄]
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  have h₅ : (F.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) ≫
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
        ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) := by
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    erw [Functor.mapHomotopyCategory_map, NatTrans.mapHomotopyCategory_app, ← Functor.map_comp]
    congr 1
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f]
    rw [← hα, assoc]
    erw [Iso.inv_hom_id_app]
    exact comp_id _
  rw [rightDerivedPullback_fac_app, ← Qh.map_comp_assoc]
  erw [h₅]
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The pullback map `RΓ(X, K) ⟶ RΓ(Y, φ^* K)` of derived global sections induced by the
pullback of global sections is the restriction map `globalSectionsRestriction φ K`. -/
lemma rightDerivedPullback_ΓPullback_app {X Y : Scheme.{u}} (φ : Y ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (Functor.rightDerivedPullback (φ)^*[A] (ΓPullback A φ)).app K =
      globalSectionsRestriction φ K :=
  Functor.rightDerivedPullback_app_eq_of_adjunction (upperStarLowerStarAdjunction A φ)
    (lowerStarCompGlobalSectionsIso A φ) _
    (ΓPullback_app_comp_lowerStarCompGlobalSectionsIso_inv_app A φ) K

/-- If the restriction map `RΓ(X, K) ⟶ RΓ(Y, φ^* K)` vanishes, so does the restriction of
derived sections over the terminal étale objects `𝟙 X` and `𝟙 Y`. -/
lemma sectionsRestriction_app_eq_zero_of_globalSectionsRestriction_eq_zero {X Y : Scheme.{u}}
    (φ : Y ⟶ X) (hφ : φ ≫ (Scheme.Etale.mk (𝟙 X)).hom = (Scheme.Etale.mk (𝟙 Y)).hom ≫ φ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (h : globalSectionsRestriction φ K = 0) :
    (sectionsRestriction A φ (V := Scheme.Etale.mk (𝟙 X)) (W := Scheme.Etale.mk (𝟙 Y))
      φ hφ).app K = 0 := by
  let τ := Sheaf.natTransΓRes X.smallEtaleTopology A (op (Scheme.Etale.mk (𝟙 X)))
  let τ' := Sheaf.natTransΓRes Y.smallEtaleTopology A (op (Scheme.Etale.mk (𝟙 Y)))
  have hc := congr_app (Functor.rightDerivedFunctorNatTrans_comp_rightDerivedPullback (φ)^*[A]
    τ τ' (ΓPullback A φ) (sectionsPullback A φ (V := Scheme.Etale.mk (𝟙 X))
      (W := Scheme.Etale.mk (𝟙 Y)) φ hφ) (by
        refine NatTrans.ext (funext fun F ↦ ?_)
        exact (ΓPullback_app_comp_ΓRes A φ (V := Scheme.Etale.mk (𝟙 X))
          (W := Scheme.Etale.mk (𝟙 Y)) φ hφ F).symm)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, rightDerivedPullback_ΓPullback_app,
    h, zero_comp] at hc
  rw [← cancel_epi ((Functor.rightDerivedFunctorNatTrans τ).app K), comp_zero]
  exact hc

end AlgebraicGeometry.Etale
