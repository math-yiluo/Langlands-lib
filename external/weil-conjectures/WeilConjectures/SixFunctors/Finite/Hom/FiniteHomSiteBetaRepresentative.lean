/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps

/-! # The finite site mate on a single K-flat representative

Source: Stacks 07A4 and 07A6; the scalar/site comparison in
lemma-change-coefficients-internal-hom--1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem mate_normalization_at
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {E₁ : C₁ ⥤ C₂} {U₁ : C₂ ⥤ C₁} {E₂ : C₃ ⥤ C₄} {U₂ : C₄ ⥤ C₃}
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {L₁ : D₁ ⥤ D₂} {R₁ : D₂ ⥤ D₁} {L₂ : D₃ ⥤ D₄} {R₂ : D₄ ⥤ D₃}
    (d₁ : L₁ ⊣ R₁) (d₂ : L₂ ⊣ R₂)
    (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (Q₃ : C₃ ⥤ D₃) (Q₄ : C₄ ⥤ D₄)
    {F : C₁ ⥤ C₃} {G : C₂ ⥤ C₄} {Fd : D₁ ⥤ D₃} {Gd : D₂ ⥤ D₄}
    (β₁ : Q₂ ⋙ R₁ ≅ U₁ ⋙ Q₁) (β₂ : Q₄ ⋙ R₂ ≅ U₂ ⋙ Q₃)
    (γ₁ : Q₁ ⋙ Fd ≅ F ⋙ Q₃) (γ₂ : Q₂ ⋙ Gd ≅ G ⋙ Q₄)
    (τ : U₁ ⋙ F ⟶ G ⋙ U₂) (τd : R₁ ⋙ Fd ⟶ Gd ⋙ R₂) (P : C₁)
    (α₁ : L₁.obj (Q₁.obj P) ⟶ Q₂.obj (E₁.obj P))
    (α₂ : L₂.obj (Q₃.obj (F.obj P)) ⟶ Q₄.obj (E₂.obj (F.obj P)))
    (h₁ : d₁.unit.app (Q₁.obj P) ≫ R₁.map α₁ ≫
      β₁.hom.app (E₁.obj P) = Q₁.map (a₁.unit.app P))
    (h₂ : d₂.unit.app (Q₃.obj (F.obj P)) ≫ R₂.map α₂ ≫
      β₂.hom.app (E₂.obj (F.obj P)) = Q₃.map (a₂.unit.app (F.obj P)))
    (hτ : ∀ N, Fd.map (β₁.hom.app N) ≫ γ₁.hom.app (U₁.obj N) ≫ Q₃.map (τ.app N) =
      τd.app (Q₂.obj N) ≫ R₂.map (γ₂.hom.app N) ≫ β₂.hom.app (G.obj N)) :
    ((mateEquiv d₁ d₂).symm (TwoSquare.mk _ _ _ _ τd)).app (Q₁.obj P) ≫
        Gd.map α₁ ≫ γ₂.hom.app (E₁.obj P) =
      L₂.map (γ₁.hom.app P) ≫ α₂ ≫
        Q₄.map (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).app P) := by
  apply (d₂.homEquiv _ _).injective
  apply (cancel_mono (β₂.hom.app (G.obj (E₁.obj P)))).mp
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (unit_mateEquiv_symm d₁ d₂ (TwoSquare.mk _ _ _ _ τd) (Q₁.obj P))]
  rw [← reassoc_of% τd.naturality α₁]
  rw [← hτ (E₁.obj P)]
  rw [← Fd.map_comp_assoc, ← Fd.map_comp_assoc, Category.assoc, h₁]
  rw [reassoc_of% γ₁.hom.naturality (a₁.unit.app P)]
  rw [← Q₃.map_comp, unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ τ) P]
  rw [Q₃.map_comp]
  have hb := β₂.hom.naturality
    (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).app P)
  simp only [Functor.comp_map, Functor.comp_obj] at hb
  rw [hb]
  rw [← reassoc_of% d₂.unit.naturality (γ₁.hom.app P)]
  convert! (congrArg
    (fun z ↦ γ₁.hom.app P ≫ z ≫
      Q₃.map (U₂.map (((mateEquiv a₁ a₂).symm
        (TwoSquare.mk _ _ _ _ τ)).app P))) h₂.symm) using 1;
    simp only [Category.assoc]

private theorem mate_mapComplex_at
    {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    {F : C₁ ⥤ C₃} {G : C₂ ⥤ C₄}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [F.Additive] [G.Additive]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (τ : R₁ ⋙ F ⟶ G ⋙ R₂)
    (P : CochainComplex C₁ ℤ) :
    ((mateEquiv (a.mapHomologicalComplex (.up ℤ))
      (b.mapHomologicalComplex (.up ℤ))).symm
        (TwoSquare.mk (R₁.mapHomologicalComplex (.up ℤ))
          (G.mapHomologicalComplex (.up ℤ)) (F.mapHomologicalComplex (.up ℤ))
          (R₂.mapHomologicalComplex (.up ℤ))
          (NatTrans.mapHomologicalComplex τ (.up ℤ)))).app P =
      (NatTrans.mapHomologicalComplex
        ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)) (.up ℤ)).app P := by
  ext i
  simp only [mateEquiv,
    Equiv.symm_mk, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj, Functor.comp_map,
    HomologicalComplex.id_f,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, Category.id_comp]
  rfl

private theorem mate_mapComplex_normalization_at
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {E₁ : C₁ ⥤ C₂} {U₁ : C₂ ⥤ C₁} {E₂ : C₃ ⥤ C₄} {U₂ : C₄ ⥤ C₃}
    [E₁.Additive] [U₁.Additive] [E₂.Additive] [U₂.Additive]
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {L₁ : D₁ ⥤ D₂} {R₁ : D₂ ⥤ D₁} {L₂ : D₃ ⥤ D₄} {R₂ : D₄ ⥤ D₃}
    (d₁ : L₁ ⊣ R₁) (d₂ : L₂ ⊣ R₂)
    (Q₁ : CochainComplex C₁ ℤ ⥤ D₁) (Q₂ : CochainComplex C₂ ℤ ⥤ D₂)
    (Q₃ : CochainComplex C₃ ℤ ⥤ D₃) (Q₄ : CochainComplex C₄ ℤ ⥤ D₄)
    {F : C₁ ⥤ C₃} {G : C₂ ⥤ C₄} [F.Additive] [G.Additive]
    {Fd : D₁ ⥤ D₃} {Gd : D₂ ⥤ D₄}
    (β₁ : Q₂ ⋙ R₁ ≅ U₁.mapHomologicalComplex (.up ℤ) ⋙ Q₁)
    (β₂ : Q₄ ⋙ R₂ ≅ U₂.mapHomologicalComplex (.up ℤ) ⋙ Q₃)
    (γ₁ : Q₁ ⋙ Fd ≅ F.mapHomologicalComplex (.up ℤ) ⋙ Q₃)
    (γ₂ : Q₂ ⋙ Gd ≅ G.mapHomologicalComplex (.up ℤ) ⋙ Q₄)
    (τ : U₁ ⋙ F ⟶ G ⋙ U₂) (τd : R₁ ⋙ Fd ⟶ Gd ⋙ R₂)
    (P : CochainComplex C₁ ℤ)
    (α₁ : L₁.obj (Q₁.obj P) ⟶ Q₂.obj ((E₁.mapHomologicalComplex (.up ℤ)).obj P))
    (α₂ : L₂.obj (Q₃.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ⟶
      Q₄.obj ((E₂.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)))
    (h₁ : d₁.unit.app (Q₁.obj P) ≫ R₁.map α₁ ≫
      β₁.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj P) =
        Q₁.map ((a₁.mapHomologicalComplex (.up ℤ)).unit.app P))
    (h₂ : d₂.unit.app (Q₃.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫ R₂.map α₂ ≫
      β₂.hom.app ((E₂.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
      Q₃.map ((a₂.mapHomologicalComplex (.up ℤ)).unit.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)))
    (hτ : ∀ N, Fd.map (β₁.hom.app N) ≫ γ₁.hom.app
        ((U₁.mapHomologicalComplex (.up ℤ)).obj N) ≫
        Q₃.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app N) =
      τd.app (Q₂.obj N) ≫ R₂.map (γ₂.hom.app N) ≫
        β₂.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj N)) :
    ((mateEquiv d₁ d₂).symm (TwoSquare.mk _ _ _ _ τd)).app (Q₁.obj P) ≫
        Gd.map α₁ ≫ γ₂.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj P) =
      L₂.map (γ₁.hom.app P) ≫ α₂ ≫
        Q₄.map ((NatTrans.mapHomologicalComplex
          ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)) (.up ℤ)).app P) := by
  have hc := mate_normalization_at
    (a₁.mapHomologicalComplex (.up ℤ)) (a₂.mapHomologicalComplex (.up ℤ))
    d₁ d₂ Q₁ Q₂ Q₃ Q₄ β₁ β₂ γ₁ γ₂
    (NatTrans.mapHomologicalComplex τ (.up ℤ)) τd P α₁ α₂ h₁ h₂ hτ
  rw [mate_mapComplex_at a₁ a₂ τ P] at hc
  exact hc

private theorem exactSquare_inv_fac
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (K : CochainComplex C ℤ) :
    S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        S.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app K) =
      (Functor.mapDerivedCategorySquareIso e).inv.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
  simpa only [Functor.square_symm_hom, Iso.symm_hom] using (Functor.exactSquare_fac e.symm K).symm

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Ordinary scalar/site comparison: the actual left mate of scalar restriction.
Source: Stacks 03CZ, 07A4; blueprint lemma-change-coefficients-internal-hom--1.
(blueprint: lem-coef-finite-hom-site-beta-representative). -/
def finiteHomSiteOrdinaryBeta {n m : ℕ} (h : m ≤ n) :
    finiteHomNuOrdinary l E X n ⋙ coefficientFiniteQuotientExtension l E X h ⟶
      ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X ⋙
        finiteHomNuOrdinary l E X m :=
  ((mateEquiv (ProEtale.etaleSheafExtendScalarsAdjunction (finiteHomQuotient l E h) X)
    ((coefficientDerivedSystemEvaluationCalculus l E
      X).choose.quotientCalculus.ordinaryAdjunction h)).symm
    (TwoSquare.mk _ _ _ _ (finiteHomNuRestriction l E X h).inv))

private theorem scalar_unit_normalization {n m : ℕ} (h : m ≤ n)
    (P : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (finiteHomQuotient l E h))).unit.app (DerivedCategory.Q.obj P) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology (finiteHomQuotient l E h)).map
          (Etale.scalarExtensionRepresentative (finiteHomQuotient l E h) X P) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E
      h)).mapDerivedCategoryFactors.hom.app
            (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h)
      X).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((ProEtale.etaleSheafExtendScalarsAdjunction
          (finiteHomQuotient l E h) X).mapHomologicalComplex (.up ℤ)).unit.app P) := by
  have hu := (Iso.eq_comp_inv
    ((Sheaf.restrictScalars X.smallEtaleTopology
      (finiteHomQuotient l E h)).mapDerivedCategoryFactors.app
        (((ProEtale.etaleSheafExtendScalars
          (finiteHomQuotient l E h) X).mapHomologicalComplex (.up ℤ)).obj P))).mp
    (Etale.scalarExtensionRepresentative_unit_public (finiteHomQuotient l E h) X P)
  exact (Category.assoc _ _ _).symm.trans (hu.trans
    (congrArg (fun f ↦ DerivedCategory.Q.map f)
      (Etale.ExceptionalCoefficients.mapComplex_unit_formula
        (ProEtale.etaleSheafExtendScalarsAdjunction (finiteHomQuotient l E h) X) P).symm))

end WeilConjectures
