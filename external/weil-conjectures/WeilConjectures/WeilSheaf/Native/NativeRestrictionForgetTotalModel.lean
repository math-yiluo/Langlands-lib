/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTotalModel
import WeilConjectures.WeilSheaf.Native.NativeForgetNormalizedBinaryModels
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.SixFunctors.ProEtale.Adic.TensorLeftInvertible
import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-! # Native restriction and the ordinary total tensor

Source: Stacks 0E8I, 0GL1 and 015F.
(blueprint: lem-sf-native-restriction-forget-total-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u a b v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

section Proof

attribute [local irreducible]
  HomologicalComplex₂.total
  AlgebraicGeometry.Scheme.Hom.geometricFiberMap
  AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius
  AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenForgetPull
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenTensorModel
  DerivedCategory DerivedCategory.Q instCategoryDerivedCategory
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
  CategoryTheory.Functor.mapDerivedCategoryNatIso
section ExactFactors

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
  [Abelian C] [Abelian D] [Abelian A] [Abelian B]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory A] [HasDerivedCategory B]
  (L : C ⥤ D) (V : D ⥤ B) (F : C ⥤ A) (R : A ⥤ B)
  [L.Additive] [V.Additive] [F.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private theorem exact_forget_factors (e : L ⋙ V ≅ F ⋙ R) (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryCompIso L V ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso F R).symm).hom.app
        (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    V.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
      V.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).symm).hom.app P) := by
  have ha : (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P =
      (Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).symm).hom.app P := by
    ext n
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv,
      NatTrans.id_app]
    erw [Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso L V).inv.app
    (DerivedCategory.Q.obj P))).1
  rw [Iso.inv_hom_id_app_assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at ha
  erw [← ha]

end ExactFactors

section MuTransport

private theorem isIso_mu_transport
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (Q : C ⥤ D) [Q.LaxMonoidal]
    {X Y X' Y' : C} (e : X ≅ X') (f : Y ≅ Y')
    (h : IsIso (Functor.LaxMonoidal.μ Q X Y)) :
    IsIso (Functor.LaxMonoidal.μ Q X' Y') := by
  let := h
  exact IsIso.of_isIso_fac_left (Functor.LaxMonoidal.μ_natural Q e.hom f.hom)

end MuTransport

/-- Naturality of the binary comparisons and the localization tensorator. -/
private theorem binary_square
    {C : Type u} {D : Type v} {E : Type w}
    [Category* C] [Category* D] [Category* E]
    [MonoidalCategory D] [MonoidalCategory E]
    (V : C ⥤ D) (Q : E ⥤ D) [Q.LaxMonoidal]
    (NT : C × C ⥤ C) (S : D × D ⥤ D)
    (t : NT ⋙ V ≅ V.prod V ⋙ S) (d : S ≅ MonoidalCategory.tensor D)
    {x₁ x₂ y₁ y₂ : C} {z₁ z₂ : D} {u₁ u₂ w₁ w₂ : E}
    (l₁ : x₁ ⟶ y₁) (l₂ : x₂ ⟶ y₂)
    (e₁ : V.obj x₁ ⟶ z₁) (e₂ : V.obj x₂ ⟶ z₂)
    (f₁ : z₁ ⟶ Q.obj w₁) (f₂ : z₂ ⟶ Q.obj w₂)
    (g₁ : V.obj y₁ ⟶ Q.obj u₁) (g₂ : V.obj y₂ ⟶ Q.obj u₂)
    (a₁ : u₁ ⟶ w₁) (a₂ : u₂ ⟶ w₂)
    (q : V.obj (NT.obj (y₁, y₂)) ⟶ Q.obj (u₁ ⊗ u₂))
    (hq : q = t.hom.app (y₁, y₂) ≫ d.hom.app (V.obj y₁, V.obj y₂) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom g₁ g₂) ≫
        Functor.LaxMonoidal.μ Q u₁ u₂)
    (hf₁ : e₁ ≫ f₁ = V.map l₁ ≫ g₁ ≫ Q.map a₁)
    (hf₂ : e₂ ≫ f₂ = V.map l₂ ≫ g₂ ≫ Q.map a₂) :
    t.hom.app (x₁, x₂) ≫ S.map (Prod.mkHom e₁ e₂) ≫
      d.hom.app (z₁, z₂) ≫ (MonoidalCategory.tensor D).map (Prod.mkHom f₁ f₂) ≫
        Functor.LaxMonoidal.μ Q w₁ w₂ =
    V.map (NT.map (Prod.mkHom l₁ l₂)) ≫ q ≫
      Q.map ((MonoidalCategory.tensor E).map (Prod.mkHom a₁ a₂)) := by
  rw [hq]
  simp only [Category.assoc]
  erw [t.hom.naturality_assoc]
  dsimp only [Functor.comp_map, Functor.prod_map]
  erw [d.hom.naturality_assoc, d.hom.naturality_assoc]
  erw [← Functor.LaxMonoidal.μ_natural]
  simp only [← (MonoidalCategory.tensor D).map_comp_assoc]
  dsimp only [MonoidalCategory.tensor]
  dsimp only [CategoryTheory.prod_comp, Prod.mkHom]
  simp only [tensorHom_comp_tensorHom_assoc]
  rw [hf₁, hf₂]
  simp only [Category.assoc]

section FinalDiagram

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
  [Abelian C] [Abelian D] [Abelian A] [Abelian B]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory A] [HasDerivedCategory B]
  [MonoidalCategory (CochainComplex A ℤ)] [MonoidalCategory (CochainComplex B ℤ)]
  [MonoidalCategory (DerivedCategory B)]
  [Functor.LaxMonoidal (DerivedCategory.Q (C := B))]
  (L : C ⥤ D) (V : D ⥤ B) (F : C ⥤ A) (R : A ⥤ B)
  [L.Additive] [V.Additive] [F.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private abbrev complex_square (e : L ⋙ V ≅ F ⋙ R) :=
  Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).symm

/-- Paste the normalized binary models and the exact-functor restriction square. -/
private theorem final_total_diagram
    (e : L ⋙ V ≅ F ⋙ R)
    (DZ : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C)
    (DU : DerivedCategory D × DerivedCategory D ⥤ DerivedCategory D)
    (SU : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (tu : DU ⋙ V.mapDerivedCategory ≅
      V.mapDerivedCategory.prod V.mapDerivedCategory ⋙ SU)
    (du : SU ≅ MonoidalCategory.tensor (DerivedCategory B))
    (rho : DZ ⋙ L.mapDerivedCategory ≅
      L.mapDerivedCategory.prod L.mapDerivedCategory ⋙ DU)
    (P T WZ : CochainComplex C ℤ) (WU : CochainComplex D ℤ)
    (modelZ : DZ.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj WZ)
    (modelU : DU.obj
        (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P),
          DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj T)) ≅
      DerivedCategory.Q.obj WU)
    (tr : (L.mapHomologicalComplex (.up ℤ)).obj WZ ≅ WU)
    (hr : V.mapDerivedCategory.map
          (rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        V.mapDerivedCategory.map
          (DU.map (Prod.mkHom (L.mapDerivedCategoryFactors.hom.app P)
            (L.mapDerivedCategoryFactors.hom.app T))) ≫
        V.mapDerivedCategory.map modelU.hom =
      V.mapDerivedCategory.map (L.mapDerivedCategory.map modelZ.hom) ≫
        V.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app WZ) ≫
        V.mapDerivedCategory.map (DerivedCategory.Q.map tr.hom))
    (cZ : (F.mapHomologicalComplex (.up ℤ)).obj WZ ≅
      (F.mapHomologicalComplex (.up ℤ)).obj P ⊗ (F.mapHomologicalComplex (.up ℤ)).obj T)
    (cU : (V.mapHomologicalComplex (.up ℤ)).obj WU ≅
      (V.mapHomologicalComplex (.up ℤ)).obj
          ((L.mapHomologicalComplex (.up ℤ)).obj P) ⊗
        (V.mapHomologicalComplex (.up ℤ)).obj
          ((L.mapHomologicalComplex (.up ℤ)).obj T))
    (hmU : V.mapDerivedCategory.map modelU.hom ≫
        V.mapDerivedCategoryFactors.hom.app WU ≫ DerivedCategory.Q.map cU.hom =
      tu.hom.app
          (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P),
            DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj T)) ≫
        du.hom.app
          (V.mapDerivedCategory.obj
              (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P)),
            V.mapDerivedCategory.obj
              (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj T))) ≫
        (MonoidalCategory.tensor (DerivedCategory B)).map
          (Prod.mkHom
            (V.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P))
            (V.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj T))) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((V.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj P))
          ((V.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj T)))
    (ord : (R.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P ⊗
          (F.mapHomologicalComplex (.up ℤ)).obj T) ≅
      (R.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⊗
        (R.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj T))
    (hchain : (V.mapHomologicalComplex (.up ℤ)).map tr.hom ≫ cU.hom ≫
        (MonoidalCategory.tensor (CochainComplex B ℤ)).map
          (Prod.mkHom ((complex_square L V F R e).hom.app P)
            ((complex_square L V F R e).hom.app T)) =
      (complex_square L V F R e).hom.app WZ ≫
        (R.mapHomologicalComplex (.up ℤ)).map cZ.hom ≫ ord.hom)
    (mZ : F.mapDerivedCategory.obj
        (DZ.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≅
      DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P ⊗
          (F.mapHomologicalComplex (.up ℤ)).obj T))
    (hmZ : mZ.hom = F.mapDerivedCategory.map modelZ.hom ≫
      F.mapDerivedCategoryFactors.hom.app WZ ≫ DerivedCategory.Q.map cZ.hom) :
    ∃ mU : SU.obj
        (R.mapDerivedCategory.obj (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)),
          R.mapDerivedCategory.obj (F.mapDerivedCategory.obj (DerivedCategory.Q.obj T))) ≅
      DerivedCategory.Q.obj
        ((R.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⊗
          (R.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj T)),
      mU.hom = du.hom.app
          (R.mapDerivedCategory.obj (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)),
            R.mapDerivedCategory.obj (F.mapDerivedCategory.obj (DerivedCategory.Q.obj T))) ≫
        (MonoidalCategory.tensor (DerivedCategory B)).map
          (Prod.mkHom
            (R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
              R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
            (R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app T) ≫
              R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj T))) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((R.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
          ((R.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj T)) ∧
      V.mapDerivedCategory.map (rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
          tu.hom.app
            (L.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
              L.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) ≫
          SU.map (Prod.mkHom
            ((Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P))
            ((Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj T))) ≫
          mU.hom =
        (Functor.mapDerivedCategorySquareIso e).hom.app
            (DZ.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
          R.mapDerivedCategory.map mZ.hom ≫
          R.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj P ⊗
              (F.mapHomologicalComplex (.up ℤ)).obj T) ≫ DerivedCategory.Q.map ord.hom := by
  let RP := (L.mapHomologicalComplex (.up ℤ)).obj P
  let RT := (L.mapHomologicalComplex (.up ℤ)).obj T
  let P₀ := (F.mapHomologicalComplex (.up ℤ)).obj P
  let T₀ := (F.mapHomologicalComplex (.up ℤ)).obj T
  let a := complex_square L V F R e
  have hμU : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((V.mapHomologicalComplex (.up ℤ)).obj RP)
      ((V.mapHomologicalComplex (.up ℤ)).obj RT)) := by
    have h : IsIso (V.mapDerivedCategory.map modelU.hom ≫
        V.mapDerivedCategoryFactors.hom.app WU ≫ DerivedCategory.Q.map cU.hom) :=
      inferInstance
    rw [hmU] at h
    have : IsIso (Prod.mkHom (V.mapDerivedCategoryFactors.hom.app RP)
        (V.mapDerivedCategoryFactors.hom.app RT)) := by
      change IsIso ((V.mapDerivedCategoryFactors.app RP).prod
        (V.mapDerivedCategoryFactors.app RT)).hom
      infer_instance
    simpa only [isIso_comp_left_iff] using h
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((R.mapHomologicalComplex (.up ℤ)).obj P₀)
      ((R.mapHomologicalComplex (.up ℤ)).obj T₀)) :=
    isIso_mu_transport DerivedCategory.Q (a.app P) (a.app T) hμU
  let f := R.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    R.mapDerivedCategoryFactors.app P₀
  let g := R.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app T) ≪≫
    R.mapDerivedCategoryFactors.app T₀
  let mU := du.app _ ≪≫
    (MonoidalCategory.tensor (DerivedCategory B)).mapIso (f.prod g) ≪≫
    asIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((R.mapHomologicalComplex (.up ℤ)).obj P₀)
      ((R.mapHomologicalComplex (.up ℤ)).obj T₀))
  refine ⟨mU, rfl, ?_⟩
  have hopen := binary_square V.mapDerivedCategory DerivedCategory.Q DU SU tu du
    (L.mapDerivedCategoryFactors.hom.app P) (L.mapDerivedCategoryFactors.hom.app T)
    ((Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P))
    ((Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj T))
    f.hom g.hom (V.mapDerivedCategoryFactors.hom.app RP)
    (V.mapDerivedCategoryFactors.hom.app RT) (a.hom.app P) (a.hom.app T)
    (V.mapDerivedCategory.map modelU.hom ≫ V.mapDerivedCategoryFactors.hom.app WU ≫
      DerivedCategory.Q.map cU.hom) hmU
    (exact_forget_factors L V F R e P) (exact_forget_factors L V F R e T)
  simp only [mU, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom,
    asIso_hom, Category.assoc, Functor.comp_obj] at hopen ⊢
  rw [hopen]
  rw [reassoc_of% hr]
  rw [V.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [← DerivedCategory.Q.map_comp]
  rw [hchain]
  simp only [DerivedCategory.Q.map_comp]
  rw [← (reassoc_of% (exact_forget_factors L V F R e WZ))]
  have hn := (Functor.mapDerivedCategorySquareIso e).hom.naturality modelZ.hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [hmZ]
  simp only [Functor.map_comp, Category.assoc]
  rw [R.mapDerivedCategoryFactors_hom_naturality_assoc]
  rfl

end FinalDiagram

section RestrictionData

variable {A B C₀ : Type a} [Category.{b} A] [Category.{b} B] [Category.{b} C₀]
  [Abelian A] [Abelian B] [Abelian C₀]
  [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B] [HasDerivedCategory.{b} C₀]

private def ForgottenRestrictionSummands
    (R0 : B ⥤ A) [R0.Additive]
    [PreservesFiniteLimits R0] [PreservesFiniteColimits R0]
    (V0 : A ⥤ C₀) [V0.Additive]
    [PreservesFiniteLimits V0] [PreservesFiniteColimits V0]
    (SA0 : A → A → A) (SB0 : B → B → B)
    (TA0 : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB0 : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA0 : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB0 : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA0 : CochainComplex A ℤ → Prop) (flatB0 : CochainComplex B ℤ → Prop)
    (_hR0 : ∀ T, flatB0 T → flatA0 ((R0.mapHomologicalComplex (.up ℤ)).obj T))
    (_modelA0 : ∀ P T, flatA0 P → flatA0 T →
      (DA0.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA0.obj P).obj T)))
    (_modelB0 : ∀ P T, flatB0 P → flatB0 T →
      (DB0.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB0.obj P).obj T)))
    (iA0 : ∀ P T (p q n : ℤ), p + q = n →
      (SA0 (P.X p) (T.X q) ⟶ ((TA0.obj P).obj T).X n))
    (iB0 : ∀ P T (p q n : ℤ), p + q = n →
      (SB0 (P.X p) (T.X q) ⟶ ((TB0.obj P).obj T).X n))
    (sheafRestriction0 : ∀ M N,
      R0.obj (SB0 M N) ≅ SA0 (R0.obj M) (R0.obj N))
    (_rho0 : DB0 ⋙ R0.mapDerivedCategory ≅
      R0.mapDerivedCategory.prod R0.mapDerivedCategory ⋙ DA0)
    (total : ∀ P T,
        (R0.mapHomologicalComplex (.up ℤ)).obj ((TB0.obj P).obj T) ≅
        (TA0.obj ((R0.mapHomologicalComplex (.up ℤ)).obj P)).obj
          ((R0.mapHomologicalComplex (.up ℤ)).obj T)) : Prop :=
  (∀ P T (p q n : ℤ) (hpq : p + q = n),
        V0.map (R0.map (iB0 P T p q n hpq)) ≫ V0.map ((total P T).hom.f n) =
          V0.map (sheafRestriction0 (P.X p) (T.X q)).hom ≫
            V0.map (iA0 ((R0.mapHomologicalComplex (.up ℤ)).obj P)
              ((R0.mapHomologicalComplex (.up ℤ)).obj T) p q n hpq))

private def ForgottenRestrictionModels
    (R0 : B ⥤ A) [R0.Additive]
    [PreservesFiniteLimits R0] [PreservesFiniteColimits R0]
    (V0 : A ⥤ C₀) [V0.Additive]
    [PreservesFiniteLimits V0] [PreservesFiniteColimits V0]
    (SA0 : A → A → A) (SB0 : B → B → B)
    (TA0 : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB0 : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA0 : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB0 : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA0 : CochainComplex A ℤ → Prop) (flatB0 : CochainComplex B ℤ → Prop)
    (hR0 : ∀ T, flatB0 T → flatA0 ((R0.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA0 : ∀ P T, flatA0 P → flatA0 T →
      (DA0.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA0.obj P).obj T)))
    (modelB0 : ∀ P T, flatB0 P → flatB0 T →
      (DB0.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB0.obj P).obj T)))
    (_iA0 : ∀ P T (p q n : ℤ), p + q = n →
      (SA0 (P.X p) (T.X q) ⟶ ((TA0.obj P).obj T).X n))
    (_iB0 : ∀ P T (p q n : ℤ), p + q = n →
      (SB0 (P.X p) (T.X q) ⟶ ((TB0.obj P).obj T).X n))
    (_sheafRestriction0 : ∀ M N,
      R0.obj (SB0 M N) ≅ SA0 (R0.obj M) (R0.obj N))
    (rho0 : DB0 ⋙ R0.mapDerivedCategory ≅
      R0.mapDerivedCategory.prod R0.mapDerivedCategory ⋙ DA0)
    (total : ∀ P T,
        (R0.mapHomologicalComplex (.up ℤ)).obj ((TB0.obj P).obj T) ≅
        (TA0.obj ((R0.mapHomologicalComplex (.up ℤ)).obj P)).obj
          ((R0.mapHomologicalComplex (.up ℤ)).obj T)) : Prop :=
  (∀ P T (hP : flatB0 P) (hT : flatB0 T),
        V0.mapDerivedCategory.map
            (rho0.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
          V0.mapDerivedCategory.map
            (DA0.map (Prod.mkHom (R0.mapDerivedCategoryFactors.hom.app P)
              (R0.mapDerivedCategoryFactors.hom.app T))) ≫
          V0.mapDerivedCategory.map (modelA0 _ _ (hR0 P hP) (hR0 T hT)).hom =
        V0.mapDerivedCategory.map
            (R0.mapDerivedCategory.map (modelB0 P T hP hT).hom) ≫
          V0.mapDerivedCategory.map (R0.mapDerivedCategoryFactors.hom.app _) ≫
          V0.mapDerivedCategory.map (DerivedCategory.Q.map (total P T).hom))

private def ForgottenRestrictionResult
    (R0 : B ⥤ A) [R0.Additive]
    [PreservesFiniteLimits R0] [PreservesFiniteColimits R0]
    (V0 : A ⥤ C₀) [V0.Additive]
    [PreservesFiniteLimits V0] [PreservesFiniteColimits V0]
    (SA0 : A → A → A) (SB0 : B → B → B)
    (TA0 : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB0 : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA0 : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB0 : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA0 : CochainComplex A ℤ → Prop) (flatB0 : CochainComplex B ℤ → Prop)
    (hR0 : ∀ T, flatB0 T → flatA0 ((R0.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA0 : ∀ P T, flatA0 P → flatA0 T →
      (DA0.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA0.obj P).obj T)))
    (modelB0 : ∀ P T, flatB0 P → flatB0 T →
      (DB0.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB0.obj P).obj T)))
    (iA0 : ∀ P T (p q n : ℤ), p + q = n →
      (SA0 (P.X p) (T.X q) ⟶ ((TA0.obj P).obj T).X n))
    (iB0 : ∀ P T (p q n : ℤ), p + q = n →
      (SB0 (P.X p) (T.X q) ⟶ ((TB0.obj P).obj T).X n))
    (sheafRestriction0 : ∀ M N,
      R0.obj (SB0 M N) ≅ SA0 (R0.obj M) (R0.obj N))
    (rho0 : DB0 ⋙ R0.mapDerivedCategory ≅
      R0.mapDerivedCategory.prod R0.mapDerivedCategory ⋙ DA0)
    : Prop :=
    ∃ (total : ∀ P T,
        (R0.mapHomologicalComplex (.up ℤ)).obj ((TB0.obj P).obj T) ≅
        (TA0.obj ((R0.mapHomologicalComplex (.up ℤ)).obj P)).obj
          ((R0.mapHomologicalComplex (.up ℤ)).obj T)),
      ForgottenRestrictionSummands R0 V0 SA0 SB0 TA0 TB0 DA0 DB0 flatA0 flatB0 hR0
      modelA0 modelB0 iA0 iB0 sheafRestriction0 rho0 total ∧
      ForgottenRestrictionModels R0 V0 SA0 SB0 TA0 TB0 DA0 DB0 flatA0 flatB0 hR0
      modelA0 modelB0 iA0 iB0 sheafRestriction0 rho0 total

/-- Transport only the restriction fields of the native presentation. -/
private theorem restriction_data
    (R0 : B ⥤ A) [R0.Additive]
    [PreservesFiniteLimits R0] [PreservesFiniteColimits R0]
    (V0 : A ⥤ C₀) [V0.Additive]
    [PreservesFiniteLimits V0] [PreservesFiniteColimits V0]
    (SA0 : A → A → A) (SB0 : B → B → B)
    (TA0 : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB0 : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA0 : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB0 : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA0 : CochainComplex A ℤ → Prop) (flatB0 : CochainComplex B ℤ → Prop)
    (hR0 : ∀ T, flatB0 T → flatA0 ((R0.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA0 : ∀ P T, flatA0 P → flatA0 T →
      (DA0.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA0.obj P).obj T)))
    (modelB0 : ∀ P T, flatB0 P → flatB0 T →
      (DB0.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB0.obj P).obj T)))
    (iA0 : ∀ P T (p q n : ℤ), p + q = n →
      (SA0 (P.X p) (T.X q) ⟶ ((TA0.obj P).obj T).X n))
    (iB0 : ∀ P T (p q n : ℤ), p + q = n →
      (SB0 (P.X p) (T.X q) ⟶ ((TB0.obj P).obj T).X n))
    (sheafRestriction0 : ∀ M N,
      R0.obj (SB0 M N) ≅ SA0 (R0.obj M) (R0.obj N))
    (rho0 : DB0 ⋙ R0.mapDerivedCategory ≅
      R0.mapDerivedCategory.prod R0.mapDerivedCategory ⋙ DA0)
    (c : OpenTensorPresentation A B)
    (hc : HEq c.R R0 ∧ HEq (fun M N ↦ c.SA.obj (M, N)) SA0 ∧
      HEq (fun M N ↦ c.SB.obj (M, N)) SB0 ∧
      HEq c.TA TA0 ∧ HEq c.TB TB0 ∧ HEq c.DA DA0 ∧ HEq c.DB DB0 ∧
      HEq c.flatA flatA0 ∧ HEq c.flatB flatB0 ∧
      HEq c.modelA modelA0 ∧ HEq c.modelB modelB0 ∧
      HEq c.iA iA0 ∧ HEq c.iB iB0 ∧
      HEq c.sheafRestriction sheafRestriction0 ∧ HEq c.restriction rho0) :
    ForgottenRestrictionResult R0 V0 SA0 SB0 TA0 TB0 DA0 DB0 flatA0 flatB0 hR0
      modelA0 modelB0 iA0 iB0 sheafRestriction0 rho0 := by
  unfold ForgottenRestrictionResult ForgottenRestrictionSummands ForgottenRestrictionModels
  rcases c with @⟨E, cR, eadd, radd, elim, ecolim, rlim, rcolim, SA, SB, TA, TB,
    DA, DB, flatA, flatB, hE, hR, modelA, modelB, iA, iB, sheafGamma, totalGamma,
    summands, sheafRestriction, totalRestriction, restriction_summands, restriction,
    restriction_model, gamma', model⟩
  dsimp only at hc
  rcases hc with ⟨hr, hsa, hsb, hta, htb, hda, hdb, hfa, hfb, hma, hmb,
    hia, hib, hsr, hres⟩
  have hr := eq_of_heq hr
  subst cR
  have hsa := eq_of_heq hsa
  subst SA0
  have hsb := eq_of_heq hsb
  subst SB0
  have hta := eq_of_heq hta
  subst TA
  have htb := eq_of_heq htb
  subst TB
  have hda := eq_of_heq hda
  subst DA
  have hdb := eq_of_heq hdb
  subst DB
  have hfa := eq_of_heq hfa
  subst flatA
  have hfb := eq_of_heq hfb
  subst flatB
  have hma := eq_of_heq hma
  subst modelA
  have hmb := eq_of_heq hmb
  subst modelB
  have hia := eq_of_heq hia
  subst iA
  have hib := eq_of_heq hib
  subst iB
  have hsr := eq_of_heq hsr
  subst sheafRestriction
  have hres := eq_of_heq hres
  have restriction_model' := restriction_model
  rw [hres] at restriction_model'
  refine ⟨totalRestriction, ?_, ?_⟩
  · intro P T p q n hpq
    simpa only [Functor.map_comp] using
      congrArg V0.map (restriction_summands P T p q n hpq)
  · intro P T hP hT
    simpa only [Functor.map_comp] using
      congrArg V0.mapDerivedCategory.map (restriction_model' P T hP hT)

end RestrictionData

section OrdinarySheafRestriction

open scoped Obj

-- The two module tensor conventions are compared through their quotient formulas.
omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] [IsOpenImmersion j]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] in
private theorem ordinary_sheaf_restriction_tensor
    (M N : ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    let R := ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))));
    let G := ProEtale.upperStar (WeilCoefficients.{u} l)
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))));
    let : G.Braided :=
      { toMonoidal := inferInstance
        braided X Y := Functor.LaxBraided.braided (F := G) X Y };
    let : R.Monoidal := by
      dsimp only [R, ProEtale.adicUpperStar, Adjunction.modLeft]
      infer_instance;
    Mod.tensorObjπ (R.obj M) (R.obj N) ≫ (Functor.LaxMonoidal.μ R M N).hom =
      Functor.LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorObjπ M N) := by
  let G := ProEtale.upperStar (WeilCoefficients.{u} l)
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  let : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  dsimp only
  simp only [ProEtale.adicUpperStar, Adjunction.modLeft,
    Functor.LaxMonoidal.comp_μ, Mod.comp_hom']
  erw [Mod.tensorπ_comapTensorIso_hom_hom_assoc]
  rw [Mod.comap_map_hom]
  erw [Functor.mapMod_μ_hom]
  simpa only [Functor.mapModTensorIso_hom_hom] using
    Functor.tensorπ_mapModTensorIso_hom_hom
      (ProEtale.upperStar (WeilCoefficients.{u} l)
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))) M N

end OrdinarySheafRestriction

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] [IsOpenImmersion j]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] in
/-- On a balanced tensor summand, the inverse ordinary total comparison is the
pullback tensorator followed by the image of the ordinary insertion. -/
private theorem ordinary_restriction_total_summand
    (P T : CochainComplex (ProEtale.AdicSheaf l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    let R := ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))));
    let G := ProEtale.upperStar (WeilCoefficients.{u} l)
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))));
    Mod.tensorObjπ (R.obj (P.X p)) (R.obj (T.X q)) ≫
        (HomologicalComplex.ιTensorObj ((R.mapHomologicalComplex (.up ℤ)).obj P)
          ((R.mapHomologicalComplex (.up ℤ)).obj T) p q n hpq).hom ≫
        ((nativeOrdinaryRestrictionTotal k₀ l j P T).inv.f n).hom =
      Functor.LaxMonoidal.μ G (P.X p).X (T.X q).X ≫
        G.map (Mod.tensorObjπ (P.X p) (T.X q)) ≫
        G.map (HomologicalComplex.ιTensorObj P T p q n hpq).hom := by
  intro R G
  let : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let : R.Monoidal := by
    dsimp only [R, ProEtale.adicUpperStar, Adjunction.modLeft]
    infer_instance
  let : R.IsLeftAdjoint :=
    (ProEtale.adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).isLeftAdjoint
  change _ ≫ _ ≫ ((R.mapCochainComplexμIso P T).hom.f n).hom = _
  have hι := congrArg Mod.Hom.hom
    (R.ιTensorObj_mapCochainComplexμIso_hom_f P T p q n hpq)
  simp only [R, Mod.comp_hom', ProEtale.adicUpperStar_map_hom] at hι
  rw [hι, reassoc_of% (ordinary_sheaf_restriction_tensor k₀ l j (P.X p) (T.X q))]

-- Keep the concrete presentation types folded while transporting the restriction fields.
private theorem native_restriction_data
    (R0 : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U) [R0.Additive]
    [PreservesFiniteLimits R0] [PreservesFiniteColimits R0]
    (hR0 : ∀ T, NativeIsKFlat k₀ l Z T →
      NativeIsKFlat k₀ l U ((R0.mapHomologicalComplex (.up ℤ)).obj T))
    (sheafRestriction0 : ∀ M N,
      R0.obj (tensor k₀ l Z N M) ≅ tensor k₀ l U (R0.obj N) (R0.obj M))
    (rho0 : (nativeDerivedTensor k₀ l Z) ⋙ R0.mapDerivedCategory ≅
      R0.mapDerivedCategory.prod R0.mapDerivedCategory ⋙ (nativeDerivedTensor k₀ l U))
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (hc : HEq c.R R0 ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧ HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧ HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafRestriction sheafRestriction0 ∧ HEq c.restriction rho0) :
    ForgottenRestrictionResult R0
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U))
      (fun M N ↦ tensor k₀ l U N M) (fun M N ↦ tensor k₀ l Z N M)
      (nativeTensorTotal k₀ l U) (nativeTensorTotal k₀ l Z)
      (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
      (NativeIsKFlat k₀ l U) (NativeIsKFlat k₀ l Z) hR0
      (nativeOpenTensorModel k₀ l U) (nativeOpenTensorModel k₀ l Z)
      (nativeOpenTensorInsertion k₀ l U) (nativeOpenTensorInsertion k₀ l Z)
      sheafRestriction0 rho0 := by
  exact restriction_data (A := ProEtaleWeilSheaf k₀ l U)
      (B := ProEtaleWeilSheaf k₀ l Z) R0
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U))
      (fun M N ↦ tensor k₀ l U N M) (fun M N ↦ tensor k₀ l Z N M)
      (nativeTensorTotal k₀ l U) (nativeTensorTotal k₀ l Z)
      (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
      (NativeIsKFlat k₀ l U) (NativeIsKFlat k₀ l Z) hR0
      (nativeOpenTensorModel k₀ l U) (nativeOpenTensorModel k₀ l Z)
      (nativeOpenTensorInsertion k₀ l U) (nativeOpenTensorInsertion k₀ l Z)
      sheafRestriction0 rho0 c
      ⟨hc.1, heq_of_eq (congrArg (fun S ↦ fun M N ↦ S.obj (M, N))
          (eq_of_heq hc.2.1)),
        heq_of_eq (congrArg (fun S ↦ fun M N ↦ S.obj (M, N))
          (eq_of_heq hc.2.2.1)), hc.2.2.2⟩

/-- Paste the two balanced quotient equations with the pullback tensorator. -/
private theorem balanced_restriction_summand
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A B O W T : C} {A' B' O' W' T' : D}
    {π : A ⟶ B} {π₀ : A ⟶ O} {i : B ⟶ W} {c : W ⟶ T} {i₀ : O ⟶ T}
    {π' : A' ⟶ B'} {π₀' : A' ⟶ O'} {i' : B' ⟶ W'} {c' : W' ⟶ T'}
    {i₀' : O' ⟶ T'} {μ : T' ⟶ G.obj T}
    {μA : A' ⟶ G.obj A} {r : B' ⟶ G.obj B}
    (hu : π' ≫ i' ≫ c' = π₀' ≫ i₀')
    (ht : π₀' ≫ i₀' ≫ μ = μA ≫ G.map π₀ ≫ G.map i₀)
    (hr : π' ≫ r = μA ≫ G.map π)
    (hz : π ≫ i ≫ c = π₀ ≫ i₀) :
    π' ≫ i' ≫ c' ≫ μ = π' ≫ r ≫ G.map i ≫ G.map c := by
  rw [reassoc_of% hu, ht, reassoc_of% hr]
  simp only [← G.map_comp, hz]

/-- Identity input comparisons do not change a binary functor square. -/
private theorem binary_map_identity_square
    {C D : Type*} [Category* C] [Category* D] (S : C × C ⥤ D)
    {P T : C} {A B E : D} {a : P ⟶ P} {b : T ⟶ T} {c : A ⟶ A}
    {f : A ⟶ B} {g : B ⟶ S.obj (P, T)} {r : A ⟶ E} {s : E ⟶ S.obj (P, T)}
    (ha : a = 𝟙 P) (hb : b = 𝟙 T) (hc : c = 𝟙 A) (h : f ≫ g = r ≫ s) :
    f ≫ g ≫ S.map (Prod.mkHom a b) = c ≫ r ≫ s := by
  rw [ha, hb, hc, ← prod_id, S.map_id, Category.comp_id, Category.id_comp]
  exact h

section AbstractTransport
variable (α : (ProEtale.adicUpperStar l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))) ⋙
      WeilSheaf.frobeniusPullback k₀ l U ≅
  WeilSheaf.frobeniusPullback k₀ l Z ⋙
    (ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))))
local notation "Lα" => Endofunctor.IsoAlgebra.mapOfNatIso α

omit [Fact (ringChar k₀ ≠ l)] [IsOpenImmersion j]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] in
/-- The exact restriction-forget square is the identity on each complex. -/
private theorem native_restriction_complex_square_hom
    (K : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) :
    (complex_square (Lα)
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U))
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
      (ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
      (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso α)).hom.app K = 𝟙 _ := by
  ext n : 1
  simp only [complex_square, Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso,
    Iso.refl_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv,
    NatTrans.id_app, HomologicalComplex.id_f]
  erw [Category.comp_id]
  rfl

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] in
/-- The chain comparison follows from the balanced summand equations, independently of
any derived models. -/
private theorem native_restriction_chain
    (hL : (Lα).IsLeftAdjoint)
    (sr : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      (Lα).obj (tensor k₀ l Z N M) ≅ tensor k₀ l U ((Lα).obj N) ((Lα).obj M))
    (hsr : ∀ M N, HEq ((sr M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier))
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) :
    let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z);
    let FU := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U);
    let R := ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))));
    let RP := ((Lα).mapHomologicalComplex (.up ℤ)).obj P;
    let RT := ((Lα).mapHomologicalComplex (.up ℤ)).obj T;
    let P₀ := (F.mapHomologicalComplex (.up ℤ)).obj P;
    let T₀ := (F.mapHomologicalComplex (.up ℤ)).obj T;
    ∀ (tr : ((Lα).mapHomologicalComplex (.up ℤ)).obj
        (((nativeTensorTotal k₀ l Z).obj P).obj T) ≅
          ((nativeTensorTotal k₀ l U).obj RP).obj RT)
      (cZ : (F.mapHomologicalComplex (.up ℤ)).obj
          (((nativeTensorTotal k₀ l Z).obj P).obj T) ≅ P₀ ⊗ T₀)
      (cU : (FU.mapHomologicalComplex (.up ℤ)).obj
          (((nativeTensorTotal k₀ l U).obj RP).obj RT) ≅
        (FU.mapHomologicalComplex (.up ℤ)).obj RP ⊗
          (FU.mapHomologicalComplex (.up ℤ)).obj RT)
      (_ : ∀ (p q n : ℤ) (hpq : p + q = n),
        FU.map ((Lα).map (nativeOpenTensorInsertion k₀ l Z P T p q n hpq)) ≫
            FU.map (tr.hom.f n) =
          FU.map (sr (P.X p) (T.X q)).hom ≫
            FU.map (nativeOpenTensorInsertion k₀ l U RP RT p q n hpq))
      (_ : ∀ (p q n : ℤ) (hpq : p + q = n),
        Mod.tensorπ (P.X p).carrier (T.X q).carrier ≫
            (F.map (nativeOpenTensorInsertion k₀ l Z P T p q n hpq)).hom ≫
            (cZ.hom.f n).hom =
          Mod.tensorObjπ (P.X p).carrier (T.X q).carrier ≫
            (HomologicalComplex.ιTensorObj P₀ T₀ p q n hpq).hom)
      (_ : ∀ (p q n : ℤ) (hpq : p + q = n),
        Mod.tensorπ (RP.X p).carrier (RT.X q).carrier ≫
            (FU.map (nativeOpenTensorInsertion k₀ l U RP RT p q n hpq)).hom ≫
            (cU.hom.f n).hom =
          Mod.tensorObjπ (RP.X p).carrier (RT.X q).carrier ≫
            (HomologicalComplex.ιTensorObj
              ((FU.mapHomologicalComplex (.up ℤ)).obj RP)
              ((FU.mapHomologicalComplex (.up ℤ)).obj RT) p q n hpq).hom),
      (FU.mapHomologicalComplex (.up ℤ)).map tr.hom ≫ cU.hom =
        (R.mapHomologicalComplex (.up ℤ)).map cZ.hom ≫
          (nativeOrdinaryRestrictionTotal k₀ l j P₀ T₀).hom := by
  let := hL
  intro F FU R RP RT P₀ T₀ tr cZ cU restriction_summands hcZ hcU
  let G := ProEtale.upperStar (WeilCoefficients.{u} l)
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  dsimp only [nativeOpenTensorInsertion] at restriction_summands hcZ hcU
  dsimp only [RP, RT, Functor.mapHomologicalComplex_obj_X] at hcU
  apply (cancel_mono (nativeOrdinaryRestrictionTotal k₀ l j P₀ T₀).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map ((Lα) ⋙ FU)
    (F := (nativeTensorBifunctor k₀ l Z).flip)
  intro p q hpq
  dsimp only [Functor.comp_map]
  rw [reassoc_of% (restriction_summands p q n hpq)]
  let r := (ProEtale.adicUpperStarTensorLeftIso l
    (Scheme.Hom.geometricFiberMap j (comp_over j _)) (T.X q).carrier).app
      (P.X p).carrier
  have hs : FU.map (sr (P.X p) (T.X q)).hom = r.hom := by
    exact eq_of_heq (hsr (P.X p) (T.X q))
  conv_lhs =>
    arg 1
    rw [hs]
  apply (cancel_epi r.inv).1
  conv_lhs => rw [Iso.inv_hom_id_assoc]
  apply Mod.tensorLeft_obj_hom_ext
  simp only [Mod.comp_hom']
  simp only [R, ProEtale.adicUpperStar_map_hom]
  exact balanced_restriction_summand G (hcU p q n hpq)
    (ordinary_restriction_total_summand k₀ l j P₀ T₀ p q n hpq)
    (ProEtale.tensorπ_adicUpperStarTensorLeftIso_inv_app
      (l := l) (g := Scheme.Hom.geometricFiberMap j (comp_over j _))
        (P.X p).carrier (T.X q).carrier)
    (hcZ p q n hpq)

-- Project the model witnesses without eliminating into the concrete derived-category goal.
private theorem native_restriction_goal_proof
    (hL : (Endofunctor.IsoAlgebra.mapOfNatIso α).IsLeftAdjoint) :
  ∀ (_hR : ∀ T, NativeIsKFlat k₀ l Z T →
      NativeIsKFlat k₀ l U (((Lα).mapHomologicalComplex (.up ℤ)).obj T))
    (sr : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      (Lα).obj (tensor k₀ l Z N M) ≅ tensor k₀ l U ((Lα).obj N) ((Lα).obj M))
    (_hsr : ∀ M N, HEq ((sr M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier))
    (rho : nativeDerivedTensor k₀ l Z ⋙ (Lα).mapDerivedCategory ≅
      ((Lα).mapDerivedCategory).prod ((Lα).mapDerivedCategory) ⋙ nativeDerivedTensor k₀ l U)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (_hc :
      HEq c.R (Lα) ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧ HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧ HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafRestriction sr ∧ HEq c.restriction rho)
    (dU : NativeOrdinaryTensorIdentification k₀ l U)
    (dZ : NativeOrdinaryTensorIdentification k₀ l Z)
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ)
    (_hP : NativeIsKFlat k₀ l Z P) (_hT : NativeIsKFlat k₀ l Z T),
    let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z);
    let R := ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))));
    let P₀ := (F.mapHomologicalComplex (.up ℤ)).obj P;
    let T₀ := (F.mapHomologicalComplex (.up ℤ)).obj T;
    let M := DerivedCategory.Q.obj P;
    let N := DerivedCategory.Q.obj T;
    ∃ (mZ : (nativeForget k₀ l Z).obj ((nativeDerivedTensor k₀ l Z).obj (M, N)) ≅
        DerivedCategory.Q.obj (P₀ ⊗ T₀))
      (mU : (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor.obj
        (R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj M),
          R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj N)) ≅
        DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj P₀ ⊗
          (R.mapHomologicalComplex (.up ℤ)).obj T₀)),
      mZ.hom = (nativeDerivedClosedComparison k₀ l Z).tensorComparison.hom.app (M, N) ≫
        (dZ.tensorIso k₀ l).hom.app
          ((nativeForget k₀ l Z).obj M, (nativeForget k₀ l Z).obj N) ≫
        (MonoidalCategory.tensor _).map
          (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
            (F.mapDerivedCategoryFactors.hom.app T)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q P₀ T₀ ∧
      mU.hom = (dU.tensorIso k₀ l).hom.app
          (R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj M),
            R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj N)) ≫
        (MonoidalCategory.tensor _).map
          (Prod.mkHom
            (R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
              R.mapDerivedCategoryFactors.hom.app P₀)
            (R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app T) ≫
              R.mapDerivedCategoryFactors.hom.app T₀)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((R.mapHomologicalComplex (.up ℤ)).obj P₀)
          ((R.mapHomologicalComplex (.up ℤ)).obj T₀) ∧
      (nativeForget k₀ l U).map (rho.hom.app (M, N)) ≫
        (nativeDerivedClosedComparison k₀ l U).tensorComparison.hom.app
          (((Lα).mapDerivedCategory).obj M, ((Lα).mapDerivedCategory).obj N) ≫
        (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor.map
          (Prod.mkHom ((Functor.mapDerivedCategorySquareIso
              (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso α)).hom.app M)
            ((Functor.mapDerivedCategorySquareIso
              (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso α)).hom.app N)) ≫ mU.hom =
      (Functor.mapDerivedCategorySquareIso
          (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso α)).hom.app
        ((nativeDerivedTensor k₀ l Z).obj (M, N)) ≫
        R.mapDerivedCategory.map mZ.hom ≫ R.mapDerivedCategoryFactors.hom.app (P₀ ⊗ T₀) ≫
        DerivedCategory.Q.map (nativeOrdinaryRestrictionTotal k₀ l j P₀ T₀).hom := by
  let := hL
  intro hR sr hsr rho c _hc dU dZ P T hP hT
  have hdata := native_restriction_data k₀ l (Lα)
    hR sr rho c _hc
  let totalRestriction := hdata.choose
  have restriction_summands := hdata.choose_spec.1
  have restriction_model' := hdata.choose_spec.2
  dsimp only
  let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)
  let FU := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U)
  let R := ProEtale.adicUpperStar l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  let P₀ := (F.mapHomologicalComplex (.up ℤ)).obj P
  let T₀ := (F.mapHomologicalComplex (.up ℤ)).obj T
  have hmodelsZ := native_forget_normalized_binary_models k₀ l Z P T hP hT dZ
  let cZ := hmodelsZ.choose
  have hcZ := hmodelsZ.choose_spec.1
  have hmZ := hmodelsZ.choose_spec.2
  let mZ := (nativeForget k₀ l Z).mapIso (nativeOpenTensorModel k₀ l Z P T hP hT) ≪≫
    F.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso cZ
  have hmZ' : mZ.hom = _ := hmZ
  let RP := ((Lα).mapHomologicalComplex (.up ℤ)).obj P
  let RT := ((Lα).mapHomologicalComplex (.up ℤ)).obj T
  have hmodelsU := native_forget_normalized_binary_models k₀ l U RP RT
    (hR P hP) (hR T hT) dU
  let cU := hmodelsU.choose
  have hcU := hmodelsU.choose_spec.1
  have hmU := hmodelsU.choose_spec.2
  let e : (Lα) ⋙ FU ≅ F ⋙ R :=
    Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso α
  let ztotal := (((nativeTensorTotal k₀ l Z).obj P).obj T)
  let utotal := (((nativeTensorTotal k₀ l U).obj RP).obj RT)
  have hchain := native_restriction_chain k₀ l j α hL sr hsr P T
    (totalRestriction P T) cZ cU (restriction_summands P T) hcZ hcU
  have ha := native_restriction_complex_square_hom k₀ l j α
  have hdiagram :=
    final_total_diagram (Lα) FU F R e
      (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l U)
      (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor
      (nativeDerivedClosedComparison k₀ l U).tensorComparison (dU.tensorIso k₀ l)
      rho P T ztotal utotal
      (nativeOpenTensorModel k₀ l Z P T hP hT)
      (nativeOpenTensorModel k₀ l U RP RT (hR P hP) (hR T hT))
      (totalRestriction P T) (restriction_model' P T hP hT)
      cZ cU hmU (nativeOrdinaryRestrictionTotal k₀ l j P₀ T₀)
      (binary_map_identity_square _ (ha P) (ha T) (ha ztotal) hchain) mZ rfl
  exact ⟨mZ, hdiagram.choose, hmZ', hdiagram.choose_spec.1, hdiagram.choose_spec.2⟩

-- Preserve the named restriction functor when specializing the Frobenius comparison.
/-- Match the named pullback in the inputs before transporting its Frobenius comparison. -/
private theorem native_restriction_goal_transport
    (R0 : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    [R0.Additive] [PreservesFiniteLimits R0] [PreservesFiniteColimits R0]
    (hRdef : R0 = Endofunctor.IsoAlgebra.mapOfNatIso α)
    (e0 : R0 ⋙ Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U) ≅
      Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z) ⋙
        ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
    (hE : ∀ M, HEq (e0.hom.app M)
      (𝟙 ((ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))).obj
          M.carrier)))
    (hL : R0.IsLeftAdjoint) :
  ∀ (_hR : ∀ T, NativeIsKFlat k₀ l Z T →
      NativeIsKFlat k₀ l U ((R0.mapHomologicalComplex (.up ℤ)).obj T))
    (sr : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      R0.obj (tensor k₀ l Z N M) ≅ tensor k₀ l U (R0.obj N) (R0.obj M))
    (_hsr : ∀ M N, HEq ((sr M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier))
    (rho : nativeDerivedTensor k₀ l Z ⋙ R0.mapDerivedCategory ≅
      (R0.mapDerivedCategory).prod (R0.mapDerivedCategory) ⋙ nativeDerivedTensor k₀ l U)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (_hc :
      HEq c.R R0 ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧ HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧ HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafRestriction sr ∧ HEq c.restriction rho)
    (dU : NativeOrdinaryTensorIdentification k₀ l U)
    (dZ : NativeOrdinaryTensorIdentification k₀ l Z)
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ)
    (_hP : NativeIsKFlat k₀ l Z P) (_hT : NativeIsKFlat k₀ l Z T),
    let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z);
    let R := ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))));
    let P₀ := (F.mapHomologicalComplex (.up ℤ)).obj P;
    let T₀ := (F.mapHomologicalComplex (.up ℤ)).obj T;
    let M := DerivedCategory.Q.obj P;
    let N := DerivedCategory.Q.obj T;
    ∃ (mZ : (nativeForget k₀ l Z).obj ((nativeDerivedTensor k₀ l Z).obj (M, N)) ≅
        DerivedCategory.Q.obj (P₀ ⊗ T₀))
      (mU : (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor.obj
        (R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj M),
          R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj N)) ≅
        DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj P₀ ⊗
          (R.mapHomologicalComplex (.up ℤ)).obj T₀)),
      mZ.hom = (nativeDerivedClosedComparison k₀ l Z).tensorComparison.hom.app (M, N) ≫
        (dZ.tensorIso k₀ l).hom.app
          ((nativeForget k₀ l Z).obj M, (nativeForget k₀ l Z).obj N) ≫
        (MonoidalCategory.tensor _).map
          (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
            (F.mapDerivedCategoryFactors.hom.app T)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q P₀ T₀ ∧
      mU.hom = (dU.tensorIso k₀ l).hom.app
          (R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj M),
            R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj N)) ≫
        (MonoidalCategory.tensor _).map
          (Prod.mkHom
            (R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
              R.mapDerivedCategoryFactors.hom.app P₀)
            (R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app T) ≫
              R.mapDerivedCategoryFactors.hom.app T₀)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((R.mapHomologicalComplex (.up ℤ)).obj P₀)
          ((R.mapHomologicalComplex (.up ℤ)).obj T₀) ∧
      (nativeForget k₀ l U).map (rho.hom.app (M, N)) ≫
        (nativeDerivedClosedComparison k₀ l U).tensorComparison.hom.app
          ((R0.mapDerivedCategory).obj M, (R0.mapDerivedCategory).obj N) ≫
        (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor.map
          (Prod.mkHom ((Functor.mapDerivedCategorySquareIso e0).hom.app M)
            ((Functor.mapDerivedCategorySquareIso e0).hom.app N)) ≫ mU.hom =
      (Functor.mapDerivedCategorySquareIso e0).hom.app ((nativeDerivedTensor k₀ l Z).obj (M, N)) ≫
        R.mapDerivedCategory.map mZ.hom ≫ R.mapDerivedCategoryFactors.hom.app (P₀ ⊗ T₀) ≫
        DerivedCategory.Q.map (nativeOrdinaryRestrictionTotal k₀ l j P₀ T₀).hom := by
  subst R0
  have he0 : e0 = Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso α := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    exact eq_of_heq (hE M)
  subst e0
  exact native_restriction_goal_proof k₀ l j α hL

end AbstractTransport
end Proof

-- The concrete specialization carries the full exact-derived normalization diagram.
/-- Forgetting the native restriction presentation, compared with ordinary total models.
The two isomorphisms are pinned by the binary model equations; the assertion does
not use an ordinary derived restriction tensorator.

Source: Stacks 012Z, 0GL1, 0E8I and 015F, steps 1, 2, 4 and the native part of
step 5 of the parent representative restriction-forgetting proof.
(blueprint: lem-sf-native-restriction-forget-total-model).

Proof: restrict P,T using s.restriction_kflat, then apply
native_two_sided_kflat_forget on the ambient and open schemes. Apply
native_forget_normalized_binary_models to both pairs. Its first conjunct fixes
the chain comparisons cZ,cU on every balanced summand. In degree n precompose
with each (p,q) inclusion for p+q=n. The presentation's restriction_summands
rewrites the native total map to s.sheafRestriction. Then s.restriction_forget
identifies its underlying balanced map with ordinary module pullback. The
monoidal module pullback comparison and its totalization give exactly the
summand of nativeOrdinaryRestrictionTotal. The raw balanced quotient maps are
epimorphisms, and restriction and forgetting preserve the diagonal coproducts;
therefore the two total chain maps agree. Apply Q to this equality. Apply
nativeForget to c.restriction_model and substitute the two binary model
equations. Naturality of the exact-derived factorization moves Q(cZ), Q(cU)
and the native model maps across the restriction factors. The two successive
exact factors are the factors for the composite exact functor, so their ratio
is nativeOpenForgetPull. This identifies the ambient model with mZ in the first
equation. On the open the same substitution and naturality in the two input
factor isomorphisms gives mU in the second equation. All its factors are
invertible: the ordinary tensorator of Q is invertible on the K-flat restricted
forgotten inputs. The localized total square is the third equation. These
normalization equations determine mZ,mU uniquely. Zero complexes and empty opens
use the same coproduct equations and do not require nonempty diagonals. -/
theorem native_restriction_forget_total_model (s : NativeOpenTensorData k₀ l j)
    (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
      (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (_hc :
      HEq c.R (upperStar k₀ l j) ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧ HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧ HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction rho)
    (dU : NativeOrdinaryTensorIdentification k₀ l U)
    (dZ : NativeOrdinaryTensorIdentification k₀ l Z)
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ)
    (hP : NativeIsKFlat k₀ l Z P) (hT : NativeIsKFlat k₀ l Z T) :
    let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z);
    let R := ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))));
    let P₀ := (F.mapHomologicalComplex (.up ℤ)).obj P;
    let T₀ := (F.mapHomologicalComplex (.up ℤ)).obj T;
    let M := DerivedCategory.Q.obj P;
    let N := DerivedCategory.Q.obj T;
    ∃ (mZ : (nativeForget k₀ l Z).obj ((nativeDerivedTensor k₀ l Z).obj (M, N)) ≅
        DerivedCategory.Q.obj (P₀ ⊗ T₀))
      (mU : (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor.obj
        (R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj M),
          R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj N)) ≅
        DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj P₀ ⊗
          (R.mapHomologicalComplex (.up ℤ)).obj T₀)),
      mZ.hom = (nativeDerivedClosedComparison k₀ l Z).tensorComparison.hom.app (M, N) ≫
        (dZ.tensorIso k₀ l).hom.app
          ((nativeForget k₀ l Z).obj M, (nativeForget k₀ l Z).obj N) ≫
        (MonoidalCategory.tensor _).map
          (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
            (F.mapDerivedCategoryFactors.hom.app T)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q P₀ T₀ ∧
      mU.hom = (dU.tensorIso k₀ l).hom.app
          (R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj M),
            R.mapDerivedCategory.obj ((nativeForget k₀ l Z).obj N)) ≫
        (MonoidalCategory.tensor _).map
          (Prod.mkHom
            (R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
              R.mapDerivedCategoryFactors.hom.app P₀)
            (R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app T) ≫
              R.mapDerivedCategoryFactors.hom.app T₀)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((R.mapHomologicalComplex (.up ℤ)).obj P₀)
          ((R.mapHomologicalComplex (.up ℤ)).obj T₀) ∧
      (nativeForget k₀ l U).map (rho.hom.app (M, N)) ≫
        (nativeDerivedClosedComparison k₀ l U).tensorComparison.hom.app
          ((nativeOpenPull k₀ l j).obj M, (nativeOpenPull k₀ l j).obj N) ≫
        (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor.map
          (Prod.mkHom ((nativeOpenForgetPull k₀ l j).hom.app M)
            ((nativeOpenForgetPull k₀ l j).hom.app N)) ≫ mU.hom =
      (nativeOpenForgetPull k₀ l j).hom.app ((nativeDerivedTensor k₀ l Z).obj (M, N)) ≫
        R.mapDerivedCategory.map mZ.hom ≫ R.mapDerivedCategoryFactors.hom.app (P₀ ⊗ T₀) ≫
        DerivedCategory.Q.map (nativeOrdinaryRestrictionTotal k₀ l j P₀ T₀).hom := by
  let e : upperStar k₀ l j ⋙
      Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U) ≅
      Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z) ⋙
        ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro M N f; rfl)
  exact native_restriction_goal_transport k₀ l j
    (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso (k := k₀) l j
        (comp_over j (Spec (CommRingCat.of k₀))))
    (upperStar k₀ l j) rfl e (fun _ ↦ HEq.rfl)
    (upperStarLowerStarAdjunction k₀ l j).isLeftAdjoint
    s.restriction_kflat s.sheafRestriction s.restriction_forget rho c _hc dU dZ P T hP hT

end AlgebraicGeometry.ProEtaleWeilSheaf
