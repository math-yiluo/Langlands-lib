/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Composition coherence of the specified integral pull comparisons -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u₀ u₁ u₂ u₃ u₄ u₅ v₀ v₁ v₂ v₃ v₄ v₅
private lemma conjugate_associator_inv
    {A : Type u₀} {B : Type u₁} {C : Type u₂} {D : Type u₃}
    [Category.{v₀} A] [Category.{v₁} B] [Category.{v₂} C] [Category.{v₃} D]
    {L₀ : A ⥤ B} {R₀ : B ⥤ A} {L₁ : B ⥤ C} {R₁ : C ⥤ B}
    {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) :
    conjugateEquiv ((a₀.comp a₁).comp a₂) (a₀.comp (a₁.comp a₂))
        (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv := by
  apply (cancel_mono (Functor.associator R₂ R₁ R₀).hom).1
  conv_lhs => rw [← conjugateEquiv_associator_hom a₀ a₁ a₂]
  rw [conjugateEquiv_comp, Iso.hom_inv_id, conjugateEquiv_id, Iso.inv_hom_id]

section
variable {A₀ : Type u₀} {A₁ : Type u₁} {A₂ : Type u₂}
  {B₀ : Type u₃} {B₁ : Type u₄} {B₂ : Type u₅}
  [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} A₂]
  [Category.{v₃} B₀] [Category.{v₄} B₁] [Category.{v₅} B₂]
  {E₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀} (a₀ : E₀ ⊣ R₀)
  {E₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} (a₁ : E₁ ⊣ R₁)
  {E₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂} (a₂ : E₂ ⊣ R₂)
  {U : A₁ ⥤ A₀} {F : A₀ ⥤ A₁} (af : U ⊣ F)
  {V : A₂ ⥤ A₁} {G : A₁ ⥤ A₂} (ag : V ⊣ G)
  {W : A₂ ⥤ A₀} {H : A₀ ⥤ A₂} (ah : W ⊣ H)
  {U' : B₁ ⥤ B₀} {F' : B₀ ⥤ B₁} (af' : U' ⊣ F')
  {V' : B₂ ⥤ B₁} {G' : B₁ ⥤ B₂} (ag' : V' ⊣ G')
  {W' : B₂ ⥤ B₀} {H' : B₀ ⥤ B₂} (ah' : W' ⊣ H')
  (ef : F' ⋙ R₁ ≅ R₀ ⋙ F) (eg : G' ⋙ R₂ ≅ R₁ ⋙ G)
  (eh : H' ⋙ R₂ ≅ R₀ ⋙ H)
  (c : W ≅ V ⋙ U) (c' : W' ≅ V' ⋙ U')
  (r : F ⋙ G ≅ H) (r' : F' ⋙ G' ≅ H')
  (hc : conjugateEquiv (ag.comp af) ah c.hom = r.hom)
  (hc' : conjugateEquiv (ag'.comp af') ah' c'.hom = r'.hom)

include hc hc' in
private lemma pull_comparison_pasting
    (he : Functor.whiskerRight r'.hom R₂ ≫ eh.hom =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft F' eg.hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ef.hom G ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft R₀ r.hom) :
    Functor.whiskerRight c.hom E₀ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft V (Adjunction.pullIsoOfComapIso a₀ a₁ af af' ef).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Adjunction.pullIsoOfComapIso a₁ a₂ ag ag' eg).hom U' =
      (Adjunction.pullIsoOfComapIso a₀ a₂ ah ah' eh).hom ≫
        Functor.whiskerLeft E₂ c'.hom ≫ (Functor.associator _ _ _).inv := by
  apply (conjugateEquiv ((a₂.comp ag').comp af') (ah.comp a₀)).injective
  rw [← conjugateEquiv_comp _ ((ag.comp af).comp a₀),
    ← conjugateEquiv_comp _ (ag.comp (af.comp a₀)),
    ← conjugateEquiv_comp _ (ag.comp (a₁.comp af')),
    ← conjugateEquiv_comp _ ((ag.comp a₁).comp af'),
    ← conjugateEquiv_comp _ (a₂.comp ah'),
    ← conjugateEquiv_comp _ (a₂.comp (ag'.comp af'))]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, Adjunction.pullIsoOfComapIso,
    conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply, hc, hc', conjugate_associator_inv]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun t ↦ (Functor.associator F' G' R₂).inv ≫ t) he.symm
end

section
variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory C'] [HasDerivedCategory D']
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions C']

private lemma comp_unit_app (F : C ⥤ D) (G : D ⥤ D') [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app K =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) := by
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) K
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, hi]
  erw [DerivedCategory.Qh.map_id]
  dsimp
  simp only [Category.id_comp, Category.comp_id]

omit [Abelian.HasKInjectiveResolutions D] in
private lemma comp_map_fac (F : C ⥤ D) (S : D ⥤ D') [F.Additive] [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (K : HomotopyCategory C (.up ℤ)) :
    (F ⋙ S).rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F S).hom.app
          (DerivedCategory.Qh.obj K) =
      S.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        S.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) := by
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app']

private lemma comp_fac (F : C ⥤ D) (G : D ⥤ D') (H : C ⥤ D')
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app K ≫
        (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
        H.rightDerivedFunctorUnit.app K := by
  have hc : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  have h : Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh ≫
        H.rightDerivedFunctorUnit := by
    rw [← hc, Category.assoc, ← Functor.whiskerLeft_comp]
    simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
    rw [Iso.hom_inv_id_assoc]
    exact Functor.rightDerivedNatTrans_fac _ _ _ _
      (HomotopyCategory.quasiIso C (.up ℤ)) _
  exact congr_app h K

private noncomputable def derived_square (F : C ⥤ D) (G : C' ⥤ D')
    (R : C ⥤ C') (S : D ⥤ D') [F.Additive] [G.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [R.PreservesKInjectiveComplexes] (e : F ⋙ S ≅ R ⋙ G) :
    F.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅ R.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F S).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫ Functor.rightDerivedFunctorCompIso R G ≪≫
      Functor.isoWhiskerRight R.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor

omit [Abelian.HasKInjectiveResolutions D] in
private lemma square_fac (F : C ⥤ D) (G : C' ⥤ D')
    (R : C ⥤ C') (S : D ⥤ D') [F.Additive] [G.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [R.PreservesKInjectiveComplexes] (e : F ⋙ S ≅ R ⋙ G)
    (K : HomotopyCategory C (.up ℤ)) :
    S.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
        (derived_square F G R S e).hom.app (DerivedCategory.Qh.obj K) =
      S.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
        G.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (R.mapDerivedCategoryFactorsh.inv.app K) := by
  apply (cancel_epi (S.mapDerivedCategoryFactorsh.inv.app
    ((F.mapHomotopyCategory (.up ℤ)).obj K))).1
  simp only [← Category.assoc, ← comp_map_fac F S K]
  simp only [derived_square, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc,
    Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
  erw [Functor.rightDerivedNatTrans_app_assoc]
  have hc : (R ⋙ G).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompIso R G).hom.app (DerivedCategory.Qh.obj K) =
      (Functor.rightDerivedFunctorCompUnit R G).app K := by
    simp [Functor.rightDerivedFunctorCompIso]
  simp only [Functor.whiskerRight_app]
  erw [reassoc_of% hc]
  rw [comp_unit_app]
  simp only [Category.assoc, ← Functor.map_comp]
  have hr := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hr
  rw [hr]
end

section Composition
variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  [Abelian A] [Abelian B] [Abelian C] [Abelian A'] [Abelian B'] [Abelian C']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory C']
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions A'] [Abelian.HasKInjectiveResolutions B']
  [Abelian.HasKInjectiveResolutions C']
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
  (F' : A' ⥤ B') (G' : B' ⥤ C') (H' : A' ⥤ C')
  (R₀ : A' ⥤ A) (R₁ : B' ⥤ B) (R₂ : C' ⥤ C)
  [F.Additive] [G.Additive] [H.Additive] [F'.Additive] [G'.Additive] [H'.Additive]
  [R₀.Additive] [R₁.Additive] [R₂.Additive]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [F.PreservesKInjectiveComplexes] [F'.PreservesKInjectiveComplexes]
  [R₀.PreservesKInjectiveComplexes] [R₁.PreservesKInjectiveComplexes]
  (ef : F' ⋙ R₁ ≅ R₀ ⋙ F) (eg : G' ⋙ R₂ ≅ R₁ ⋙ G)
  (eh : H' ⋙ R₂ ≅ R₀ ⋙ H) (r : F ⋙ G ≅ H) (r' : F' ⋙ G' ≅ H')

omit [Abelian.HasKInjectiveResolutions C'] in
private lemma square_comp
    (he : ∀ K : A', R₂.map (r'.hom.app K) ≫ eh.hom.app K =
      eg.hom.app (F'.obj K) ≫ G.map (ef.hom.app K) ≫ r.hom.app (R₀.obj K)) :
    Functor.whiskerRight (Functor.rightDerivedFunctorCompIso' F' G' r').hom
        R₂.mapDerivedCategory ≫ (derived_square H' H R₀ R₂ eh).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft F'.rightDerivedFunctor (derived_square G' G R₁ R₂ eg).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derived_square F' F R₀ R₁ ef).hom G.rightDerivedFunctor ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft R₀.mapDerivedCategory
          (Functor.rightDerivedFunctorCompIso' F G r).hom := by
  apply Localization.natTrans_ext (HomotopyCategory.KInjectives.Qh (C := A'))
    (MorphismProperty.isomorphisms _)
  intro I
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
  let qK := (HomotopyCategory.quotient A' (.up ℤ)).obj K
  have : IsIso ((Functor.rightDerivedFunctorCompUnit F' G').app qK) := inferInstance
  apply (cancel_epi (R₂.mapDerivedCategory.map
    ((Functor.rightDerivedFunctorCompUnit F' G').app qK))).1
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  change R₂.mapDerivedCategory.map ((Functor.rightDerivedFunctorCompUnit F' G').app qK) ≫
      R₂.mapDerivedCategory.map ((Functor.rightDerivedFunctorCompIso' F' G' r').hom.app
        (DerivedCategory.Qh.obj qK)) ≫
      (derived_square H' H R₀ R₂ eh).hom.app (DerivedCategory.Qh.obj qK) =
    R₂.mapDerivedCategory.map ((Functor.rightDerivedFunctorCompUnit F' G').app qK) ≫
      (derived_square G' G R₁ R₂ eg).hom.app (F'.rightDerivedFunctor.obj
        (DerivedCategory.Qh.obj qK)) ≫
      G.rightDerivedFunctor.map ((derived_square F' F R₀ R₁ ef).hom.app
        (DerivedCategory.Qh.obj qK)) ≫
      (Functor.rightDerivedFunctorCompIso' F G r).hom.app
        (R₀.mapDerivedCategory.obj (DerivedCategory.Qh.obj qK))
  have hh :
      (R₂.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory r'.hom (.up ℤ)).app qK) ≫
        (NatTrans.mapHomotopyCategory eh.hom (.up ℤ)).app qK =
      (NatTrans.mapHomotopyCategory eg.hom (.up ℤ)).app
          ((F'.mapHomotopyCategory (.up ℤ)).obj qK) ≫
        (G.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory ef.hom (.up ℤ)).app qK) ≫
        (NatTrans.mapHomotopyCategory r.hom (.up ℤ)).app
          ((R₀.mapHomotopyCategory (.up ℤ)).obj qK) := by
    have hcomplex : (R₂.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex r'.hom (.up ℤ)).app K) ≫
        (NatTrans.mapHomologicalComplex eh.hom (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex eg.hom (.up ℤ)).app
          ((F'.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex ef.hom (.up ℤ)).app K) ≫
        (NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app
          ((R₀.mapHomologicalComplex (.up ℤ)).obj K) := by
      ext n
      exact he (K.X n)
    have hq := (HomotopyCategory.quotient C (.up ℤ)).congr_map hcomplex
    simpa only [qK, NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_obj,
      Functor.mapHomotopyCategory_map, HomotopyCategory.quotient_obj_as,
      Functor.map_comp] using hq
  have hf := square_fac F' F R₀ R₁ ef qK
  have hg := square_fac G' G R₁ R₂ eg ((F'.mapHomotopyCategory (.up ℤ)).obj qK)
  have hηg := (derived_square G' G R₁ R₂ eg).hom.naturality
    (F'.rightDerivedFunctorUnit.app qK)
  have hηF := G.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory ef.hom (.up ℤ)).app qK)
  have hp := (Functor.rightDerivedFunctorCompIso' F G r).hom.naturality
    (R₀.mapDerivedCategoryFactorsh.inv.app qK)
  have hn := R₂.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory r'.hom (.up ℤ)).app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hηg hηF hp hn
  rw [← Functor.map_comp_assoc, comp_fac]
  rw [Functor.map_comp, Category.assoc, square_fac]
  erw [reassoc_of% hn]
  rw [comp_unit_app, Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hηg, reassoc_of% hg]
  rw [← Functor.map_comp_assoc G.rightDerivedFunctor,
    ← Functor.map_comp_assoc G.rightDerivedFunctor]
  simp only [Category.assoc]
  rw [hf]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hηF, hp]
  erw [← reassoc_of% (comp_unit_app F G
    ((R₀.mapHomotopyCategory (.up ℤ)).obj qK))]
  erw [reassoc_of% (comp_fac F G H r ((R₀.mapHomotopyCategory (.up ℤ)).obj qK))]
  erw [← DerivedCategory.Qh.map_comp_assoc, hh]
  simp only [Functor.map_comp, Category.assoc]
  rfl
end Composition

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

local instance instEssentiallySmallProfinite_continuousIntegralPullComposition
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.leftDerivedFunctorIsoMapDerivedCategory

section Underived

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
private lemma comap_lowerStar_hom {S T : Scheme.{u}} (h : S ⟶ T)
    (M : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)) :
    ((comapLowerStarIso a h).hom.app M).hom = 𝟙 _ :=
  Mod.comapMapModComapIso_hom_app_hom _ _ _ _ _ _ M

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
private lemma comap_lowerStar_comp
    (K : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :
    (Mod.comap (coefficientMap a Z)).map ((lowerStarComp Λ' f g).hom.app K) ≫
        (comapLowerStarIso a (f ≫ g)).hom.app K =
      (comapLowerStarIso a g).hom.app ((f)_*⟦Λ'⟧.obj K) ≫
        (g)_*⟦Λ⟧.map ((comapLowerStarIso a f).hom.app K) ≫
        (lowerStarComp Λ f g).hom.app ((Mod.comap (coefficientMap a X)).obj K) := by
  apply Mod.hom_ext
  change ((lowerStarComp Λ' f g).hom.app K).hom ≫
      ((comapLowerStarIso a (f ≫ g)).hom.app K).hom =
    ((comapLowerStarIso a g).hom.app ((f)_*⟦Λ'⟧.obj K)).hom ≫
      (g)_*[Ab.{u + 1}].map (((comapLowerStarIso a f).hom.app K).hom) ≫
      ((lowerStarComp Λ f g).hom.app ((Mod.comap (coefficientMap a X)).obj K)).hom
  simp only [comap_lowerStar_hom, Category.id_comp]
  change ((lowerStarComp Λ' f g).hom.app K).hom ≫
      𝟙 ((f ≫ g)_*[Ab.{u + 1}].obj K.X) =
    (g)_*[Ab.{u + 1}].map (𝟙 ((f)_*[Ab.{u + 1}].obj K.X)) ≫
      ((lowerStarComp Λ f g).hom.app ((Mod.comap (coefficientMap a X)).obj K)).hom
  erw [Category.comp_id]

private lemma lowerStar_preservesKInjectives
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T : Scheme.{u}} (h : S ⟶ T) :
    (h)_*⟦Λ⟧.PreservesKInjectiveComplexes :=
  (upperStarLowerStarAdjunction Λ h).preservesKInjectiveComplexes

attribute [local instance] lowerStar_preservesKInjectives

private lemma derived_lowerStar_conjugate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    conjugateEquiv ((derivedUpperStarLowerStarAdjunction Λ g).comp
        (derivedUpperStarLowerStarAdjunction Λ f))
        (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
        (leftDerivedUpperStarComp Λ f g).hom =
      (Functor.rightDerivedFunctorCompIso' (f)_*⟦Λ⟧ (g)_*⟦Λ⟧
        (lowerStarComp Λ f g)).hom := by
  have hadj {S T : Scheme.{u}} (h : S ⟶ T) :
      (upperStarLowerStarAdjunction Λ h).mapDerivedCategoryRightDerivedAdjunction =
        (derivedUpperStarLowerStarAdjunction Λ h).ofNatIsoLeft
          (h)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory := by
    refine ((upperStarLowerStarAdjunction Λ h).mapHomotopyCategory (.up ℤ)
      ).derived_eq_ofNatIsoLeft (HomotopyCategory.quasiIso _ (.up ℤ))
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
      (h)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.symm ?_
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom]
    have hfac := congr_app
      (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac (h)^*⟦Λ⟧) K
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hfac
    exact (Iso.eq_inv_comp
      ((h)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.app
        (DerivedCategory.Qh.obj K))).2 hfac
  rw [Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ g)
    (upperStarLowerStarAdjunction Λ (f ≫ g)) _ (upperStarComp Λ f g) (by
      change _ = (conjugateEquiv _ _) ((conjugateEquiv _ _).symm _)
      exact (Equiv.apply_symm_apply _ _).symm)]
  simp only [hadj]
  ext K
  simp [conjugateEquiv_apply_app, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso]

variable [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]

private lemma derived_comap_comp :
    Functor.whiskerRight
        (Functor.rightDerivedFunctorCompIso' (f)_*⟦Λ'⟧ (g)_*⟦Λ'⟧
          (lowerStarComp Λ' f g)).hom D(Mod.comap (coefficientMap a Z)) ≫
        (derivedComapLowerStarIso a (f ≫ g)).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft R((f)_*⟦Λ'⟧) (derivedComapLowerStarIso a g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedComapLowerStarIso a f).hom R((g)_*⟦Λ⟧) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft D(Mod.comap (coefficientMap a X))
          (Functor.rightDerivedFunctorCompIso' (f)_*⟦Λ⟧ (g)_*⟦Λ⟧
            (lowerStarComp Λ f g)).hom := by
  exact square_comp (f)_*⟦Λ⟧ (g)_*⟦Λ⟧ (f ≫ g)_*⟦Λ⟧
    (f)_*⟦Λ'⟧ (g)_*⟦Λ'⟧ (f ≫ g)_*⟦Λ'⟧
    (Mod.comap (coefficientMap a X)) (Mod.comap (coefficientMap a Y))
    (Mod.comap (coefficientMap a Z))
    (comapLowerStarIso a f) (comapLowerStarIso a g) (comapLowerStarIso a (f ≫ g))
    (lowerStarComp Λ f g) (lowerStarComp Λ' f g) (comap_lowerStar_comp a f g)

private lemma derived_pull_comp :
    Functor.whiskerRight (leftDerivedUpperStarComp Λ f g).hom
        L(Mod.extendScalars (coefficientMap a X)) ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L((g)^*⟦Λ⟧) (derivedPullIso a f).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedPullIso a g).hom L((f)^*⟦Λ'⟧) =
      (derivedPullIso a (f ≫ g)).hom ≫
        Functor.whiskerLeft L(Mod.extendScalars (coefficientMap a Z))
          (leftDerivedUpperStarComp Λ' f g).hom ≫ (Functor.associator _ _ _).inv := by
  exact pull_comparison_pasting
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Z))
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ g)
    (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (derivedUpperStarLowerStarAdjunction Λ' f) (derivedUpperStarLowerStarAdjunction Λ' g)
    (derivedUpperStarLowerStarAdjunction Λ' (f ≫ g))
    (derivedComapLowerStarIso a f) (derivedComapLowerStarIso a g)
    (derivedComapLowerStarIso a (f ≫ g))
    (leftDerivedUpperStarComp Λ f g) (leftDerivedUpperStarComp Λ' f g)
    (Functor.rightDerivedFunctorCompIso' (f)_*⟦Λ⟧ (g)_*⟦Λ⟧ (lowerStarComp Λ f g))
    (Functor.rightDerivedFunctorCompIso' (f)_*⟦Λ'⟧ (g)_*⟦Λ'⟧ (lowerStarComp Λ' f g))
    (derived_lowerStar_conjugate f g Λ) (derived_lowerStar_conjugate f g Λ')
    (derived_comap_comp a f g)

end Underived

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

private lemma bounded_comp_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ V)) :
    ((boundedConstructibleUpperStarComp Λ ℓ
        (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).hom.app K).hom =
      (leftDerivedUpperStarComp Λ h j).hom.app K.obj := by
  change (boundedConstructible _).ι.map
    ((boundedConstructibleUpperStarComp Λ ℓ
        (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).hom.app K) = _
  simp only [ObjectProperty.ι_obj, Functor.comp_obj, boundedConstructibleUpperStarComp,
    Functor.FullyFaithful.preimageIso, Functor.whiskeringRight_obj_obj,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso, Iso.trans_hom,
    Iso.refl_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Iso.refl_inv, Functor.FullyFaithful.preimage_comp, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Category.assoc, Functor.isoWhiskerRight_inv, NatTrans.comp_app,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.id_app,
    ObjectProperty.lift_obj_obj, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, CategoryTheory.Functor.map_id,
    Functor.associator_hom_app, Category.comp_id,
    ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
  exact Category.id_comp ((leftDerivedUpperStarComp Λ h j).hom.app K.obj)

/-- The specified scalar-extension/pullback comparison respects composition.
Source: Bhatt--Scholze, Remark 6.8.15, and the canonical constructions
`comapLowerStarIso`, `derivedComapLowerStarIso`, `derivedPullIso`, and
`leftDerivedUpperStarComp` in ChangeOfCoefficients.lean and Derived/UpperLowerStar.lean.
(blueprint: lem-weil-pbc-continuous-integral-pull-composition).

Proof. Write T for integral scalar extension and α for its pull comparison. Before deriving,
the restriction-of-scalars/pushforward comparison has identity underlying sheaf components.
For h followed by j its composition square commutes, since the underlying components of
both coefficient pushforward composition isomorphisms are the same sheaf pushforward
composition isomorphism. All three pushforwards and scalar restrictions preserve K-injective
complexes: their left adjoints are exact. Derive the composition square using the canonical
composition units. On K-injective complexes those units are isomorphisms; cancel them and
use the underived square. Every derived object has a K-injective representative, so the
derived square commutes on all objects. The exact-restriction identification R(Res) ≅ D(Res)
is the unique comparison with its specified unit, and hence preserves that square.
Conjugate the derived square through the scalar and pullback adjunctions. Conjugation
reverses vertical composition, interchanges left and right whiskering, and sends the
associator to the reversed associator. Thus its two paths give the α_h, α_j composite and
α_(h≫j). The pullback composition comparison used here is the specified one: the underived
comparison is conjugate to pushforward composition, and the right-derived composition
conjugation theorem identifies its conjugate with the left-derived comparison obtained
from the exact levelwise functors. Finally restrict along the fully faithful bounded
constructible inclusions. Their composition comparison is the lift of that same derived
comparison, so equality of the ambient isomorphisms gives the displayed equality. -/
theorem integralConstructiblePullIso_comp
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : integralConstructible ℓ E V) :
    (integralScalarConstructible ℓ E T).mapIso
        ((boundedConstructibleUpperStarComp (integralCoeff ℓ E) ℓ
          (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).app K) ≪≫
      integralConstructiblePullIso ℓ E k h
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (j.asOver (Spec (.of k)))).obj K) ≪≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (h.asOver (Spec (.of k)))).mapIso
        (integralConstructiblePullIso ℓ E k j K) =
    integralConstructiblePullIso ℓ E k (h ≫ j) K ≪≫
      (boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ
        (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).app
        ((integralScalarConstructible ℓ E V).obj K) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  dsimp only [Iso.trans, Functor.mapIso, Iso.app,
    ObjectProperty.FullSubcategory.comp_hom]
  dsimp only [integralScalarConstructible, boundedConstructibleUpperStar,
    integralConstructiblePullIso, ObjectProperty.lift, ObjectProperty.isoMk,
    ObjectProperty.homMk, Functor.comp_map, ObjectProperty.ι_map]
  conv_lhs =>
    lhs
    arg 2
    rw [bounded_comp_hom ℓ k (integralCoeff ℓ E) h j K]
  conv_rhs =>
    rhs
    erw [bounded_comp_hom ℓ k (Profinite.continuousMapRingObj E) h j
      ((integralScalarConstructible ℓ E V).obj K)]
  have he := congr_app (derived_pull_comp (integralScalarMap ℓ E) h j) K.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at he
  convert he using 1 <;>
    dsimp only [integralScalarConstructible, integralScalarExtension,
      ObjectProperty.lift_obj_obj, Functor.comp_obj, ObjectProperty.ι_obj, Iso.app_hom,
      Scheme.Hom.asOver, OverClass.asOverHom, OverClass.asOver, Over.homMk,
      CostructuredArrow.homMk, Over.mk, CostructuredArrow.mk]

end AlgebraicGeometry.ProEtale.CondensedRing
