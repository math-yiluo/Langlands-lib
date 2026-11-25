/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizedDirectImageComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPullComposition
import all WeilConjectures.AlgebraicGeometry.System.SystemBlockDerivedComparison

/-! # Proper integral-to-rational coefficient comparison

Source: blueprint main-20261015, proposition-construction-independence-rf-shriek--7 (2),
finite-field coefficient calculation; Hemo--Richarz--Scholbach Lemmas 5.3(1), 5.6
(blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison).

The comparison is defined by the geometric adjunction and its specified counit.
The pullback/scalar isomorphism is the canonical conjugate, with the balanced-tensor
normalization of the imported K-flat and section-module transport statements.
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Use ordinary unification for the canonical derived functors in this proof.
set_option backward.defeqAttrib.useBackward false
-- Check the large derived-category declarations sequentially.
set_option Elab.async false
-- This module has public declarations; avoid enumerating its large private environment.
set_option linter.privateModule false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open WeilConjectures.SemilinearSections (exact_comp)

section ProofHelpers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ExactComposition
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private lemma exact_comp_hom_fac (e : F ⋙ G ≅ H)
    (K : HomotopyCategory A (.up ℤ)) :
    (exact_comp F G H e).hom.app (DerivedCategory.Qh.obj K) ≫
      H.mapDerivedCategoryFactorsh.hom.app K =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [exact_comp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryNatIso_fach]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app
    (DerivedCategory.Q.obj P))).1
  erw [Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factorsh_assoc]
  rfl

private lemma exact_comp_fac (e : F ⋙ G ≅ H) (K : HomotopyCategory A (.up ℤ)) :
    G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app K) ≫
      (exact_comp F G H e).hom.app (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
      H.mapDerivedCategoryFactorsh.inv.app K := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  apply (cancel_mono (H.mapDerivedCategoryFactorsh.hom.app _)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [exact_comp_hom_fac]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    Category.comp_id]
end ExactComposition

section HorizontalComposition
variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  [Abelian A] [Abelian B] [Abelian C] [Abelian A'] [Abelian B'] [Abelian C']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory C']
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ A') (G : B ⥤ B') (H : C ⥤ C')
  (R : A ⥤ B) (S : B ⥤ C) (T : A ⥤ C)
  (R' : A' ⥤ B') (S' : B' ⥤ C') (T' : A' ⥤ C')
  [F.Additive] [G.Additive] [H.Additive]
  [R.Additive] [S.Additive] [T.Additive] [R'.Additive] [S'.Additive] [T'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
  [PreservesFiniteLimits T'] [PreservesFiniteColimits T']
  [R.PreservesKInjectiveComplexes] [S.PreservesKInjectiveComplexes]
  [T.PreservesKInjectiveComplexes]
  (e : F ⋙ R' ≅ R ⋙ G) (d : G ⋙ S' ≅ S ⋙ H) (c : F ⋙ T' ≅ T ⋙ H)
  (r : R ⋙ S ≅ T) (s : R' ⋙ S' ≅ T')

-- Localization reduces coherence of these canonical squares to the ordinary identity.
private lemma square_horizontal
    (he : ∀ K : A, S'.map (e.hom.app K) ≫ d.hom.app (R.obj K) ≫
      H.map (r.hom.app K) = s.hom.app (F.obj K) ≫ c.hom.app K) :
    Functor.whiskerRight (derived_square F G R R' e).hom S'.mapDerivedCategory ≫
      Functor.whiskerLeft R.mapDerivedCategory (derived_square G H S S' d).hom ≫
      Functor.whiskerRight (exact_comp R S T r).hom H.rightDerivedFunctor =
    Functor.whiskerLeft F.rightDerivedFunctor (exact_comp R' S' T' s).hom ≫
      (derived_square F H T T' c).hom := by
  apply Localization.natTrans_ext (HomotopyCategory.KInjectives.Qh (C := A))
    (MorphismProperty.isomorphisms _)
  intro I
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
  let qK := (HomotopyCategory.quotient A (.up ℤ)).obj K
  apply (cancel_epi (S'.mapDerivedCategory.map (R'.mapDerivedCategory.map
    (F.rightDerivedFunctorUnit.app qK)))).1
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change S'.mapDerivedCategory.map (R'.mapDerivedCategory.map
      (F.rightDerivedFunctorUnit.app qK)) ≫
      S'.mapDerivedCategory.map ((derived_square F G R R' e).hom.app
        (DerivedCategory.Qh.obj qK)) ≫
      (derived_square G H S S' d).hom.app (R.mapDerivedCategory.obj
        (DerivedCategory.Qh.obj qK)) ≫
      H.rightDerivedFunctor.map ((exact_comp R S T r).hom.app
        (DerivedCategory.Qh.obj qK)) =
    S'.mapDerivedCategory.map (R'.mapDerivedCategory.map
      (F.rightDerivedFunctorUnit.app qK)) ≫
      (exact_comp R' S' T' s).hom.app (F.rightDerivedFunctor.obj
        (DerivedCategory.Qh.obj qK)) ≫
      (derived_square F H T T' c).hom.app (DerivedCategory.Qh.obj qK)
  have hf := square_fac F G R R' e qK
  have hg := square_fac G H S S' d ((R.mapHomotopyCategory (.up ℤ)).obj qK)
  have hn := (derived_square G H S S' d).hom.naturality
    (R.mapDerivedCategoryFactorsh.inv.app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← S'.mapDerivedCategory.map_comp_assoc, hf]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hg]
  have hfac := S'.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hfac
  erw [reassoc_of% hfac]
  erw [← H.rightDerivedFunctor.map_comp]
  erw [← H.rightDerivedFunctor.map_comp]
  erw [exact_comp_fac R S T r qK]
  have hη := H.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory r.hom (.up ℤ)).app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hη
  rw [Functor.map_comp]
  erw [← reassoc_of% hη]
  have hnat := (exact_comp R' S' T' s).hom.naturality
    (F.rightDerivedFunctorUnit.app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [reassoc_of% hnat, square_fac]
  rw [reassoc_of% (exact_comp_hom_fac R' S' T' s
    ((F.mapHomotopyCategory (.up ℤ)).obj qK))]
  have hh : (S'.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app qK) ≫
      (NatTrans.mapHomotopyCategory d.hom (.up ℤ)).app
        ((R.mapHomotopyCategory (.up ℤ)).obj qK) ≫
      (H.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory r.hom (.up ℤ)).app qK) =
    (NatTrans.mapHomotopyCategory s.hom (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj qK) ≫
      (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app qK := by
    have hc : (S'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) ≫
        (NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app
          ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (H.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app K) =
      (NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app K := by
      ext n
      exact he (K.X n)
    have hq := (HomotopyCategory.quotient C' (.up ℤ)).congr_map hc
    change (HomotopyCategory.quotient C' (.up ℤ)).map
        ((S'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K)) ≫
        (HomotopyCategory.quotient C' (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app
            ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        (HomotopyCategory.quotient C' (.up ℤ)).map
          ((H.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app K)) =
      (HomotopyCategory.quotient C' (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app
            ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        (HomotopyCategory.quotient C' (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app K)
    simpa only [Functor.map_comp] using hq
  rw [← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp_assoc]
  simp only [Category.assoc] at hh ⊢
  erw [hh]
  simp only [Functor.map_comp, Category.assoc]
  rfl
end HorizontalComposition

section AbstractPasting
variable {A B C D E F : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
  {LX : A ⥤ B} {UX : B ⥤ A} {MX : B ⥤ C} {VX : C ⥤ B}
  {LY : D ⥤ E} {UY : E ⥤ D} {MY : E ⥤ F} {VY : F ⥤ E}
  {NX : A ⥤ C} {WX : C ⥤ A} {NY : D ⥤ F} {WY : F ⥤ D}
  (ax : LX ⊣ UX) (bx : MX ⊣ VX) (cx : NX ⊣ WX)
  (ay : LY ⊣ UY) (by' : MY ⊣ VY) (cy : NY ⊣ WY)
  {G : A ⥤ D} {H : B ⥤ E} {I : C ⥤ F}
  (ka : H ⋙ UY ≅ UX ⋙ G) (kb : I ⋙ VY ≅ VX ⋙ H)
  (kc : I ⋙ WY ≅ WX ⋙ G)
  (rx : VX ⋙ UX ≅ WX) (ry : VY ⋙ UY ≅ WY)

-- Conjugate the restriction compositors and paste the two extension mates.
private theorem push_pasting
    (hc : Functor.whiskerRight kb.hom UY ≫ Functor.whiskerLeft VX ka.hom ≫
        Functor.whiskerRight rx.hom G =
      Functor.whiskerLeft I ry.hom ≫ kc.hom) :
    ∃ (ex : LX ⋙ MX ≅ NX) (ey : LY ⋙ MY ≅ NY),
      ∀ K : A,
      ey.hom.app (G.obj K) ≫ (Adjunction.pushHomOfComapIso cx cy kc).app K =
        MY.map ((Adjunction.pushHomOfComapIso ax ay ka).app K) ≫
          (Adjunction.pushHomOfComapIso bx by' kb).app (LX.obj K) ≫
          I.map (ex.hom.app K) := by
  let ex := (conjugateIsoEquiv cx (ax.comp bx)).symm rx.symm
  let ey := (conjugateIsoEquiv cy (ay.comp by')).symm ry.symm
  refine ⟨ex, ey, ?_⟩
  let α := TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso ax ay ka)
  let β := TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso bx by' kb)
  let γ := ((TwoSquare.vComp α β).whiskerRight ey.inv).whiskerLeft ex.hom
  have he : mateEquiv cx cy γ = TwoSquare.mk _ _ _ _ kc.inv := by
    have ha : mateEquiv ax ay α = TwoSquare.mk _ _ _ _ ka.inv :=
      (mateEquiv ax ay).apply_symm_apply _
    have hb : mateEquiv bx by' β = TwoSquare.mk _ _ _ _ kb.inv :=
      (mateEquiv bx by').apply_symm_apply _
    have hx : conjugateEquiv cx (ax.comp bx) ex.hom = rx.inv :=
      (conjugateEquiv cx (ax.comp bx)).apply_symm_apply _
    have hy : conjugateEquiv (ay.comp by') cy ey.inv = ry.hom :=
      (conjugateEquiv (ay.comp by') cy).apply_symm_apply _
    change mateEquiv cx cy
      (((α.vComp β).whiskerRight ey.inv).whiskerLeft ex.hom) = _
    rw [conjugateEquiv_mateEquiv_vcomp cx (ax.comp bx) cy,
      mateEquiv_conjugateEquiv_vcomp (ax.comp bx) (ay.comp by') cy,
      mateEquiv_hcomp ax ay bx by', ha, hb, hx, hy]
    ext K
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    apply (cancel_mono (kc.hom.app K)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have hcK := congr_app hc K
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at hcK
    rw [← hcK]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app_assoc]
    rw [← G.map_comp, Iso.inv_hom_id_app, G.map_id]
    rfl
  have hγ : γ = Adjunction.pushHomOfComapIso cx cy kc :=
    ((mateEquiv cx cy).injective
      (he.trans ((mateEquiv cx cy).apply_symm_apply _).symm))
  intro K
  have hh := congr_app hγ K
  dsimp [γ, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.vComp, α, β] at hh
  simp only [Category.id_comp, Category.comp_id] at hh
  rw [← hh]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
private theorem push_pasting_isIso
    (hc : Functor.whiskerRight kb.hom UY ≫ Functor.whiskerLeft VX ka.hom ≫
        Functor.whiskerRight rx.hom G =
      Functor.whiskerLeft I ry.hom ≫ kc.hom) (K : A)
    [IsIso ((Adjunction.pushHomOfComapIso ax ay ka).app K)]
    [IsIso ((Adjunction.pushHomOfComapIso bx by' kb).app (LX.obj K))] :
    IsIso ((Adjunction.pushHomOfComapIso cx cy kc).app K) := by
  obtain ⟨ex, ey, hp⟩ := push_pasting ax bx cx ay by' cy ka kb kc rx ry hc
  have : IsIso (ey.hom.app (G.obj K) ≫
      (Adjunction.pushHomOfComapIso cx cy kc).app K) := by
    rw [hp K]
    infer_instance
  exact IsIso.of_isIso_comp_left (ey.hom.app (G.obj K)) _
end AbstractPasting

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

section RestrictionComposition
variable {D : Type*} [Category D] [MonoidalCategory D]
  {A B C : D} [MonObj A] [MonObj B] [MonObj C]
  (a : A ⟶ B) [IsMonHom a] (b : B ⟶ C) [IsMonHom b]
  (c : A ⟶ C) [IsMonHom c] (e : a ≫ b = c)

private def restriction_comp_iso :
    Mod.comap (D := D) b ⋙ Mod.comap a ≅ Mod.comap c :=
  (Mod.comapComp a b).symm ≪≫ Mod.comapCongr e

private lemma restriction_comp_iso_hom (M : Mod D C) :
    ((restriction_comp_iso a b c e).hom.app M).hom = 𝟙 M.X := by
  exact Category.id_comp _
end RestrictionComposition

namespace AlgebraicGeometry.ProEtale.CondensedRing

section CoefficientComposition
variable {A B C : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj A] [MonObj B] [MonObj C]
  [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C]
  (a : A ⟶ B) [IsMonHom a] (b : B ⟶ C) [IsMonHom b]

private noncomputable def restriction_comp (X : Scheme.{u}) :
    Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (coefficientMap b X) ⋙ Mod.comap (coefficientMap a X) ≅
      Mod.comap (coefficientMap (a ≫ b) X) :=
  restriction_comp_iso (coefficientMap a X) (coefficientMap b X)
    (coefficientMap (a ≫ b) X) (coefficientMap_comp a b X).symm

omit [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C] in
private lemma restriction_comp_hom (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj C X)) :
    ((restriction_comp a b X).hom.app M).hom = 𝟙 _ :=
  restriction_comp_iso_hom _ _ _ _ M

omit [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C] in
private lemma coefficient_square_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj C X)) :
    (Mod.comap (coefficientMap a Y)).map ((comapLowerStarIso b f).hom.app M) ≫
      (comapLowerStarIso a f).hom.app ((Mod.comap (coefficientMap b X)).obj M) ≫
      (lowerStar A f).map ((restriction_comp a b X).hom.app M) =
    (restriction_comp a b Y).hom.app ((lowerStar C f).obj M) ≫
      (comapLowerStarIso (a ≫ b) f).hom.app M := by
  apply Mod.hom_ext
  change ((comapLowerStarIso b f).hom.app M).hom ≫
      ((comapLowerStarIso a f).hom.app ((Mod.comap (coefficientMap b X)).obj M)).hom ≫
      ((f)_*[Ab.{u + 1}]).map (((restriction_comp a b X).hom.app M).hom) =
    ((restriction_comp a b Y).hom.app ((lowerStar C f).obj M)).hom ≫
      ((comapLowerStarIso (a ≫ b) f).hom.app M).hom
  simp only [Mod.comapMapModComapIso_hom_app_hom, comapLowerStarIso,
    restriction_comp_hom]
  change 𝟙 _ ≫ 𝟙 _ ≫ ((f)_*[Ab.{u + 1}]).map (𝟙 M.X) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

omit [IsCommMonObj C] in
private theorem coefficient_comp_flat (X : Scheme.{u})
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap b X))] :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap (a ≫ b) X)) := by
  let := comp_preservesFiniteLimits
    (Mod.extendScalars (coefficientMap a X)) (Mod.extendScalars (coefficientMap b X))
  exact preservesFiniteLimits_of_natIso
    ((Mod.extendScalarsComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
      Mod.extendScalarsIsoOfEq (coefficientMap_comp a b X).symm)

attribute [local irreducible] derivedPushHom derivedComapLowerStarIso
  Mod.derivedExtendMapDerivedCategoryAdjunction
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars

-- Apply the abstract pasting identity to the published coefficient comparisons.
end CoefficientComposition

end AlgebraicGeometry.ProEtale.CondensedRing
end ProofHelpers

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual inclusion O_F → E on condensed rings, factored through F. All topologies
are induced from the fixed norm-topological algebraic closure.
Source: blueprint proposition-construction-independence-rf-shriek--7 (2), finite coefficient case
(blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison). -/
abbrev integralRationalCoefficientMap (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E) :=
  padicIntegersRingObjToContinuousMapRingObj.{u} ℓ F ≫
    Profinite.padicSubfieldRingObjMap ℓ i

/-- The existing total derived scalar extension along O_F → E on the indicated scheme.
Source: blueprint proposition-construction-independence-rf-shriek--7 (2), definition of T_W
(blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison). -/
abbrev integralRationalScalarExtension (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E) (X : Scheme.{u}) :=
  (Mod.extendScalars
    (coefficientMap (integralRationalCoefficientMap ℓ i) X)).leftDerivedFunctor

/-- The specified scalar/pullback comparison T_U h_A^* ≅ h_E^* T_V. The existing
conjugate construction uses the canonical restriction/direct-image identification.
Its inverse is the balanced comparison of kflat_scalar_comparison_normalization,
transported by internal_module_operations_transport and the section adjunction
normalizations. Exactness needed by this published interface is obtained from
localization O_F → F and finite free extension F → E, without an extra hypothesis.
Source: blueprint proposition-construction-independence-rf-shriek--7 (2); Stacks 03EL, 07A6
(blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison). -/
def integralRationalScalarPullIso (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E)
    {U V : Scheme.{u}} (h : U ⟶ V) :
    moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ F.1) h ⋙
        (integralRationalScalarExtension ℓ i U) ≅
      (integralRationalScalarExtension ℓ i V) ⋙
        moduleObjectDerivedPullback (Profinite.continuousMapRingObj E.1) h :=
  letI : ∀ X : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralRationalCoefficientMap ℓ i) X)) :=
    fun X ↦
      letI : PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ F)) :=
        (padicIntegers_invertEll X ℓ F).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2
      letI : PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ i)) :=
        (cartesianCoefficients_finiteFree ℓ i).2.2 X |>.2
      letI := comp_preservesFiniteLimits
        (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ F))
        (Mod.extendScalars (padicSubfieldRingObjMap X ℓ i))
      preservesFiniteLimits_of_natIso
        ((Mod.extendScalarsComp (padicIntegersToPadicSubfield X ℓ F)
          (padicSubfieldRingObjMap X ℓ i)).symm ≪≫
            Mod.extendScalarsIsoOfEq (coefficientMap_comp
              (padicIntegersRingObjToContinuousMapRingObj ℓ F)
              (Profinite.padicSubfieldRingObjMap ℓ i) X).symm)
  derivedPullIso (integralRationalCoefficientMap ℓ i) h

/-- The coefficient projection arrow, defined as the transpose of the inverse
scalar/pullback comparison followed by scalar extension of the A-counit.
Source: blueprint proposition-construction-independence-rf-shriek--7 (2), displayed definition of
rho (blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison). -/
def properIntegralRationalScalarComparison (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E)
    {U V : Scheme.{u}} (h : U ⟶ V)
    (J : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) U))) :
    (integralRationalScalarExtension ℓ i V).obj
          ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ F.1) h).obj J) ⟶
      (moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) h).obj
        ((integralRationalScalarExtension ℓ i U).obj J) :=
  letI : ∀ X : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralRationalCoefficientMap ℓ i) X)) :=
    fun X ↦
      letI : PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ F)) :=
        (padicIntegers_invertEll X ℓ F).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2
      letI : PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ i)) :=
        (cartesianCoefficients_finiteFree ℓ i).2.2 X |>.2
      letI := comp_preservesFiniteLimits
        (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ F))
        (Mod.extendScalars (padicSubfieldRingObjMap X ℓ i))
      preservesFiniteLimits_of_natIso
        ((Mod.extendScalarsComp (padicIntegersToPadicSubfield X ℓ F)
          (padicSubfieldRingObjMap X ℓ i)).symm ≪≫
            Mod.extendScalarsIsoOfEq (coefficientMap_comp
              (padicIntegersRingObjToContinuousMapRingObj ℓ F)
              (Profinite.padicSubfieldRingObjMap ℓ i) X).symm)
  (derivedPushHom (integralRationalCoefficientMap ℓ i) h).app J

set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] derivedPushHom derivedComapLowerStarIso
  Mod.derivedExtendMapDerivedCategoryAdjunction derivedUpperStarLowerStarAdjunction
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars

attribute [local irreducible] Mod.extendRestrictAdjunction
  properIntegralRationalScalarComparison
  integralRationalScalarPullIso

end AlgebraicGeometry.ProEtale.CondensedRing
