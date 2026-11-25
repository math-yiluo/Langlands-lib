/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SixFunctors.ProEtale.IntegralReductionTransitionComparison
import all WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import all WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.Algebra.Homology.Localization

/-! Compatibility of the compact-support input reduction with the completed tower. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open AlgebraicGeometry.ProEtale.IntegralPresentation
section IntegralReductionTransitionHelpers

open WeilConjectures
open scoped CategoryTheory.Obj
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionDerivedExtension scalarReductionExtension scalarReductionCounit
  normalizedDVRResCompletedComp normalizedDVRKFlatComparison
namespace AlgebraicGeometry.ProEtale.IntegralPresentation
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private def testDatum (p : ℕ) (hp : p.Prime) : FiniteFieldDatum.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }

private theorem existsTestDatum (l : ℕ) : ∃ D : FiniteFieldDatum.{0}, l ≠ D.p := by
  by_cases h : l = 2
  · exact ⟨testDatum 3 (by decide), by simp [testDatum, h]⟩
  · exact ⟨testDatum 2 (by decide), h⟩

/-- The restricted adjoint of the smaller reduction unit. -/
private def adjointTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (T : B ⥤ A) (d : T ⋙ Rm ≅ Rn) :
    Lm ⋙ Rm ⟶ Ln ⋙ Rn where
  app M := Rm.map ((am.homEquiv M (T.obj (Ln.obj M))).symm
      (an.unit.app M ≫ d.inv.app (Ln.obj M))) ≫ d.hom.app (Ln.obj M)
  naturality {M N} f := by
    have h : Lm.map f ≫
        (am.homEquiv N (T.obj (Ln.obj N))).symm
          (an.unit.app N ≫ d.inv.app (Ln.obj N)) =
        (am.homEquiv M (T.obj (Ln.obj M))).symm
          (an.unit.app M ≫ d.inv.app (Ln.obj M)) ≫ T.map (Ln.map f) := by
      apply (am.homEquiv _ _).injective
      rw [am.homEquiv_naturality_left, Equiv.apply_symm_apply,
        am.homEquiv_naturality_right, Equiv.apply_symm_apply]
      dsimp only [Functor.comp_obj, Functor.comp_map]
      have hu := an.unit.naturality f
      dsimp only [Functor.id_map, Functor.comp_map] at hu
      rw [reassoc_of% hu]
      simpa only [Category.assoc, Functor.comp_map] using
        congrArg (fun k ↦ an.unit.app M ≫ k) (d.inv.naturality (Ln.map f))
    dsimp only [Functor.comp_map]
    rw [← Rm.map_comp_assoc, h, Rm.map_comp, Category.assoc]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (fun k ↦ Rm.map ((am.homEquiv M (T.obj (Ln.obj M))).symm
        (an.unit.app M ≫ d.inv.app (Ln.obj M))) ≫ k)
      (d.hom.naturality (Ln.map f))

private theorem normalizeRepresentativeTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (T : B ⥤ A) (d : T ⋙ Rm ≅ Rn)
    (P V W : C) (cm : Rm.obj (Lm.obj P) ⟶ V) (cn : Rn.obj (Ln.obj P) ⟶ W)
    (f : V ⟶ W)
    (h : Rm.map ((am.homEquiv P (T.obj (Ln.obj P))).symm
        (an.unit.app P ≫ d.inv.app (Ln.obj P))) ≫ d.hom.app (Ln.obj P) ≫
        Rn.map (Ln.map (Iso.refl P).inv) ≫ cn =
      Rm.map (Lm.map (Iso.refl P).inv) ≫ cm ≫ f) :
    (adjointTransition am an T d).app P ≫ cn = cm ≫ f := by
  simpa [adjointTransition] using h

attribute [local irreducible] Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized comparison is the representative comparison. -/
private theorem normalizedDVRKFlatComparison_eq (m : ℕ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ) :
    normalizedDVRKFlatComparison.{u, u} l E X m P =
      sfReductionRepresentativeComparison l E X m P := by
  unfold normalizedDVRKFlatComparison sfReductionRepresentativeComparison
  rw [cast_eq]
  erw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have e1 : (scalarReductionDerivedExtension l E X m).map
      ((DerivedCategory.quotientCompQhIso _).inv.app P) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have e2 : DerivedCategory.Qh.map
      (((scalarReductionExtension l E X m).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) =
        𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have e3 : (DerivedCategory.quotientCompQhIso (scalarReductionTarget l E X m)).hom.app
      (unrestrictedTowerFiniteComplex l E X m P) = 𝟙 _ := rfl
  have e4 : (scalarReductionRestriction l E X m).mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso (scalarReductionTarget l E X m)).hom.app
        (((scalarReductionExtension l E X m).mapHomologicalComplex (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P).as)) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have e5 : (DerivedCategory.quotientCompQhIso (scalarReductionSource l E X)).inv.app
      (((scalarReductionRestriction l E X m).mapHomologicalComplex (.up ℤ)).obj
        (((scalarReductionExtension l E X m).mapHomologicalComplex (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P).as)) = 𝟙 _ := rfl
  have e6 : DerivedCategory.Qh.map
      (((scalarReductionRestriction l E X m).mapHomotopyCategoryFactors (.up ℤ)).inv.app
        (((scalarReductionExtension l E X m).mapHomologicalComplex (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P).as)) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  rw [e1, e2, e3, e4, e5, e6]
  simp only [Category.id_comp]
  repeat erw [Category.comp_id]
  rfl

private theorem sectionTransitionAdjoint
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    sfDerivedReductionTransition l E X n =
      adjointTransition
        (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
        (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
        (normalizedDVRRes.{u, u} l E X n.le_succ)
        (normalizedDVRResCompletedComp.{0, u, u} l E X D hl n.le_succ) := by
  apply (sfDerivedReductionTransition_existsUnique l E X n).unique
    (sfDerivedReductionTransition_existsUnique l E X n).exists.choose_spec
  intro P hP
  have h := normalizedDVR_kflat_transition.{0, u, u} l E X D hl P hP
    (DerivedCategory.Q.obj P) (Iso.refl _) n
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
    (normalizedDVRKFlatUnit.{0, u, u} l E X D hl (n + 1) P hP)
    (normalizedDVRKFlatUnit.{0, u, u} l E X D hl n P hP)
  have h' := normalizeRepresentativeTransition
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
    (normalizedDVRRes.{u, u} l E X n.le_succ)
    (normalizedDVRResCompletedComp.{0, u, u} l E X D hl n.le_succ)
    (DerivedCategory.Q.obj P) _ _
    (normalizedDVRKFlatComparison.{u, u} l E X (n + 1) P)
    (normalizedDVRKFlatComparison.{u, u} l E X n P)
    (DerivedCategory.Q.map (integralTowerTransition l E X D hl P n)) h
  have hf := congrArg (fun f ↦ DerivedCategory.Q.map f)
    (transition_eq l E X D hl P n)
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  · have key := h'.trans (congrArg
      (fun f ↦ normalizedDVRKFlatComparison.{u, u} l E X (n + 1) P ≫ f) hf)
    simpa only [normalizedDVRKFlatComparison_eq] using key

section RestrictionCompositor
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

/-- Ordinary restriction compositor coming from the limit projection equation. -/
private noncomputable def normalizedDVRTransitionRestriction
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    normalizedDVRModuleRes l E X n.le_succ ⋙
      scalarReductionRestriction.{u, u} l E X (n + 1) ≅
        scalarReductionRestriction.{u, u} l E X n := by
  let e₀ := normalizedDVRRestrictionCompIso
    (completedIntegralCoefficientProjection l E X D hl (n + 1))
    (normalizedDVRQuotient l E X n.le_succ)
  let he : completedIntegralCoefficientProjection l E X D hl (n + 1) ≫
      normalizedDVRQuotient l E X n.le_succ =
        completedIntegralCoefficientProjection l E X D hl n := by
    exact limit.w (integralCoefficientSheafSystem l E X) (homOfLE n.le_succ).op
  exact e₀ ≪≫ eqToIso (congrArg
    (fun f : completedIntegralCoefficientSheaf l E X D hl ⟶
        integralCoefficientSheaf l E X n ↦ SheafOfModules.restrictScalars.{u + 1} f) he)

/-- Localization of the ordinary compositor is the specified tower compositor. -/
private theorem normalizedDVRTransitionRestriction_comp
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    (Functor.mapDerivedCategoryCompIso
      (normalizedDVRModuleRes l E X n.le_succ)
      (scalarReductionRestriction.{u, u} l E X (n + 1))) ≪≫
        Functor.mapDerivedCategoryNatIso
          (normalizedDVRTransitionRestriction l E X D hl n) =
      normalizedDVRResCompletedComp l E X D hl n.le_succ := by
  unfold normalizedDVRResCompletedComp
  rfl
end RestrictionCompositor

end AlgebraicGeometry.ProEtale.IntegralPresentation

end IntegralReductionTransitionHelpers

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem scalarComp_eqToIso
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (hF : pbcRestrict ψ ⋙ pbcRestrict φ = pbcRestrict χ) :
    pbcRestrictComp φ ψ χ h = eqToIso hF := by
  subst χ
  change pbcRestrictComp φ ψ (φ ≫ ψ) rfl = Iso.refl _
  apply (pbcRestrictComp_exists φ ψ (φ ≫ ψ) rfl).unique
  · exact (pbcRestrictComp_exists φ ψ (φ ≫ ψ) rfl).exists.choose_spec
  · intro M U x
    rfl

private theorem eqIso_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F F' : A ⥤ B} (G : B ⥤ C) {H : A ⥤ C}
    (h : F = F') (h' : F' ⋙ G = H) (h'' : F ⋙ G = H) :
    eqToIso h'' = Functor.isoWhiskerRight (eqToIso h) G ≪≫ eqToIso h' := by
  subst F'
  subst H
  apply Iso.ext
  ext X
  simp

private theorem derivedComp_change
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {F F' : A ⥤ B} (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [F'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ F') (a : F ⋙ G ≅ H) (b : F' ⋙ G ≅ H)
    (h : a = Functor.isoWhiskerRight e G ≪≫ b) :
    (Functor.mapDerivedCategoryCompIso F G) ≪≫
        Functor.mapDerivedCategoryNatIso a =
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e) G.mapDerivedCategory ≪≫
        (Functor.mapDerivedCategoryCompIso F' G) ≪≫
          Functor.mapDerivedCategoryNatIso b := by
  apply Iso.ext
  rw [h]
  simp only [Iso.trans_hom, Functor.mapDerivedCategoryNatIso_trans]
  have hc := Functor.mapDerivedCategoryNatIso_isoWhiskerRight e G
  have hc' : (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e G)).hom =
      (Functor.mapDerivedCategoryCompIso F G).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom G.mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso F' G).hom := by
    rw [← reassoc_of% hc]
    simp only [Iso.inv_hom_id, Category.comp_id]
  rw [hc']
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.isoWhiskerRight_hom]

private theorem restrictedMate_change
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : A ⥤ C} {R' : C ⥤ A}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (S S' : C ⥤ B)
    (ρ : S ≅ S') (g : S ⋙ R ≅ R') (g' : S' ⋙ R ≅ R')
    (h : g = Functor.isoWhiskerRight ρ R ≪≫ g') (K : A) :
    R.map ((adj.homEquiv K _).symm
        (adj'.unit.app K ≫ g.inv.app (L'.obj K))) ≫ g.hom.app (L'.obj K) =
      R.map ((adj.homEquiv K _).symm
        (adj'.unit.app K ≫ g'.inv.app (L'.obj K))) ≫ g'.hom.app (L'.obj K) := by
  have hm : (adj.homEquiv K _).symm
        (adj'.unit.app K ≫ g.inv.app (L'.obj K)) ≫ ρ.hom.app (L'.obj K) =
      (adj.homEquiv K _).symm (adj'.unit.app K ≫ g'.inv.app (L'.obj K)) := by
    apply (adj.homEquiv K _).injective
    rw [Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    rw [h]
    simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
      Functor.whiskerRight_app, Category.assoc, ← R.map_comp,
      Iso.inv_hom_id_app, R.map_id]
    erw [Category.comp_id]
  rw [h] at hm ⊢
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, ← Category.assoc, ← R.map_comp, hm]

attribute [local irreducible] Functor.mapDerivedCategory HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence scalarReductionDerivedExtension

private theorem ordinaryCompletedComp_eq
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (p : R ⟶ S) (q : S ⟶ T) (r : R ⟶ T)
    (h : p ≫ q = r)
    (hF : SheafOfModules.restrictScalars.{u + 1} q ⋙
      SheafOfModules.restrictScalars.{u + 1} p = SheafOfModules.restrictScalars.{u + 1} r) :
    normalizedDVRRestrictionCompIso p q ≪≫
        eqToIso (congrArg (fun f ↦ SheafOfModules.restrictScalars.{u + 1} f) h) =
      eqToIso hF := by
  change Iso.refl _ ≪≫ eqToIso _ = _
  simp only [Iso.refl_trans]

section
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted
private theorem completedProjection_comp (W : Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    completedIntegralCoefficientProjection l E W D hl (n + 1) ≫
      normalizedDVRQuotient l E W n.le_succ =
        completedIntegralCoefficientProjection l E W D hl n := by
  exact limit.w (integralCoefficientSheafSystem l E W) (homOfLE n.le_succ).op
end

private theorem completedComp_change (W : Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
      (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
    letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
      (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
    normalizedDVRResCompletedComp l E W D hl n.le_succ =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso
          (eqToIso (compactSupportModuleRes_eq l E W n.le_succ)))
        (scalarReductionDerivedRestriction l E W (n + 1)) ≪≫
      compactSupportRestrictionComp l E W (n + 1) n n.le_succ := by
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
  let h := compactSupportModuleRes_eq l E W n.le_succ
  let h₀ := coefficientRestrictionComp l E W n.le_succ
  have h₁ : proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E (n + 1) n n.le_succ) ⋙
      scalarReductionRestriction l E W (n + 1) = scalarReductionRestriction l E W n :=
    (congrArg (fun F ↦ F ⋙ scalarReductionRestriction l E W (n + 1)) h).symm.trans h₀
  have he : pbcRestrictComp
      (completedIntegralCommRingProjectionUnrestricted l E W (n + 1))
      (compactSupportLevelSheafQuotient l E W (n + 1) n n.le_succ)
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (compactSupportProjection_comp l E W (n + 1) n n.le_succ) =
      eqToIso h₁ := by
    apply scalarComp_eqToIso
  have he₀ : normalizedDVRTransitionRestriction l E W D hl n = eqToIso h₀ := by
    exact ordinaryCompletedComp_eq
      (completedIntegralCoefficientProjection l E W D hl (n + 1))
      (normalizedDVRQuotient l E W n.le_succ)
      (completedIntegralCoefficientProjection l E W D hl n)
      (completedProjection_comp l E W D hl n) h₀
  rw [← normalizedDVRTransitionRestriction_comp]
  unfold compactSupportRestrictionComp pbcDerivedRestrictComp
  rw [he₀, he]
  exact derivedComp_change _ _ _ _ _ (eqIso_comp _ h h₁ h₀)

private theorem inputAdjacent (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (scalarReductionDerivedRestriction l E W (n + 1)).map
        (compactSupportReductionMap l E W (n + 1) n n.le_succ K) ≫
      (compactSupportRestrictionComp l E W (n + 1) n n.le_succ).hom.app
        ((scalarReductionDerivedExtension l E W n).obj K) =
      (sfDerivedReductionTransition l E W n).app K := by
  obtain ⟨D, hl⟩ := existsTestDatum l
  rw [sectionTransitionAdjoint l E W D hl n]
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
  exact (restrictedMate_change
    (derivedScalarExtensionRestrictionAdjunction l E W (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction l E W n).choose
    (normalizedDVRRes l E W n.le_succ) _
    (Functor.mapDerivedCategoryNatIso (eqToIso (compactSupportModuleRes_eq l E W n.le_succ)))
    (normalizedDVRResCompletedComp l E W D hl n.le_succ)
    (compactSupportRestrictionComp l E W (n + 1) n n.le_succ)
    (completedComp_change l E W D hl n) K).symm

private def inputNativeTower (W : Scheme.{u})
    (M : coefficientSequenceRestrictedDerived.{u, u} l E W) :
    ℕᵒᵖ ⥤ DerivedCategory (scalarReductionSource l E W) where
  obj n := (pbcTowerEvaluation W
    (completedIntegralCommRingSheafUnrestricted l E W) n.unop).obj M
  map {m n} f := (pbcTowerTransition W
    (completedIntegralCommRingSheafUnrestricted l E W) m.unop n.unop
      (leOfHom f.unop)).app M
  map_id n := by
    have h : pbcTowerTransition W
        (completedIntegralCommRingSheafUnrestricted l E W) n.unop n.unop le_rfl = 𝟙 _ := by
      unfold pbcTowerTransition
      simp only [homOfLE_refl, op_id]
      erw [CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id,
        Functor.whiskerRight_id, Localization.liftNatTrans_id]
    exact NatTrans.congr_app h M
  map_comp {r m n} f g := by
    have h : pbcTowerTransition W
        (completedIntegralCommRingSheafUnrestricted l E W) r.unop n.unop
          ((leOfHom g.unop).trans (leOfHom f.unop)) =
      pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W)
        r.unop m.unop (leOfHom f.unop) ≫
      pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W)
        m.unop n.unop (leOfHom g.unop) := by
      unfold pbcTowerTransition
      rw [Localization.comp_liftNatTrans]
      congr 1
      rw [← Functor.whiskerRight_comp, ← NatTrans.mapHomologicalComplex_comp,
        ← Functor.map_comp]
      rfl
    exact NatTrans.congr_app h M

/-- Restricting the direct quotient reduction to completed coefficients gives the
specified integral reduction tower, including its actual arrows.
Source: blueprint lemma-change-coefficients-compact-support, proof paragraphs 1--2; Stacks
Tags 06YY and 07A6 (blueprint: lem-coef-compact-support-input-tower-compatibility).

Proof: take the native derived coefficient system obtained by reducing K on the
ringed sequence site. Its finite evaluations identify with the derived reductions of
K. Its transitions and compactSupportReductionMap are adjuncts of the same smaller
reduction unit, under the scalar adjunction; injectivity of its Hom bijection identifies
them after quotient transport. Restrict this system to completed coefficients using
the evaluation-transition compatibility of the coefficient sequence calculus.
The ordinary restriction compositor
for the sequence quotient equals the direct quotient compositor: both act as the
identity on every underlying section. This equality passes to exact derived functors.
For adjacent levels, apply the scalar-extension/restriction Hom bijection. Both the
restricted quotient map and sfDerivedReductionTransition are adjuncts of the smaller
reduction unit followed by the inverse completed restriction compositor; their equality
is the normalized K-flat transition comparison (sectionTransitionAdjoint).
For equal indices, the native coefficient transition and the tower map are identities.
Induct on m-n: the native transitions compose by their cocycle, and the tower maps
compose by functoriality. The adjacent equality therefore identifies every map.
No boundedness, constructibility, or finite-type hypothesis is used. -/
theorem compactSupportInput_completed_tower (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) :
    ∀ (m n : ℕ) (h : n ≤ m),
      (scalarReductionDerivedRestriction l E W m).map
          (compactSupportReductionMap l E W m n h K) ≫
        (compactSupportRestrictionComp l E W m n h).hom.app
          ((scalarReductionDerivedExtension l E W n).obj K) =
        (sfIntegralReductionTower l E W K).map (homOfLE h).op := by
  classical
  obtain ⟨S, _hS⟩ := coefficientDerivedSystemEvaluationCalculus.{u, u} l E W
  let N := S.reduction.obj K
  let U := (coefficientSequenceDerivedRestriction l E W).obj N
  let T := inputNativeTower l E W U
  let e (n : ℕ) : T.obj (op n) ≅
      (sfDerivedReductionRestricted l E W n).obj K :=
    (coefficientRestrictedEvaluationIso l E W n).app N ≪≫
      (scalarReductionDerivedRestriction l E W n).mapIso ((S.reductionEvaluation n).app K)
  have he (m n : ℕ) (h : n ≤ m) :
      T.map (homOfLE h).op ≫ (e n).hom =
        (e m).hom ≫ (scalarReductionDerivedRestriction l E W m).map
          (compactSupportReductionMap l E W m n h K) ≫
        (compactSupportRestrictionComp l E W m n h).hom.app
          ((scalarReductionDerivedExtension l E W n).obj K) := by
    have ht := compactSupportCoefficientTransition_restricted l E W h N
    have hd := compactSupportReductionTransition l E W S.toCoefficientDerivedSystemReduction h K
    have hn := (compactSupportRestrictionComp l E W m n h).hom.naturality
      ((S.reductionEvaluation n).hom.app K)
    dsimp only [Functor.comp_map] at hn
    dsimp only [e, T, U, inputNativeTower, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom]
    rw [reassoc_of% ht]
    dsimp only [N, Functor.comp_obj] at hn ⊢
    erw [← hn]
    rw [← Functor.map_comp_assoc, hd, Functor.map_comp]
    simp only [Category.assoc]
    rfl
  let α : T ⟶ sfIntegralReductionTower l E W K := NatTrans.ofOpSequence
    (fun n ↦ (e n).hom) (by
      intro n
      rw [he, inputAdjacent]
      simp only [sfIntegralReductionTower, Functor.ofOpSequence_map_homOfLE_succ])
  intro m n h
  apply (cancel_epi (e m).hom).mp
  exact (he m n h).symm.trans (α.naturality (homOfLE h).op)

end WeilConjectures
