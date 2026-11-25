/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.CompactSupportProperImageTower.CompactSupportProperImageTower
import WeilConjectures.SmoothPurity.Sf.SfDirectImageInputTransitionAdjacent

/-! # The normalized adjacent input transition -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (p : X ⟶ Y)

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
    Functor.mapDerivedCategoryCompIso F G ≪≫
        Functor.mapDerivedCategoryNatIso a =
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e) G.mapDerivedCategory ≪≫
        Functor.mapDerivedCategoryCompIso F' G ≪≫
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

private theorem adjacentRestriction_eq (n : ℕ) :
    normalizedDVRModuleRes l E X (Nat.le_succ n) =
      proEtaleCoefficientRestrictScalars X
        (compactSupportLevelQuotient l E (n + 1) n (Nat.le_succ n)) := by
  unfold normalizedDVRModuleRes normalizedDVRQuotient integralCoefficientSheafSystem
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

private theorem quotientRestrictionLimits (n : ℕ) : PreservesFiniteLimits
    (proEtaleCoefficientRestrictScalars X
      (compactSupportLevelQuotient l E (n + 1) n (Nat.le_succ n))) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteLimits X _

private theorem quotientRestrictionColimits (n : ℕ) : PreservesFiniteColimits
    (proEtaleCoefficientRestrictScalars X
      (compactSupportLevelQuotient l E (n + 1) n (Nat.le_succ n))) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteColimits X _

private theorem adjacentRestrictionComp (n : ℕ) :
    letI := quotientRestrictionLimits l E (X := X) n
    letI := quotientRestrictionColimits l E (X := X) n
    compactSupportSystemRestrictionComp l E X (Nat.le_succ n) =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso (eqToIso (adjacentRestriction_eq l E (X := X) n)))
        (scalarReductionDerivedRestriction l E X (n + 1)) ≪≫
      compactSupportRestrictionComp l E X (n + 1) n (Nat.le_succ n) := by
  let := quotientRestrictionLimits l E (X := X) n
  let := quotientRestrictionColimits l E (X := X) n
  let h := adjacentRestriction_eq l E (X := X) n
  let h₀ := coefficientRestrictionComp l E X (Nat.le_succ n)
  have h₁ : proEtaleCoefficientRestrictScalars X
      (compactSupportLevelQuotient l E (n + 1) n (Nat.le_succ n)) ⋙
      scalarReductionRestriction l E X (n + 1) = scalarReductionRestriction l E X n :=
    (congrArg (fun F ↦ F ⋙ scalarReductionRestriction l E X (n + 1)) h).symm.trans h₀
  have he : pbcRestrictComp
      (completedIntegralCommRingProjectionUnrestricted l E X (n + 1))
      (compactSupportLevelSheafQuotient l E X (n + 1) n (Nat.le_succ n))
      (completedIntegralCommRingProjectionUnrestricted l E X n)
      (compactSupportProjection_comp l E X (n + 1) n (Nat.le_succ n)) =
      eqToIso h₁ := by
    apply scalarComp_eqToIso
  unfold compactSupportSystemRestrictionComp compactSupportRestrictionComp pbcDerivedRestrictComp
  rw [he]
  exact derivedComp_change _ _ _ _ _ (eqIso_comp _ h h₁ h₀)

/-- The normalized finite quotient has the canonical completed coefficient transition.
Source: Stacks Tags 06YY and 07A6; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-sf-normalized-input-transition).
Proof: choose a K-flat model of K. The finite scalar-extension adjunction is normalized
by the tensor unit. Its transpose defining reductionMap is therefore id tensor the
quotient, whose completed restriction is the canonical quotient transition. The
normalized restriction compositor is the identity on sections. The same computation
identifies the quotient-based compact-support transition with the canonical transition
by sfDirectImageInputTransition_adjacent. Localization through the K-flat models and
naturality give the identity for K, including the zero object. -/
theorem sfNormalizedInputTransition
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (coefficientFiniteDerivedRestriction l E X (n + 1)).map
          (CompactSupportProperImageTower.reductionMap l E X K n) ≫
        (compactSupportSystemRestrictionComp l E X (Nat.le_succ n)).hom.app
          ((coefficientFiniteDerivedExtension l E X n).obj K) =
      (sfDerivedReductionTransition l E X n).app K := by
  let := quotientRestrictionLimits l E (X := X) n
  let := quotientRestrictionColimits l E (X := X) n
  have h := restrictedMate_change (coefficientFiniteAdjunction l E X (n + 1))
    (coefficientFiniteAdjunction l E X n)
    (normalizedDVRRes l E X (Nat.le_succ n))
    (proEtaleCoefficientRestrictScalars X
      (compactSupportLevelQuotient l E (n + 1) n (Nat.le_succ n))).mapDerivedCategory
    (Functor.mapDerivedCategoryNatIso (eqToIso (adjacentRestriction_eq l E (X := X) n)))
    (compactSupportSystemRestrictionComp l E X (Nat.le_succ n))
    (compactSupportRestrictionComp l E X (n + 1) n (Nat.le_succ n))
    (adjacentRestrictionComp l E (X := X) n) K
  exact h.trans (sfDirectImageInputTransition_adjacent l E K n)

end WeilConjectures
