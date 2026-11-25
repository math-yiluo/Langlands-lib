/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import WeilConjectures.SixFunctors.SheafRestrictionTowerData.StrictRestrictionTower
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Coherence of completed scalar restriction

Source: the canonical restriction comparisons in def-coef-normalized-dvr-tower,
and Stacks, Derived Categories, lemma-right-derived-exact-functor;
Categories, lemma-properties-left-localization.
(blueprint: lem-coef-normalized-dvr-completed-restriction-coherence).
-/

@[expose] public section
set_option autoImplicit false
universe u t d
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

private theorem restrictionUnit
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (f : R ⟶ S) (q : S ⟶ S) (hq : q = 𝟙 S)
    (hf : f ≫ q = f) :
    normalizedDVRRestrictionComp.{_, _, _, u} f q f hf =
      Functor.isoWhiskerRight
        (eqToIso (congrArg (fun a ↦ SheafOfModules.restrictScalars.{u} a) hq))
        (SheafOfModules.restrictScalars.{u} f) := by
  subst q
  rfl

private theorem restrictionAssoc
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R₀ R₁ R₂ R₃ : Sheaf J RingCat.{u}}
    (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂) (h : R₂ ⟶ R₃)
    (fg : R₀ ⟶ R₂) (gh : R₁ ⟶ R₃) (fgh : R₀ ⟶ R₃)
    (e₁ : f ≫ g = fg) (e₂ : g ≫ h = gh)
    (e₃ : f ≫ gh = fgh) (e₄ : fg ≫ h = fgh)
    (M : SheafOfModules.{u} R₃) :
    (SheafOfModules.restrictScalars f).map
        ((normalizedDVRRestrictionComp g h gh e₂).hom.app M) ≫
      (normalizedDVRRestrictionComp f gh fgh e₃).hom.app M =
    (normalizedDVRRestrictionComp f g fg e₁).hom.app
        ((SheafOfModules.restrictScalars h).obj M) ≫
      (normalizedDVRRestrictionComp fg h fgh e₄).hom.app M := by
  cases e₁
  cases e₂
  cases e₃
  rfl

private theorem derivedUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (S : A ⥤ A) (G : A ⥤ B) [S.Additive] [G.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : S ≅ 𝟭 A) (P : DerivedCategory A) :
    (Functor.mapDerivedCategoryCompNatIso (Functor.isoWhiskerRight a G)).hom.app P =
      G.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryIdIso A).hom.app P) := by
  have hw := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight a G) P
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp G) P
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hw hu
  dsimp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [CategoryTheory.Functor.map_comp]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso S G).inv.app P)).mp
  rw [Iso.inv_hom_id_app_assoc, ← Category.assoc, ← hw, Category.assoc, hu]
  exact (Category.comp_id _).symm

section

variable {A₁ A₂ A₃ A₄ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category A₄]
  [Abelian A₁] [Abelian A₂] [Abelian A₃] [Abelian A₄]
  [HasDerivedCategory A₁] [HasDerivedCategory A₂] [HasDerivedCategory A₃] [HasDerivedCategory A₄]
  {F₁₂ : A₁ ⥤ A₂} {F₂₃ : A₂ ⥤ A₃} {F₃₄ : A₃ ⥤ A₄} {F₁₃ : A₁ ⥤ A₃} {F₂₄ : A₂ ⥤ A₄}
  {F₁₄ : A₁ ⥤ A₄} [F₁₂.Additive] [F₂₃.Additive] [F₃₄.Additive] [F₁₃.Additive] [F₂₄.Additive]
  [F₁₄.Additive] [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₂₃] [PreservesFiniteColimits F₂₃]
  [PreservesFiniteLimits F₃₄] [PreservesFiniteColimits F₃₄]
  [PreservesFiniteLimits F₁₃] [PreservesFiniteColimits F₁₃]
  [PreservesFiniteLimits F₂₄] [PreservesFiniteColimits F₂₄]
  [PreservesFiniteLimits F₁₄] [PreservesFiniteColimits F₁₄]

private theorem derivedCocycleInv (γ₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃)
    (γ₁₃₄ : F₁₃ ⋙ F₃₄ ≅ F₁₄) (γ₂₃₄ : F₂₃ ⋙ F₃₄ ≅ F₂₄) (γ₁₂₄ : F₁₂ ⋙ F₂₄ ≅ F₁₄)
    (h : ∀ X, F₃₄.map (γ₁₂₃.hom.app X) ≫ γ₁₃₄.hom.app X =
      γ₂₃₄.hom.app (F₁₂.obj X) ≫ γ₁₂₄.hom.app X) (K : DerivedCategory A₁) :
    F₃₄.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompNatIso γ₁₂₃).inv.app K) ≫
      (Functor.mapDerivedCategoryCompNatIso γ₂₃₄).hom.app (F₁₂.mapDerivedCategory.obj K) ≫
      (Functor.mapDerivedCategoryCompNatIso γ₁₂₄).hom.app K =
    (Functor.mapDerivedCategoryCompNatIso γ₁₃₄).hom.app K := by
  rw [← Functor.mapDerivedCategoryCompNatIso_cocycle γ₁₂₃ γ₁₃₄ γ₂₃₄ γ₁₂₄ h K,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end

private noncomputable instance completedLimits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℕ) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{max u (t + 1)}
      (completedIntegralCoefficientProjection l E X D hl n)) :=
  (completedIntegralRestrictScalars_exact l E X D hl n).1

private noncomputable instance completedColimits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℕ) :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{max u (t + 1)}
      (completedIntegralCoefficientProjection l E X D hl n)) :=
  (completedIntegralRestrictScalars_exact l E X D hl n).2

/-- The unit and associativity equations for the canonical completed restriction
comparisons. These are equations of the specified comparisons, not merely the
existence of some coherent comparison isomorphisms.

Source: def-coef-normalized-dvr-tower and the strict representative step in
lem-coef-integral-dualizing-roos-model; Stacks, Derived Categories,
lemma-right-derived-exact-functor; Categories, lemma-properties-left-localization.
(blueprint: lem-coef-normalized-dvr-completed-restriction-coherence).

Proof: for ordinary module sheaves every restriction comparison has the identity
as its underlying map on every section. The unit and the threefold composition
squares therefore commute sectionwise. Apply exact restriction to complexes and
then localize. The canonical composition comparison of mapDerivedCategory is
characterized by its factorization through Q. Whisker each proposed derived
identity with Q, replace every comparison by this factorization, and cancel the
invertible factorization maps. The remaining unit square, respectively the
threefold composition square, is precisely the identity-on-sections square just
checked. Faithfulness of precomposition with the localization proves both
identities on every derived object. Repeated indices cause no exception: their
quotient maps are identities, so this also proves all degenerate associativity
cases. The zero sheaf on an empty scheme satisfies the same equalities. -/
theorem normalizedDVR_completedRestriction_coherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    (∀ (n : ℕ) (P : normalizedDVRDerived l E X n),
      (normalizedDVRResCompletedComp l E X D hl (Nat.le_refl n)).hom.app P =
        (normalizedDVRResCompleted l E X D hl n).map
          ((normalizedDVRResUnit l E X n).hom.app P)) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m)
      (P : normalizedDVRDerived l E X n),
      (normalizedDVRResCompleted l E X D hl r).map
          ((normalizedDVRResComp l E X hrm hmn).inv.app P) ≫
        (normalizedDVRResCompletedComp l E X D hl hrm).hom.app
          ((normalizedDVRRes l E X hmn).obj P) ≫
        (normalizedDVRResCompletedComp l E X D hl hmn).hom.app P =
      (normalizedDVRResCompletedComp l E X D hl (hmn.trans hrm)).hom.app P) := by
  let := HasDerivedCategory.standard (completedIntegralModuleSheaves l E X D hl)
  let (n : ℕ) := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  let γ {m n : ℕ} (h : n ≤ m) := normalizedDVRRestrictionComp.{_, _, _, max u (t + 1)}
    (completedIntegralCoefficientProjection l E X D hl m) (normalizedDVRQuotient l E X h)
    (completedIntegralCoefficientProjection l E X D hl n)
    (limit.w (integralCoefficientSheafSystem l E X) (homOfLE h).op)
  let β {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :=
    normalizedDVRRestrictionComp.{_, _, _, max u (t + 1)}
      (normalizedDVRQuotient l E X hrm) (normalizedDVRQuotient l E X hmn)
      (normalizedDVRQuotient l E X (hmn.trans hrm))
      ((integralCoefficientSheafSystem l E X).map_comp
        (homOfLE hrm).op (homOfLE hmn).op).symm
  constructor
  · intro n P
    have he := restrictionUnit
      (completedIntegralCoefficientProjection l E X D hl n)
      (normalizedDVRQuotient l E X (Nat.le_refl n))
      ((integralCoefficientSheafSystem l E X).map_id (op n))
      (limit.w (integralCoefficientSheafSystem l E X) (𝟙 (op n)))
    change (Functor.mapDerivedCategoryCompNatIso (γ (Nat.le_refl n))).hom.app P = _
    dsimp only [γ] at he ⊢
    rw [he]
    exact derivedUnit _ _ _ P
  · intro r m n hrm hmn P
    exact derivedCocycleInv
      (β hrm hmn) (γ (hmn.trans hrm)) (γ hrm) (γ hmn)
      (restrictionAssoc
        (completedIntegralCoefficientProjection l E X D hl r)
        (normalizedDVRQuotient l E X hrm) (normalizedDVRQuotient l E X hmn)
        (completedIntegralCoefficientProjection l E X D hl m)
        (normalizedDVRQuotient l E X (hmn.trans hrm))
        (completedIntegralCoefficientProjection l E X D hl n)
        (limit.w _ (homOfLE hrm).op)
        ((integralCoefficientSheafSystem l E X).map_comp
          (homOfLE hrm).op (homOfLE hmn).op).symm
        (limit.w _ (homOfLE (hmn.trans hrm)).op)
        (limit.w _ (homOfLE hmn).op)) P

end WeilConjectures
