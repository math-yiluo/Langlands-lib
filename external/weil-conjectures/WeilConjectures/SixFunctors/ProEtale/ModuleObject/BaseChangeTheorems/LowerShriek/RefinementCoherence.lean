/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.OverRefinementEqualizer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeFormalism

/-!

# Coherence of the comparisons of the lower shriek along refinements

For bounded constructible `ℚ̄_ℓ`-sheaves, this file proves the coherence clauses of blueprint
`proposition-construction-independence-rf-shriek` for the comparisons
`boundedConstructibleLowerShriekRefinementIso'` along refinements and
`boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl` between compactifications:

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekRefinementIso'_trans_eq`: the
  comparisons along refinements compose, by the composition law
  `ExchangeFormalism.refinementComparison_comp` of the exchange formalism;
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekOverRefinementIso_eq`: the comparison
  along a refinement `c → c₁` of compactifications does not depend on the refinement. Two
  refinements `r r' : c → c₁` are equalized by the refinement of `c` by their equalizer
  (`Compactification.OverRefinement.eqLocusRefinement`), and the comparison along that
  refinement is an isomorphism, which can be cancelled;
- `boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_trans_symm`:
  the comparison of two compactifications may be computed through any common refinement;
- `boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans_eq`
  (the cocycle condition) and
  `boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_refinementIso`
  (the comparison with a refinement is the comparison along the refinement).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

section Transitivity

variable {X Z Z₁ Z₂ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Z₂.hom] [QuasiCompact Z₂.hom] [IsSeparated Z₂.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The comparison `boundedConstructibleLowerShriekRefinementIso'` along a refinement only
depends on the refinement morphism. -/
lemma boundedConstructibleLowerShriekRefinementIso'_congr {i : X ⟶ Z} {i₁ : X ⟶ Z₁}
    [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] {h h' : Z ⟶ Z₁}
    (sq : IsPullback (𝟙 X) i i₁ h) (sq' : IsPullback (𝟙 X) i i₁ h') {p : Z ⟶ Y} {p₁ : Z₁ ⟶ Y}
    (wp : h ≫ p₁ = p) (wp' : h' ≫ p₁ = p)
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq)]
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq')]
    (hh : h = h') :
    boundedConstructibleLowerShriekRefinementIso' ℓ sq wp =
      boundedConstructibleLowerShriekRefinementIso' ℓ sq' wp' := by
  subst hh
  rfl

/-- **Transitivity of the comparisons along refinements**: for refinements `h : Z ⟶ Z₁` and
`h₁ : Z₁ ⟶ Z₂`, the comparison along `h ≫ h₁` is the composite of the comparisons. -/
theorem boundedConstructibleLowerShriekRefinementIso'_trans_eq {i : X ⟶ Z} {i₁ : X ⟶ Z₁}
    {i₂ : X ⟶ Z₂} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] [IsOpenImmersion i₂.left]
    {h : Z ⟶ Z₁} {h₁ : Z₁ ⟶ Z₂} {h₂ : Z ⟶ Z₂} (sq : IsPullback (𝟙 X) i i₁ h)
    (sq₁ : IsPullback (𝟙 X) i₁ i₂ h₁) (sq₂ : IsPullback (𝟙 X) i i₂ h₂) (hh : h ≫ h₁ = h₂)
    {p : Z ⟶ Y} {p₁ : Z₁ ⟶ Y} {p₂ : Z₂ ⟶ Y} (wp : h ≫ p₁ = p) (wp₁ : h₁ ≫ p₂ = p₁)
    (wp₂ : h₂ ≫ p₂ = p)
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq)]
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq₁)]
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq₂)] :
    boundedConstructibleLowerShriekRefinementIso' ℓ sq₁ wp₁ ≪≫
        boundedConstructibleLowerShriekRefinementIso' ℓ sq wp =
      boundedConstructibleLowerShriekRefinementIso' ℓ sq₂ wp₂ := by
  have := isIso_baseChange_boundedConstructibleExchangeFormalism_id ℓ sq
  have := isIso_baseChange_boundedConstructibleExchangeFormalism_id ℓ sq₁
  have := isIso_baseChange_boundedConstructibleExchangeFormalism_id ℓ sq₂
  ext1
  rw [Iso.trans_hom, boundedConstructibleLowerShriekRefinementIso'_hom_eq,
    boundedConstructibleLowerShriekRefinementIso'_hom_eq,
    boundedConstructibleLowerShriekRefinementIso'_hom_eq]
  exact ((𝔽).refinementComparison_comp (r := SepFinType.homMk h) (s := SepFinType.homMk h₁)
    (rs := SepFinType.homMk h₂) _ _ _ _ _ _ (ObjectProperty.hom_ext _ hh) _ _ _ _ _ _).symm

end Transitivity

section Compactification

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The comparison `Rf_!^{c₁} ≅ Rf_!^c` along a refinement `r : c → c₁` of compactifications
(`boundedConstructibleLowerShriekRefinementIso'` along `r.hom`). -/
noncomputable def boundedConstructibleLowerShriekOverRefinementIso {c c₁ : Compactification f.left}
    (r : Compactification.OverRefinement c c₁) :
    boundedConstructibleLowerShriekOfCompactification ℓ c₁ ≅
      boundedConstructibleLowerShriekOfCompactification ℓ c :=
  haveI := r.isProper
  haveI := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    r.isPullback
  boundedConstructibleLowerShriekRefinementIso' ℓ r.isPullback r.hom_overG

/-- The comparison along a composite of refinements is the composite of the comparisons. -/
lemma boundedConstructibleLowerShriekOverRefinementIso_trans
    {c c₁ c₂ : Compactification f.left} (r : Compactification.OverRefinement c c₁)
    (s : Compactification.OverRefinement c₁ c₂) :
    boundedConstructibleLowerShriekOverRefinementIso ℓ s ≪≫
        boundedConstructibleLowerShriekOverRefinementIso ℓ r =
      boundedConstructibleLowerShriekOverRefinementIso ℓ (r.trans s) := by
  have := r.isProper
  have := s.isProper
  have := (r.trans s).isProper
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    r.isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    s.isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (r.trans s).isPullback
  exact boundedConstructibleLowerShriekRefinementIso'_trans_eq ℓ r.isPullback s.isPullback
    (r.trans s).isPullback rfl r.hom_overG s.hom_overG (r.trans s).hom_overG

/-- **Independence of the refinement**: the comparisons along two refinements `r r' : c → c₁`
agree. Both become equal after composing with the comparison along the refinement of `c` by the
equalizer of `r.hom` and `r'.hom`, which is an isomorphism. -/
theorem boundedConstructibleLowerShriekOverRefinementIso_eq {c c₁ : Compactification f.left}
    (r r' : Compactification.OverRefinement c c₁) :
    boundedConstructibleLowerShriekOverRefinementIso ℓ r =
      boundedConstructibleLowerShriekOverRefinementIso ℓ r' := by
  let t := r.eqLocusRefinement r'
  have h₁ := boundedConstructibleLowerShriekOverRefinementIso_trans ℓ t r
  have h₂ := boundedConstructibleLowerShriekOverRefinementIso_trans ℓ t r'
  have h₃ : boundedConstructibleLowerShriekOverRefinementIso ℓ (t.trans r) =
      boundedConstructibleLowerShriekOverRefinementIso ℓ (t.trans r') := by
    have := (t.trans r).isProper
    have := (t.trans r').isProper
    have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
      (t.trans r).isPullback
    have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
      (t.trans r').isPullback
    exact boundedConstructibleLowerShriekRefinementIso'_congr ℓ _ _ _ _
      (r.eqLocusRefinement_hom_comp r')
  ext1
  rw [← cancel_mono (boundedConstructibleLowerShriekOverRefinementIso ℓ t).hom]
  exact congrArg Iso.hom (h₁.trans (h₃.trans h₂.symm))

/-- The comparison along the identity refinement is the identity. -/
lemma boundedConstructibleLowerShriekOverRefinementIso_refl (c : Compactification f.left) :
    boundedConstructibleLowerShriekOverRefinementIso ℓ
        (Compactification.OverRefinement.refl c) = Iso.refl _ := by
  ext1
  rw [← cancel_epi (boundedConstructibleLowerShriekOverRefinementIso ℓ
    (Compactification.OverRefinement.refl c)).hom, Iso.refl_hom, Category.comp_id]
  exact congrArg Iso.hom ((boundedConstructibleLowerShriekOverRefinementIso_trans ℓ _ _).trans
    (boundedConstructibleLowerShriekOverRefinementIso_eq ℓ _ _))

/-- Unfolding `boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl` in terms of
`boundedConstructibleLowerShriekOverRefinementIso`: the comparison through the chosen common
refinement. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_overRefinementIso
    (c₁ c₂ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₂ =
      boundedConstructibleLowerShriekOverRefinementIso ℓ
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some ≪≫
        (boundedConstructibleLowerShriekOverRefinementIso ℓ
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some).symm :=
  boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_refinementIso' ℓ c₁ c₂

/-- For refinements `r : d → c` and `r' : d' → c`, the comparisons along `r` and `r'` agree
after composing with the comparisons along refinements `t : e → d` and `t' : e → d'`. -/
lemma boundedConstructibleLowerShriekOverRefinementIso_trans_eq_trans
    {c d d' e : Compactification f.left} (r : Compactification.OverRefinement d c)
    (r' : Compactification.OverRefinement d' c) (t : Compactification.OverRefinement e d)
    (t' : Compactification.OverRefinement e d') :
    boundedConstructibleLowerShriekOverRefinementIso ℓ r ≪≫
        boundedConstructibleLowerShriekOverRefinementIso ℓ t =
      boundedConstructibleLowerShriekOverRefinementIso ℓ r' ≪≫
        boundedConstructibleLowerShriekOverRefinementIso ℓ t' :=
  (boundedConstructibleLowerShriekOverRefinementIso_trans ℓ t r).trans
    ((boundedConstructibleLowerShriekOverRefinementIso_eq ℓ _ _).trans
      (boundedConstructibleLowerShriekOverRefinementIso_trans ℓ t' r').symm)

/-- The comparison `Rf_!^{c₁} ≅ Rf_!^{c₂}` may be computed through any common refinement
`r₁ : d → c₁`, `r₂ : d → c₂`. -/
theorem boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_trans_symm
    {c₁ c₂ d : Compactification f.left} (r₁ : Compactification.OverRefinement d c₁)
    (r₂ : Compactification.OverRefinement d c₂) :
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₂ =
      boundedConstructibleLowerShriekOverRefinementIso ℓ r₁ ≪≫
        (boundedConstructibleLowerShriekOverRefinementIso ℓ r₂).symm := by
  rw [boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_overRefinementIso]
  obtain ⟨e, ⟨t⟩, ⟨t₀⟩⟩ := Compactification.exists_overRefinement d
    (Compactification.exists_overRefinement c₁ c₂).choose
  calc _ = (boundedConstructibleLowerShriekOverRefinementIso ℓ
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some ≪≫
          boundedConstructibleLowerShriekOverRefinementIso ℓ t₀) ≪≫
        (boundedConstructibleLowerShriekOverRefinementIso ℓ
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some ≪≫
          boundedConstructibleLowerShriekOverRefinementIso ℓ t₀).symm := by simp
    _ = (boundedConstructibleLowerShriekOverRefinementIso ℓ r₁ ≪≫
          boundedConstructibleLowerShriekOverRefinementIso ℓ t) ≪≫
        (boundedConstructibleLowerShriekOverRefinementIso ℓ r₂ ≪≫
          boundedConstructibleLowerShriekOverRefinementIso ℓ t).symm := by
      rw [boundedConstructibleLowerShriekOverRefinementIso_trans_eq_trans ℓ _ r₁ t₀ t,
        boundedConstructibleLowerShriekOverRefinementIso_trans_eq_trans ℓ _ r₂ t₀ t]
    _ = _ := by simp

/-- **The cocycle condition** for the comparisons of the lower shrieks attached to three
compactifications. -/
theorem boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans_eq
    (c₁ c₂ c₃ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₂ ≪≫
        boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₂ c₃ =
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₃ := by
  obtain ⟨d, ⟨r₁⟩, ⟨r₂⟩⟩ := Compactification.exists_overRefinement c₁ c₂
  obtain ⟨e, ⟨t⟩, ⟨t₃⟩⟩ := Compactification.exists_overRefinement d c₃
  rw [boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_trans_symm ℓ
      (t.trans r₁) (t.trans r₂),
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_trans_symm ℓ
      (t.trans r₂) t₃,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_trans_symm ℓ
      (t.trans r₁) t₃]
  simp

/-- The comparison of a compactification `c₁` with a refinement `c` of `c₁` is the comparison
along the refinement. -/
theorem boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_refinementIso
    {c c₁ : Compactification f.left} (r : Compactification.OverRefinement c c₁) :
    haveI := r.isProper
    haveI := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
      r.isPullback
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c =
      boundedConstructibleLowerShriekRefinementIso' ℓ r.isPullback r.hom_overG := by
  rw [boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_trans_symm ℓ r
      (Compactification.OverRefinement.refl c),
    boundedConstructibleLowerShriekOverRefinementIso_refl, Iso.refl_symm, Iso.trans_refl]
  rfl

end Compactification

end AlgebraicGeometry.ProEtale.CondensedRing
