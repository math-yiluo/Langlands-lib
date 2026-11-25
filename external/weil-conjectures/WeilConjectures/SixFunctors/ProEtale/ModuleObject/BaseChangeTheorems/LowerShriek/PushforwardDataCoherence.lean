/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.OverRefinementBaseChange
public import WeilConjectures.Compactification.OverRefinementEqualizer
public import WeilConjectures.Mathlib.CategoryTheory.Iso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardDataExchangeFormalism

/-!
# Coherence of the compact-support base change of a pushforward datum

Let `P` be a pushforward datum for a coefficient ring `Λ`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData`) whose comparisons along proper
refinements are isomorphisms (`hP : P.IsIsoRefinementPushforward`). This file proves, for the
constructions of `P`, the coherence results proved for the coefficient ring `ℚ̲̄_ℓ` in the files
`RefinementCoherence` and `BaseChangeIndependence` of this directory, by the same formal
arguments in the exchange formalism of `P`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData.exchangeFormalism`):

* the comparisons `P.lowerShriekRefinementIso` along refinements compose, and the comparison
  along a refinement of compactifications does not depend on the refinement;
* the independence isomorphisms `lowerShriekOfCompactificationIso hP c₁ c₂` may be computed
  through any common refinement, are the identity for `c₁ = c₂` and satisfy the cocycle
  condition;
* the compact-support base change `lowerShriekBaseChange hP sq` may be computed through any
  compactification `c` of `f` and any compactification `c'` of `f'` lying over `c`
  (`BoundedConstructiblePushforwardData.lowerShriekBaseChange_eq_baseChange`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace BoundedConstructiblePushforwardData

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (P : BoundedConstructiblePushforwardData Λ ℓ k)

/-- The exchange formalism of the pushforward datum `P`. -/
local notation "𝔽" => exchangeFormalism P

section Transitivity

variable {X Z Z₁ Z₂ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Z₂.hom] [QuasiCompact Z₂.hom] [IsSeparated Z₂.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The comparison `P.lowerShriekRefinementIso` along a refinement only depends on the
refinement morphism. -/
lemma lowerShriekRefinementIso_congr {i : X ⟶ Z} {i₁ : X ⟶ Z₁} [IsOpenImmersion i.left]
    [IsOpenImmersion i₁.left] {h h' : Z ⟶ Z₁} (sq : IsPullback (𝟙 X) i i₁ h)
    (sq' : IsPullback (𝟙 X) i i₁ h') {p : Z ⟶ Y} {p₁ : Z₁ ⟶ Y} (wp : h ≫ p₁ = p)
    (wp' : h' ≫ p₁ = p) [IsIso (P.openImmersionLowerShriekRefinementPushforward sq)]
    [IsIso (P.openImmersionLowerShriekRefinementPushforward sq')] (hh : h = h') :
    P.lowerShriekRefinementIso sq wp = P.lowerShriekRefinementIso sq' wp' := by
  subst hh
  rfl

/-- **Transitivity of the comparisons along refinements**: for refinements `h : Z ⟶ Z₁` and
`h₁ : Z₁ ⟶ Z₂`, the comparison along `h ≫ h₁` is the composite of the comparisons. -/
theorem lowerShriekRefinementIso_trans_eq {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {i₂ : X ⟶ Z₂}
    [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] [IsOpenImmersion i₂.left]
    {h : Z ⟶ Z₁} {h₁ : Z₁ ⟶ Z₂} {h₂ : Z ⟶ Z₂} (sq : IsPullback (𝟙 X) i i₁ h)
    (sq₁ : IsPullback (𝟙 X) i₁ i₂ h₁) (sq₂ : IsPullback (𝟙 X) i i₂ h₂) (hh : h ≫ h₁ = h₂)
    {p : Z ⟶ Y} {p₁ : Z₁ ⟶ Y} {p₂ : Z₂ ⟶ Y} (wp : h ≫ p₁ = p) (wp₁ : h₁ ≫ p₂ = p₁)
    (wp₂ : h₂ ≫ p₂ = p) [IsIso (P.openImmersionLowerShriekRefinementPushforward sq)]
    [IsIso (P.openImmersionLowerShriekRefinementPushforward sq₁)]
    [IsIso (P.openImmersionLowerShriekRefinementPushforward sq₂)] :
    P.lowerShriekRefinementIso sq₁ wp₁ ≪≫ P.lowerShriekRefinementIso sq wp =
      P.lowerShriekRefinementIso sq₂ wp₂ := by
  have := P.isIso_baseChange_exchangeFormalism_id sq
  have := P.isIso_baseChange_exchangeFormalism_id sq₁
  have := P.isIso_baseChange_exchangeFormalism_id sq₂
  ext1
  rw [Iso.trans_hom, P.lowerShriekRefinementIso_hom_eq, P.lowerShriekRefinementIso_hom_eq,
    P.lowerShriekRefinementIso_hom_eq]
  exact ((𝔽).refinementComparison_comp (r := SepFinType.homMk h) (s := SepFinType.homMk h₁)
    (rs := SepFinType.homMk h₂) _ _ _ _ _ _ (ObjectProperty.hom_ext _ hh) _ _ _ _ _ _).symm

end Transitivity

section Compactification

variable {P} (hP : P.IsIsoRefinementPushforward) {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The comparison `Rf_!^{c₁} ≅ Rf_!^c` of `P` along a refinement `r : c → c₁` of
compactifications (`P.lowerShriekRefinementIso` along `r.hom`). -/
noncomputable def lowerShriekOverRefinementIso {c c₁ : Compactification f.left}
    (r : Compactification.OverRefinement c c₁) :
    P.lowerShriekOfCompactification c₁ ≅ P.lowerShriekOfCompactification c :=
  haveI := r.isProper
  haveI := hP r.isPullback
  P.lowerShriekRefinementIso r.isPullback r.hom_overG

/-- The comparison along a composite of refinements is the composite of the comparisons. -/
lemma lowerShriekOverRefinementIso_trans {c c₁ c₂ : Compactification f.left}
    (r : Compactification.OverRefinement c c₁) (s : Compactification.OverRefinement c₁ c₂) :
    lowerShriekOverRefinementIso hP s ≪≫ lowerShriekOverRefinementIso hP r =
      lowerShriekOverRefinementIso hP (r.trans s) := by
  have := r.isProper
  have := s.isProper
  have := (r.trans s).isProper
  have := hP r.isPullback
  have := hP s.isPullback
  have := hP (r.trans s).isPullback
  exact P.lowerShriekRefinementIso_trans_eq r.isPullback s.isPullback (r.trans s).isPullback rfl
    r.hom_overG s.hom_overG (r.trans s).hom_overG

/-- **Independence of the refinement**: the comparisons along two refinements `r r' : c → c₁`
agree. Both become equal after composing with the comparison along the refinement of `c` by the
equalizer of `r.hom` and `r'.hom`, which is an isomorphism. -/
theorem lowerShriekOverRefinementIso_eq {c c₁ : Compactification f.left}
    (r r' : Compactification.OverRefinement c c₁) :
    lowerShriekOverRefinementIso hP r = lowerShriekOverRefinementIso hP r' := by
  let t := r.eqLocusRefinement r'
  have h₁ := lowerShriekOverRefinementIso_trans hP t r
  have h₂ := lowerShriekOverRefinementIso_trans hP t r'
  have h₃ : lowerShriekOverRefinementIso hP (t.trans r) =
      lowerShriekOverRefinementIso hP (t.trans r') := by
    have := (t.trans r).isProper
    have := (t.trans r').isProper
    have := hP (t.trans r).isPullback
    have := hP (t.trans r').isPullback
    exact P.lowerShriekRefinementIso_congr _ _ _ _ (r.eqLocusRefinement_hom_comp r')
  ext1
  exact (Iso.cancel_iso_hom_right _ _ (lowerShriekOverRefinementIso hP t)).1
    (congrArg Iso.hom (h₁.trans (h₃.trans h₂.symm)))

/-- The comparison along the identity refinement is the identity. -/
lemma lowerShriekOverRefinementIso_refl (c : Compactification f.left) :
    lowerShriekOverRefinementIso hP (Compactification.OverRefinement.refl c) = Iso.refl _ := by
  ext1
  rw [← cancel_epi (lowerShriekOverRefinementIso hP
    (Compactification.OverRefinement.refl c)).hom, Iso.refl_hom, Category.comp_id]
  exact congrArg Iso.hom ((lowerShriekOverRefinementIso_trans hP _ _).trans
    (lowerShriekOverRefinementIso_eq hP _ _))

/-- Unfolding `lowerShriekOfCompactificationIso` in terms of `lowerShriekOverRefinementIso`: the
comparison through the chosen common refinement. -/
lemma lowerShriekOfCompactificationIso_eq_overRefinementIso (c₁ c₂ : Compactification f.left) :
    lowerShriekOfCompactificationIso hP c₁ c₂ =
      lowerShriekOverRefinementIso hP
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some ≪≫
        (lowerShriekOverRefinementIso hP
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some).symm :=
  rfl

/-- For refinements `r : d → c` and `r' : d' → c`, the comparisons along `r` and `r'` agree
after composing with the comparisons along refinements `t : e → d` and `t' : e → d'`. -/
lemma lowerShriekOverRefinementIso_trans_eq_trans {c d d' e : Compactification f.left}
    (r : Compactification.OverRefinement d c) (r' : Compactification.OverRefinement d' c)
    (t : Compactification.OverRefinement e d) (t' : Compactification.OverRefinement e d') :
    lowerShriekOverRefinementIso hP r ≪≫ lowerShriekOverRefinementIso hP t =
      lowerShriekOverRefinementIso hP r' ≪≫ lowerShriekOverRefinementIso hP t' :=
  (lowerShriekOverRefinementIso_trans hP t r).trans
    ((lowerShriekOverRefinementIso_eq hP _ _).trans
      (lowerShriekOverRefinementIso_trans hP t' r').symm)

/-- The comparison `Rf_!^{c₁} ≅ Rf_!^{c₂}` of `P` may be computed through any common refinement
`r₁ : d → c₁`, `r₂ : d → c₂`. -/
theorem lowerShriekOfCompactificationIso_eq_trans_symm {c₁ c₂ d : Compactification f.left}
    (r₁ : Compactification.OverRefinement d c₁) (r₂ : Compactification.OverRefinement d c₂) :
    lowerShriekOfCompactificationIso hP c₁ c₂ =
      lowerShriekOverRefinementIso hP r₁ ≪≫ (lowerShriekOverRefinementIso hP r₂).symm := by
  rw [lowerShriekOfCompactificationIso_eq_overRefinementIso]
  obtain ⟨e, ⟨t⟩, ⟨t₀⟩⟩ := Compactification.exists_overRefinement d
    (Compactification.exists_overRefinement c₁ c₂).choose
  calc _ = (lowerShriekOverRefinementIso hP
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some ≪≫
          lowerShriekOverRefinementIso hP t₀) ≪≫
        (lowerShriekOverRefinementIso hP
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some ≪≫
          lowerShriekOverRefinementIso hP t₀).symm := by simp
    _ = (lowerShriekOverRefinementIso hP r₁ ≪≫ lowerShriekOverRefinementIso hP t) ≪≫
        (lowerShriekOverRefinementIso hP r₂ ≪≫ lowerShriekOverRefinementIso hP t).symm := by
      rw [lowerShriekOverRefinementIso_trans_eq_trans hP _ r₁ t₀ t,
        lowerShriekOverRefinementIso_trans_eq_trans hP _ r₂ t₀ t]
    _ = _ := by simp

/-- **The cocycle condition** for the comparisons of the lower shrieks of `P` attached to three
compactifications. -/
theorem lowerShriekOfCompactificationIso_trans (c₁ c₂ c₃ : Compactification f.left) :
    lowerShriekOfCompactificationIso hP c₁ c₂ ≪≫ lowerShriekOfCompactificationIso hP c₂ c₃ =
      lowerShriekOfCompactificationIso hP c₁ c₃ := by
  obtain ⟨d, ⟨r₁⟩, ⟨r₂⟩⟩ := Compactification.exists_overRefinement c₁ c₂
  obtain ⟨e, ⟨t⟩, ⟨t₃⟩⟩ := Compactification.exists_overRefinement d c₃
  rw [lowerShriekOfCompactificationIso_eq_trans_symm hP (t.trans r₁) (t.trans r₂),
    lowerShriekOfCompactificationIso_eq_trans_symm hP (t.trans r₂) t₃,
    lowerShriekOfCompactificationIso_eq_trans_symm hP (t.trans r₁) t₃]
  simp

/-- The comparison of a compactification `c₁` with a refinement `c` of `c₁` is the comparison
along the refinement. -/
theorem lowerShriekOfCompactificationIso_eq_overRefinementIso_of_refinement
    {c c₁ : Compactification f.left} (r : Compactification.OverRefinement c c₁) :
    lowerShriekOfCompactificationIso hP c₁ c = lowerShriekOverRefinementIso hP r := by
  rw [lowerShriekOfCompactificationIso_eq_trans_symm hP r
      (Compactification.OverRefinement.refl c),
    lowerShriekOverRefinementIso_refl, Iso.refl_symm, Iso.trans_refl]

/-- The comparison of a compactification with itself is the identity. -/
lemma lowerShriekOfCompactificationIso_refl (c : Compactification f.left) :
    lowerShriekOfCompactificationIso hP c c = Iso.refl _ := by
  rw [lowerShriekOfCompactificationIso_eq_overRefinementIso_of_refinement hP
    (Compactification.OverRefinement.refl c), lowerShriekOverRefinementIso_refl]

/-- The comparisons of compactifications are compatible with inverses. -/
lemma lowerShriekOfCompactificationIso_symm (c₁ c₂ : Compactification f.left) :
    (lowerShriekOfCompactificationIso hP c₁ c₂).symm =
      lowerShriekOfCompactificationIso hP c₂ c₁ := by
  have h := lowerShriekOfCompactificationIso_trans hP c₁ c₂ c₁
  rw [lowerShriekOfCompactificationIso_refl] at h
  ext : 1
  rw [Iso.symm_hom, ← cancel_epi (lowerShriekOfCompactificationIso hP c₁ c₂).hom,
    Iso.hom_inv_id]
  exact (congrArg Iso.hom h).symm

end Compactification

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *compact-support exchange map* `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` of `P` for a
compactification `c` of `f` and a compactification `c'` of `f'` lying over it along
`h : c'.Z ⟶ c.Z` with cartesian squares: the compact-support exchange map
`CategoryTheory.ExchangeFormalism.shriekBaseChange` of the exchange formalism of `P`. -/
noncomputable def lowerShriekOfCompactificationBaseChange (c : Compactification f.left)
    (c' : Compactification f'.left) (h : c'.overObj ⟶ c.overObj)
    (hi : IsPullback g' c'.overI c.overI h) (hp : IsPullback h c'.overG c.overG g) :
    P.lowerShriekOfCompactification c ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙ P.lowerShriekOfCompactification c' :=
  haveI := P.isIso_baseChange_exchangeFormalism hi
  ((𝔽).shriekBaseChange (SepFinType.homMk c.overI) (SepFinType.homMk c.overG)
    (SepFinType.homMk c'.overI) (SepFinType.homMk c'.overG) (SepFinType.homMk g')
    (SepFinType.homMk h) (SepFinType.homMk g) (SepFinType.homMk_comp_homMk hi.w)
    (SepFinType.homMk_comp_homMk hp.w))

/-- The pasting `P.lowerShriekOfCompactificationBaseChangePasting c sq` for a compactification
`c` and its base change is the compact-support exchange map of the pair. -/
lemma lowerShriekOfCompactificationBaseChangePasting_eq_baseChange
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    P.lowerShriekOfCompactificationBaseChangePasting c sq =
      P.lowerShriekOfCompactificationBaseChange c (c.ofIsPullback sq.overLeft)
        (c.overBaseChangeFst sq) (c.overBaseChange_isPullback_i sq)
        (c.overBaseChange_isPullback_g sq) := by
  have := P.isIso_baseChange_exchangeFormalism (c.overBaseChange_isPullback_i sq)
  rw [lowerShriekOfCompactificationBaseChangePasting, lowerShriekOfCompactificationBaseChange,
    ExchangeFormalism.shriekBaseChange, P.baseChange_eq_pfBaseChange,
    P.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso_hom_eq]
  rfl

/-- **The compact-support exchange maps of `P` are compatible with the comparisons along
refinements**: for refinements `r` of `d` by `c` (compactifications of `f`) and `r'` of `d'` by
`c'` (compactifications of `f'`), compatible with the maps `hc : c'.Z ⟶ c.Z` and
`hd : d'.Z ⟶ d.Z`, the exchange maps of `(c, c')` and `(d, d')` are intertwined by the
comparisons `Rf_!^d ≅ Rf_!^c` and `Rf'_!^{d'} ≅ Rf'_!^{c'}`. -/
theorem lowerShriekOfCompactificationBaseChange_refinementIso
    {c d : Compactification f.left} {c' d' : Compactification f'.left}
    (r : Compactification.OverRefinement c d) (r' : Compactification.OverRefinement c' d')
    (hc : c'.overObj ⟶ c.overObj) (hci : IsPullback g' c'.overI c.overI hc)
    (hcp : IsPullback hc c'.overG c.overG g) (hd : d'.overObj ⟶ d.overObj)
    (hdi : IsPullback g' d'.overI d.overI hd) (hdp : IsPullback hd d'.overG d.overG g)
    (hcomm : hc ≫ r.hom = r'.hom ≫ hd)
    [IsIso (P.openImmersionLowerShriekRefinementPushforward r.isPullback)]
    [IsIso (P.openImmersionLowerShriekRefinementPushforward r'.isPullback)] :
    Functor.whiskerRight (P.lowerShriekRefinementIso r.isPullback r.hom_overG).hom
        (boundedConstructibleUpperStar Λ ℓ g) ≫
      P.lowerShriekOfCompactificationBaseChange c c' hc hci hcp =
    P.lowerShriekOfCompactificationBaseChange d d' hd hdi hdp ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
        (P.lowerShriekRefinementIso r'.isPullback r'.hom_overG).hom := by
  have := P.isIso_baseChange_exchangeFormalism_id r.isPullback
  have := P.isIso_baseChange_exchangeFormalism_id r'.isPullback
  have := P.isIso_baseChange_exchangeFormalism hci
  have := P.isIso_baseChange_exchangeFormalism hdi
  rw [P.lowerShriekRefinementIso_hom_eq, P.lowerShriekRefinementIso_hom_eq]
  exact (𝔽).shriekBaseChange_refinementComparison (SepFinType.homMk c.overI)
    (SepFinType.homMk c.overG) (SepFinType.homMk d.overI) (SepFinType.homMk d.overG)
    (SepFinType.homMk c'.overI) (SepFinType.homMk c'.overG) (SepFinType.homMk d'.overI)
    (SepFinType.homMk d'.overG) (SepFinType.homMk g') (SepFinType.homMk g)
    (SepFinType.homMk r.hom) (SepFinType.homMk_comp_homMk (a := 𝟙 X) r.isPullback.w)
    (ObjectProperty.hom_ext _ r.hom_overG) (SepFinType.homMk r'.hom)
    (SepFinType.homMk_comp_homMk (a := 𝟙 X') r'.isPullback.w)
    (ObjectProperty.hom_ext _ r'.hom_overG) (SepFinType.homMk hc)
    (SepFinType.homMk_comp_homMk hci.w) (SepFinType.homMk_comp_homMk hcp.w)
    (SepFinType.homMk hd) (SepFinType.homMk_comp_homMk hdi.w)
    (SepFinType.homMk_comp_homMk hdp.w) (SepFinType.homMk_comp_homMk hcomm)

variable {P} (hP : P.IsIsoRefinementPushforward) (sq : IsPullback g' f' f g)

/-- The compact-support exchange map of `P` for a compactification and its base change. -/
local notation "𝔼" c => lowerShriekOfCompactificationBaseChange P c
  (Compactification.ofIsPullback sq.overLeft c)
  (Compactification.overBaseChangeFst c sq) (Compactification.overBaseChange_isPullback_i c sq)
  (Compactification.overBaseChange_isPullback_g c sq)

/-- The compact-support exchange maps of `P` of the base changes of two compactifications `c₁`
and `c₂` of `f` are intertwined by the comparisons `Rf_!^{c₁} ≅ Rf_!^{c₂}` and
`Rf'_!^{c₁'} ≅ Rf'_!^{c₂'}`. -/
theorem lowerShriekOfCompactificationBaseChange_iso (c₁ c₂ : Compactification f.left) :
    Functor.whiskerRight (lowerShriekOfCompactificationIso hP c₁ c₂).hom
        (boundedConstructibleUpperStar Λ ℓ g) ≫ (𝔼 c₂) =
      (𝔼 c₁) ≫ Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
        (lowerShriekOfCompactificationIso hP (c₁.ofIsPullback sq.overLeft)
          (c₂.ofIsPullback sq.overLeft)).hom := by
  obtain ⟨d, ⟨r₁⟩, ⟨r₂⟩⟩ := Compactification.exists_overRefinement c₁ c₂
  have := r₁.isProper
  have := r₂.isProper
  have := (r₁.ofIsPullback sq).isProper
  have := (r₂.ofIsPullback sq).isProper
  have := hP r₁.isPullback
  have := hP r₂.isPullback
  have := hP (r₁.ofIsPullback sq).isPullback
  have := hP (r₂.ofIsPullback sq).isPullback
  have h₁ := P.lowerShriekOfCompactificationBaseChange_refinementIso r₁
    (r₁.ofIsPullback sq) _ (d.overBaseChange_isPullback_i sq) (d.overBaseChange_isPullback_g sq)
    _ (c₁.overBaseChange_isPullback_i sq) (c₁.overBaseChange_isPullback_g sq)
    (Compactification.OverRefinement.ofIsPullback_hom_overBaseChangeFst sq r₁).symm
  have h₂ := P.lowerShriekOfCompactificationBaseChange_refinementIso r₂
    (r₂.ofIsPullback sq) _ (d.overBaseChange_isPullback_i sq) (d.overBaseChange_isPullback_g sq)
    _ (c₂.overBaseChange_isPullback_i sq) (c₂.overBaseChange_isPullback_g sq)
    (Compactification.OverRefinement.ofIsPullback_hom_overBaseChangeFst sq r₂).symm
  have e₁ := lowerShriekOfCompactificationIso_eq_overRefinementIso_of_refinement hP r₁
  have e₂ := lowerShriekOfCompactificationIso_eq_overRefinementIso_of_refinement hP r₂
  have e₁' := lowerShriekOfCompactificationIso_eq_overRefinementIso_of_refinement hP
    (r₁.ofIsPullback sq)
  have e₂' := lowerShriekOfCompactificationIso_eq_overRefinementIso_of_refinement hP
    (r₂.ofIsPullback sq)
  simp only [lowerShriekOverRefinementIso] at e₁ e₂ e₁' e₂'
  rw [← e₁, ← e₁'] at h₁
  rw [← e₂, ← e₂'] at h₂
  rw [← lowerShriekOfCompactificationIso_trans hP c₁ d c₂,
    ← lowerShriekOfCompactificationIso_trans hP (c₁.ofIsPullback sq.overLeft)
      (d.ofIsPullback sq.overLeft) (c₂.ofIsPullback sq.overLeft),
    ← lowerShriekOfCompactificationIso_symm hP c₂ d,
    ← lowerShriekOfCompactificationIso_symm hP (c₂.ofIsPullback sq.overLeft)
      (d.ofIsPullback sq.overLeft)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
    Category.assoc]
  exact Iso.comp_inv_comp_eq_of_comm
    (Functor.isoWhiskerRight (lowerShriekOfCompactificationIso hP c₁ d) _)
    (Functor.isoWhiskerRight (lowerShriekOfCompactificationIso hP c₂ d) _)
    (Functor.isoWhiskerLeft _ (lowerShriekOfCompactificationIso hP
      (c₁.ofIsPullback sq.overLeft) (d.ofIsPullback sq.overLeft)))
    (Functor.isoWhiskerLeft _ (lowerShriekOfCompactificationIso hP
      (c₂.ofIsPullback sq.overLeft) (d.ofIsPullback sq.overLeft))) _ _ _ h₁ h₂

/-- The compact-support exchange map of `P` of a pair `(c, c')` is the exchange map of `c` and
its base change, followed by the comparison of the base change of `c` with `c'`. -/
theorem lowerShriekOfCompactificationBaseChange_eq (c : Compactification f.left)
    (c' : Compactification f'.left) (h : c'.overObj ⟶ c.overObj)
    (hi : IsPullback g' c'.overI c.overI h) (hp : IsPullback h c'.overG c.overG g) :
    P.lowerShriekOfCompactificationBaseChange c c' h hi hp =
      (𝔼 c) ≫ Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
        (lowerShriekOfCompactificationIso hP (c.ofIsPullback sq.overLeft) c').hom := by
  let e := Compactification.OverRefinement.toOfIsPullback sq c c' h hi hp
  have := e.isProper
  have := (Compactification.OverRefinement.refl c).isProper
  have := hP e.isPullback
  have := hP (Compactification.OverRefinement.refl c).isPullback
  have hN := P.lowerShriekOfCompactificationBaseChange_refinementIso
    (Compactification.OverRefinement.refl c) e h hi hp
    (c.overBaseChangeFst sq) (c.overBaseChange_isPullback_i sq)
    (c.overBaseChange_isPullback_g sq)
    (by simp [e, Compactification.OverRefinement.refl_hom])
  have e₁ := lowerShriekOfCompactificationIso_eq_overRefinementIso_of_refinement hP
    (Compactification.OverRefinement.refl c)
  have e₂ := lowerShriekOfCompactificationIso_eq_overRefinementIso_of_refinement hP e
  simp only [lowerShriekOverRefinementIso] at e₁ e₂
  rw [← e₁, ← e₂, lowerShriekOfCompactificationIso_refl] at hN
  refine NatTrans.ext (funext fun K ↦ ?_)
  have hK := congr_app hN K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Iso.refl_hom, NatTrans.id_app,
    Functor.whiskerLeft_app] at hK ⊢
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at hK
  exact hK

/-- **The compact-support base change of `P` is independent of the compactification**: for any
compactification `c` of `f` and any compactification `c'` of `f'` lying over `c` along
`h : c'.Z ⟶ c.Z` with cartesian squares, `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` is the
compact-support exchange map of `(c, c')`, conjugated by the comparisons `Rf_! ≅ Rf_!^c` and
`Rf'_!^{c'} ≅ Rf'_!`. -/
theorem lowerShriekBaseChange_eq_baseChange (c : Compactification f.left)
    (c' : Compactification f'.left) (h : c'.overObj ⟶ c.overObj)
    (hi : IsPullback g' c'.overI c.overI h) (hp : IsPullback h c'.overG c.overG g) :
    lowerShriekBaseChange hP sq =
      Functor.whiskerRight (lowerShriekOfCompactificationIso hP
          (compactificationOverField f) c).hom (boundedConstructibleUpperStar Λ ℓ g) ≫
        P.lowerShriekOfCompactificationBaseChange c c' h hi hp ≫
        Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
          (lowerShriekOfCompactificationIso hP c' (compactificationOverField f')).hom := by
  rw [lowerShriekBaseChange, P.lowerShriekOfCompactificationBaseChangePasting_eq_baseChange,
    lowerShriekOfCompactificationBaseChange_eq hP sq c c' h hi hp]
  simp only [Category.assoc]
  rw [reassoc_of% (lowerShriekOfCompactificationBaseChange_iso hP sq
      (compactificationOverField f) c)]
  simp only [← Functor.whiskerLeft_comp, ← Iso.trans_hom, lowerShriekOfCompactificationIso_trans]

end BaseChange

end BoundedConstructiblePushforwardData

end AlgebraicGeometry.ProEtale.CondensedRing
