/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.OverRefinementBaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Iso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek

/-!

# Independence of the compact-support base change from the compactification

Let `sq : IsPullback g' f' f g` be a cartesian square of separated `k`-schemes of finite type.
The compact-support base change `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded constructible
`ℚ̄_ℓ`-sheaves (`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl`) is
defined through the chosen compactification `c_f` of `f` and its base change. This file shows
that it can be computed through any compactification `c` of `f` and any compactification `c'`
of `f'` lying over `c` along a morphism `h : c'.Z ⟶ c.Z` with cartesian squares
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq`): it is the
compact-support exchange map of the pair `(c, c')`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationBaseChange`), conjugated
by the comparison isomorphisms `Rf_! ≅ Rf_!^c` and `Rf'_!^{c'} ≅ Rf'_!` of the independence of the
lower shriek from the compactification (blueprint `proposition-composition-base-change-rf-shriek`,
clause (4): "`Ex_!` is independent of the chosen compactification and compatible with the refinement
comparison isomorphisms").

The proof is formal: the compact-support exchange maps are those of the exchange formalism
`ProEtale.CondensedRing.boundedConstructibleExchangeFormalism`, which are compatible with the
comparisons along refinements
(`CategoryTheory.ExchangeFormalism.shriekBaseChange_refinementComparison`),
and the comparisons of compactifications are computed along common refinements (blueprint
`proposition-construction-independence-rf-shriek`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

section Compactification

variable (c : Compactification f.left) (c' : Compactification f'.left)
  (h : c'.overObj ⟶ c.overObj) (hi : IsPullback g' c'.overI c.overI h)
  (hp : IsPullback h c'.overG c.overG g)

/-- The *compact-support exchange map* `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` of a compactification
`c` of `f` and a compactification `c'` of `f'` lying over it along `h : c'.Z ⟶ c.Z` with cartesian
squares: the base change map `Lg^* Rp_* ⟶ Rp'_* Lh^*` of the proper square applied after `i_!`,
followed by the inverse of the extension-by-zero exchange morphism of the open square (the
compact-support exchange map `CategoryTheory.ExchangeFormalism.shriekBaseChange` of the exchange
formalism). -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChange :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ c' :=
  haveI := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ hi
  ((𝔽).shriekBaseChange (SepFinType.homMk c.overI) (SepFinType.homMk c.overG)
    (SepFinType.homMk c'.overI) (SepFinType.homMk c'.overG) (SepFinType.homMk g')
    (SepFinType.homMk h) (SepFinType.homMk g) (SepFinType.homMk_comp_homMk hi.w)
    (SepFinType.homMk_comp_homMk hp.w))

/-- The compact-support exchange map of a pair of compactifications is the base-change morphism
of the proper squares after the extension by zero, followed by the inverse of the
extension-by-zero exchange morphism of the open squares. -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChange_eq :
    boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c c' h hi hp =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
            (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)
          (boundedConstructibleBaseChange ℓ hp.toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
            (Profinite.padicAlgClRingObj ℓ) ℓ hi).hom
          (boundedConstructibleLowerStarOfIsProper ℓ c'.overG) ≫
        (Functor.associator _ _ _).hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChange,
    ExchangeFormalism.shriekBaseChange, boundedConstructibleBaseChange_eq_pfBaseChange,
    boundedConstructibleOpenImmersionLowerShriekBaseChangeIso_hom_eq]
  rfl

/-- The compact-support base-change morphism for the compactification `c` and its base change is
the compact-support exchange map of the pair. -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq_baseChange
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ c sq =
      boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c
        (c.ofIsPullback sq.overLeft) (c.overBaseChangeFst sq)
        (c.overBaseChange_isPullback_i sq) (c.overBaseChange_isPullback_g sq) := by
  have := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
    (c.overBaseChange_isPullback_i sq)
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq,
    boundedConstructibleLowerShriekOfCompactificationBaseChange,
    ExchangeFormalism.shriekBaseChange, boundedConstructibleBaseChange_eq_pfBaseChange,
    boundedConstructibleOpenImmersionLowerShriekBaseChangeIso_hom_eq]
  rfl

/-- **The compact-support exchange maps are compatible with the comparisons along refinements**:
for refinements `r` of `d` by `c` (compactifications of `f`) and `r'` of `d'` by `c'`
(compactifications of `f'`), compatible with the maps `hc : c'.Z ⟶ c.Z` and `hd : d'.Z ⟶ d.Z`,
the exchange maps of `(c, c')` and `(d, d')` are intertwined by the comparisons
`Rf_!^d ≅ Rf_!^c` and `Rf'_!^{d'} ≅ Rf'_!^{c'}`. -/
theorem boundedConstructibleLowerShriekOfCompactificationBaseChange_refinementIso'
    {c d : Compactification f.left} {c' d' : Compactification f'.left}
    (r : Compactification.OverRefinement c d) (r' : Compactification.OverRefinement c' d')
    (hc : c'.overObj ⟶ c.overObj) (hci : IsPullback g' c'.overI c.overI hc)
    (hcp : IsPullback hc c'.overG c.overG g) (hd : d'.overObj ⟶ d.overObj)
    (hdi : IsPullback g' d'.overI d.overI hd) (hdp : IsPullback hd d'.overG d.overG g)
    (hcomm : hc ≫ r.hom = r'.hom ≫ hd)
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ r.isPullback)]
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ r'.isPullback)] :
    Functor.whiskerRight (boundedConstructibleLowerShriekRefinementIso' ℓ r.isPullback
        r.hom_overG).hom (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) ≫
      boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c c' hc hci hcp =
    boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ d d' hd hdi hdp ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
        (boundedConstructibleLowerShriekRefinementIso' ℓ r'.isPullback r'.hom_overG).hom := by
  have := isIso_baseChange_boundedConstructibleExchangeFormalism_id ℓ r.isPullback
  have := isIso_baseChange_boundedConstructibleExchangeFormalism_id ℓ r'.isPullback
  have := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ hci
  have := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ hdi
  rw [boundedConstructibleLowerShriekRefinementIso'_hom_eq,
    boundedConstructibleLowerShriekRefinementIso'_hom_eq]
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

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- **Horizontal pasting** of the compact-support exchange maps of pairs of compactifications:
for compactifications `c`, `c₂`, `c₁` of `f`, `f₂`, `f₁` lying over each other along
`h₂ : c₂.Z ⟶ c.Z` and `h₁ : c₁.Z ⟶ c₂.Z`, the exchange map of `(c, c₁)` along `h₁ ≫ h₂` is the
composite of the exchange maps of `(c, c₂)` and `(c₂, c₁)`, after inserting the composition
isomorphisms of the pullbacks. -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChange_paste_horiz
    {X₁ X₂ Y₁ Y₂ : Over (Spec (.of k))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
    [IsSeparated X₁.hom] [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
    [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
    [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]
    {g'₁ : X₁ ⟶ X₂} {g'₂ : X₂ ⟶ X} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {g₁ : Y₁ ⟶ Y₂}
    {g₂ : Y₂ ⟶ Y} (c : Compactification f.left) (c₂ : Compactification f₂.left)
    (c₁ : Compactification f₁.left) (h₂ : c₂.overObj ⟶ c.overObj)
    (h₁ : c₁.overObj ⟶ c₂.overObj) (hi₂ : IsPullback g'₂ c₂.overI c.overI h₂)
    (hp₂ : IsPullback h₂ c₂.overG c.overG g₂) (hi₁ : IsPullback g'₁ c₁.overI c₂.overI h₁)
    (hp₁ : IsPullback h₁ c₁.overG c₂.overG g₁) :
    boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c c₁ (h₁ ≫ h₂)
        (hi₁.paste_horiz hi₂) (hp₁.paste_horiz hp₂) =
      ((TwoSquare.vComp (boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c c₂ h₂
        hi₂ hp₂) (boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c₂ c₁ h₁ hi₁
          hp₁)).whiskerLeft (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g'₁
              g'₂).inv).whiskerRight
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g₁ g₂).hom := by
  have := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ hi₁
  have := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ hi₂
  have : IsIso ((𝔽).baseChange (SepFinType.homMk g'₁ ≫ SepFinType.homMk g'₂)
      (SepFinType.homMk c₁.overI) (SepFinType.homMk c.overI)
      (SepFinType.homMk h₁ ≫ SepFinType.homMk h₂)
      (SepFinType.homMk_comp_homMk (hi₁.paste_horiz hi₂).w)) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ (hi₁.paste_horiz hi₂)
  have h := (𝔽).shriekBaseChange_paste_horiz (SepFinType.homMk c.overI)
    (SepFinType.homMk c.overG) (SepFinType.homMk c₂.overI) (SepFinType.homMk c₂.overG)
    (SepFinType.homMk c₁.overI) (SepFinType.homMk c₁.overG) (SepFinType.homMk g'₁)
    (SepFinType.homMk g'₂) (SepFinType.homMk h₁) (SepFinType.homMk h₂) (SepFinType.homMk g₁)
    (SepFinType.homMk g₂) (SepFinType.homMk_comp_homMk hi₁.w)
    (SepFinType.homMk_comp_homMk hp₁.w) (SepFinType.homMk_comp_homMk hi₂.w)
    (SepFinType.homMk_comp_homMk hp₂.w) (SepFinType.homMk_comp_homMk (hi₁.paste_horiz hi₂).w)
    (SepFinType.homMk_comp_homMk (hp₁.paste_horiz hp₂).w)
  rw [ExchangeFormalism.pbComp'_rfl, ExchangeFormalism.pbComp'_rfl] at h
  exact h

end Compactification

/-! ### `ℚ̄_ℓ`-sheaves -/

section PadicAlgCl

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- The comparison of a compactification with itself is the identity. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl
    (c : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c c = Iso.refl _ := by
  have h := boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans ℓ c c c
  ext : 1
  rw [← cancel_epi (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c c).hom]
  simpa using congrArg Iso.hom h

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- The comparisons of compactifications are compatible with inverses. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm
    (c₁ c₂ : Compactification f.left) :
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₂).symm =
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₂ c₁ := by
  have h := boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans ℓ c₁ c₂ c₁
  rw [boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl] at h
  ext : 1
  rw [Iso.symm_hom, ← cancel_epi (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl
    ℓ c₁ c₂).hom, Iso.hom_inv_id]
  exact (congrArg Iso.hom h).symm

variable (sq : IsPullback g' f' f g)

/-- The compact-support exchange map of a compactification and its base change. -/
local notation "𝔼" c => boundedConstructibleLowerShriekOfCompactificationBaseChange
  ℓ c (Compactification.ofIsPullback sq.overLeft c)
  (Compactification.overBaseChangeFst c sq) (Compactification.overBaseChange_isPullback_i c sq)
  (Compactification.overBaseChange_isPullback_g c sq)

/-- The compact-support exchange maps of the base changes of two compactifications `c₁` and
`c₂` of `f` are intertwined by the comparisons `Rf_!^{c₁} ≅ Rf_!^{c₂}` and
`Rf'_!^{c₁'} ≅ Rf'_!^{c₂'}`. -/
theorem boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl_iso'
    (c₁ c₂ : Compactification f.left) :
    Functor.whiskerRight (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁
        c₂).hom (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) ≫ (𝔼 c₂) =
      (𝔼 c₁) ≫ Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ g') (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (c₁.ofIsPullback sq.overLeft) (c₂.ofIsPullback sq.overLeft)).hom := by
  obtain ⟨d, ⟨r₁⟩, ⟨r₂⟩⟩ := Compactification.exists_overRefinement c₁ c₂
  have := r₁.isProper
  have := r₂.isProper
  have := (r₁.ofIsPullback sq).isProper
  have := (r₂.ofIsPullback sq).isProper
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    r₁.isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    r₂.isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (r₁.ofIsPullback sq).isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (r₂.ofIsPullback sq).isPullback
  have h₁ := boundedConstructibleLowerShriekOfCompactificationBaseChange_refinementIso'
    ℓ r₁
    (r₁.ofIsPullback sq) _ (d.overBaseChange_isPullback_i sq) (d.overBaseChange_isPullback_g sq)
    _ (c₁.overBaseChange_isPullback_i sq) (c₁.overBaseChange_isPullback_g sq)
    (Compactification.OverRefinement.ofIsPullback_hom_overBaseChangeFst sq r₁).symm
  have h₂ := boundedConstructibleLowerShriekOfCompactificationBaseChange_refinementIso'
    ℓ r₂
    (r₂.ofIsPullback sq) _ (d.overBaseChange_isPullback_i sq) (d.overBaseChange_isPullback_g sq)
    _ (c₂.overBaseChange_isPullback_i sq) (c₂.overBaseChange_isPullback_g sq)
    (Compactification.OverRefinement.ofIsPullback_hom_overBaseChangeFst sq r₂).symm
  rw [← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq,
    ← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq] at h₁ h₂
  rw [← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans ℓ c₁ d c₂,
    ← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans ℓ
      (c₁.ofIsPullback sq.overLeft) (d.ofIsPullback sq.overLeft) (c₂.ofIsPullback sq.overLeft),
    ← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm ℓ c₂ d,
    ← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm ℓ
      (c₂.ofIsPullback sq.overLeft) (d.ofIsPullback sq.overLeft)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
    Category.assoc]
  exact Iso.comp_inv_comp_eq_of_comm
    (Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ d) _)
    (Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₂ d) _)
    (Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (c₁.ofIsPullback sq.overLeft) (d.ofIsPullback sq.overLeft)))
    (Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (c₂.ofIsPullback sq.overLeft) (d.ofIsPullback sq.overLeft))) _ _ _ h₁ h₂


/-- The compact-support exchange map of a pair `(c, c')` is the exchange map of `c` and its base
change, followed by the comparison of the base change of `c` with `c'`. -/
theorem boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl_eq
    (c : Compactification f.left) (c' : Compactification f'.left)
    (h : c'.overObj ⟶ c.overObj) (hi : IsPullback g' c'.overI c.overI h)
    (hp : IsPullback h c'.overG c.overG g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ
        c c' h hi hp =
      (𝔼 c) ≫ Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ g') (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (c.ofIsPullback sq.overLeft) c').hom := by
  let e := Compactification.OverRefinement.toOfIsPullback sq c c' h hi hp
  have := e.isProper
  have := (Compactification.OverRefinement.refl c).isProper
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    e.isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (Compactification.OverRefinement.refl c).isPullback
  have hN := boundedConstructibleLowerShriekOfCompactificationBaseChange_refinementIso'
    ℓ (Compactification.OverRefinement.refl c) e h hi hp
    (c.overBaseChangeFst sq) (c.overBaseChange_isPullback_i sq)
    (c.overBaseChange_isPullback_g sq)
    (by simp [e, Compactification.OverRefinement.refl_hom])
  rw [← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq,
    ← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl] at hN
  refine NatTrans.ext (funext fun K ↦ ?_)
  have hK := congr_app hN K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Iso.refl_hom, NatTrans.id_app,
    Functor.whiskerLeft_app] at hK ⊢
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at hK
  exact hK

/-- **The compact-support base change is independent of the compactification**: for any
compactification `c` of `f` and any compactification `c'` of `f'` lying over `c` along
`h : c'.Z ⟶ c.Z` with cartesian squares, `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` is the
compact-support exchange map of `(c, c')`, conjugated by the comparisons `Rf_! ≅ Rf_!^c` and
`Rf'_!^{c'} ≅ Rf'_!` (blueprint `proposition-composition-base-change-rf-shriek`, clause (4)). -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange
    (c : Compactification f.left) (c' : Compactification f'.left)
    (h : c'.overObj ⟶ c.overObj) (hi : IsPullback g' c'.overI c.overI h)
    (hp : IsPullback h c'.overG c.overG g) :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq =
      Functor.whiskerRight (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField f) c).hom
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) ≫
        boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c c' h hi hp ≫
        Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c'
            (compactificationOverField f')).hom := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq,
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq',
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq_baseChange,
    boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl_eq ℓ sq c c' h hi hp]
  simp only [Category.assoc]
  rw [reassoc_of% (boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl_iso' ℓ sq
      (compactificationOverField f) c)]
  simp only [← Functor.whiskerLeft_comp, ← Iso.trans_hom,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans]

end PadicAlgCl

end AlgebraicGeometry.ProEtale.CondensedRing
