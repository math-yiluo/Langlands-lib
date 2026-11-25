/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationRestrict
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Section
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# The compactly supported direct image along an étale morphism is the extension by zero

Let `e : X ⟶ Y` be étale with a compactification `c`. The comparison
`Φ_c : De_! ⟶ Rf_!(c)` (`AlgebraicGeometry.Etale.compactificationEtaleComparison`) is an
isomorphism (`AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`): it commutes with
base change, so it suffices to check it over geometric points of `Y`, where `X` is covered by
sections of `e`, and it commutes with restriction to these open pieces, over which `e` is an
isomorphism.

## Main statements

- `AlgebraicGeometry.Etale.compactificationEtaleComparison_baseChange`
- `AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

attribute [local instance] Compactification.isOpenImmersion

section Transpose

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)

/-- The comparison `De_! ⟶ Rf_!(c)` is the transpose of the candidate unit under `De_! ⊣ Le^*`. -/
@[reassoc]
lemma unit_map_compactificationEtaleComparison
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedEtaleLowerShriekAdjunction _ e).unit.app N ≫
        L((e)^*[ModuleCat.{u + 1} Λ]).map ((compactificationEtaleComparison Λ e c).app N) =
      (compactificationEtaleUnit Λ e c).app N := by
  simp only [compactificationEtaleComparison, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Functor.map_comp]
  have h := (derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) e).unit.naturality
    ((compactificationEtaleUnit Λ e c).app N)
  dsimp at h
  rw [← reassoc_of% h]
  erw [Adjunction.right_triangle_components_assoc]
  simp

/-- The adjunction `Rf_!(c) ⊣ Le^*` obtained from `De_! ⊣ Le^*` when the comparison
`De_! ⟶ Rf_!(c)` is an isomorphism; its unit is the candidate unit. -/
noncomputable def compactificationEtaleAdjunction
    [IsIso (compactificationEtaleComparison Λ e c)] :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ⊣ L((e)^*[ModuleCat.{u + 1} Λ]) :=
  (derivedEtaleLowerShriekAdjunction _ e).ofNatIsoLeft
    (asIso (compactificationEtaleComparison Λ e c))

lemma compactificationEtaleAdjunction_unit_app [IsIso (compactificationEtaleComparison Λ e c)]
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactificationEtaleAdjunction Λ e c).unit.app N =
      (compactificationEtaleUnit Λ e c).app N := by
  simp only [compactificationEtaleAdjunction, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, asIso_hom]
  exact unit_map_compactificationEtaleComparison Λ e c N

end Transpose

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y} {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e) [_root_.AlgebraicGeometry.Etale e]
  [_root_.AlgebraicGeometry.Etale e']

/-- **The comparison `De_! ⟶ Rf_!(c)` commutes with base change**: for a cartesian square
`g' ≫ e = e' ≫ g`, the comparison for the base change `c'` of `c` at `Lg'^* N` is `Lg^*` of
the comparison at `N`, read through the base change isomorphisms `De'_! Lg'^* ≅ Lg^* De_!` and
`Ex_!(c)`. -/
theorem compactificationEtaleComparison_baseChange
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedEtaleLowerShriekBaseChangeIso _ sq).hom.app N ≫
      L((g)^*[ModuleCat.{u + 1} Λ]).map ((compactificationEtaleComparison Λ e c).app N) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq c).app N =
    (compactificationEtaleComparison Λ e' (c.ofIsPullback sq)).app
      (L((g')^*[ModuleCat.{u + 1} Λ]).obj N) := by
  apply ((derivedEtaleLowerShriekAdjunction _ e').homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [unit_map_compactificationEtaleComparison,
    reassoc_of% (unit_map_derivedEtaleLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq N),
    ← compactificationEtaleUnit_baseChange Λ sq c N, ← unit_map_compactificationEtaleComparison,
    Functor.map_comp, Category.assoc]
  have hn := (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).inv.naturality
    ((compactificationEtaleComparison Λ e c).app N)
  dsimp at hn
  rw [← reassoc_of% hn]
  rfl

end BaseChange

section Restrict

variable {X Y X₀ : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e) (v : X₀ ⟶ X) [IsOpenImmersion v]

/-- The composition isomorphism `D(v ≫ e)_! ≅ Dv_! ⋙ De_!` of the extensions by zero, as the
comparison of the left adjoints of `L(v ≫ e)^* ≅ Le^* ⋙ Lv^*`. -/
noncomputable def etaleLowerShriekRestrictOpenIso :
    D(etaleLowerShriek (ModuleCat.{u + 1} Λ) (v ≫ e) inferInstance) ≅
      D((v)_!open[ModuleCat.{u + 1} Λ]) ⋙
        D(etaleLowerShriek (ModuleCat.{u + 1} Λ) e inferInstance) :=
  Adjunction.leftAdjointUniq (derivedEtaleLowerShriekAdjunction _ (v ≫ e))
    (((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ v).comp
      (derivedEtaleLowerShriekAdjunction _ e)).ofNatIsoRight
        (leftDerivedUpperStarComp _ v e (v ≫ e) rfl).symm)

/-- **The comparison `De_! ⟶ Rf_!(c)` commutes with restriction to an open subscheme**: on
`Dv_! M`, it is the comparison for `c.restrictOpen v` at `M`, up to the composition
isomorphisms. -/
theorem compactificationEtaleComparison_restrictOpen
    (M : _root_.DerivedCategory (Sheaf X₀.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactificationEtaleComparison Λ (v ≫ e) (c.restrictOpen v)).app M ≫
        R((c.g)_*[ModuleCat.{u + 1} Λ]).map ((restrictOpenLowerShriekIso Λ c v).hom.app M) =
      (etaleLowerShriekRestrictOpenIso Λ e v).hom.app M ≫
        (compactificationEtaleComparison Λ e c).app (D((v)_!open[ModuleCat.{u + 1} Λ]).obj M) := by
  apply ((derivedEtaleLowerShriekAdjunction _ (v ≫ e)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [unit_map_compactificationEtaleComparison_assoc, compactificationEtaleUnit_restrictOpen,
    etaleLowerShriekRestrictOpenIso, Adjunction.unit_leftAdjointUniq_hom_app_assoc]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Adjunction.comp_unit_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v e (v ≫ e) rfl).inv.naturality
    ((compactificationEtaleComparison Λ e c).app (D((v)_!open[ModuleCat.{u + 1} Λ]).obj M))
  dsimp at hn
  simp only [Functor.comp_obj]
  rw [← hn, ← Functor.map_comp_assoc (L((v)^*[ModuleCat.{u + 1} Λ])),
    unit_map_compactificationEtaleComparison]

/-- **Isomorphy of the comparison is local on `X`**: if `X` is covered by open subschemes
`v_i : U_i ⟶ X` over which the comparison is an isomorphism, then it is an isomorphism. The
right adjoints of the comparison are compared along the jointly conservative restrictions
`Lv_i^*` (`CategoryTheory.conjugateEquiv_whiskerLeft`). -/
theorem isIso_compactificationEtaleComparison_of_cover {ι : Type u} {U : ι → Scheme.{u}}
    (w : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (w i)]
    (hw : ∀ x : X, ∃ (i : ι) (y : U i), (w i).base y = x)
    (h : ∀ i, IsIso (compactificationEtaleComparison Λ (w i ≫ e) (c.restrictOpen (w i)))) :
    IsIso (compactificationEtaleComparison Λ e c) := by
  have := isLeftAdjoint_rightDerivedLowerShriekOfCompactification Λ c
  let adj₁ := Adjunction.ofIsLeftAdjoint (Rf_!(c)[ModuleCat.{u + 1} Λ])
  let adj₂ := derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) e
  suffices IsIso (conjugateEquiv adj₁ adj₂ (compactificationEtaleComparison Λ e c)) from
    conjugateEquiv_of_iso adj₁ adj₂ _
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ w hw _ fun i ↦ ?_
  have hi : IsIso (Functor.whiskerLeft D((w i)_!open[ModuleCat.{u + 1} Λ])
      (compactificationEtaleComparison Λ e c)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [Functor.whiskerLeft_app]
    have h₁ := compactificationEtaleComparison_restrictOpen Λ e c (w i) M
    have : IsIso ((etaleLowerShriekRestrictOpenIso Λ e (w i)).hom.app M ≫
        (compactificationEtaleComparison Λ e c).app
          (D((w i)_!open[ModuleCat.{u + 1} Λ]).obj M)) := by
      rw [← h₁]
      infer_instance
    exact IsIso.of_isIso_comp_left ((etaleLowerShriekRestrictOpenIso Λ e (w i)).hom.app M) _
  have := conjugateEquiv_whiskerLeft adj₁ adj₂
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ (w i))
    (compactificationEtaleComparison Λ e c)
  have h₂ : IsIso (Functor.whiskerRight (conjugateEquiv adj₁ adj₂
      (compactificationEtaleComparison Λ e c)) L(((w i))^*[ModuleCat.{u + 1} Λ])) := by
    rw [← this]
    infer_instance
  exact (NatTrans.isIso_iff_isIso_app _).1 h₂ K

end Restrict

section Iso

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)

/-- **Over an isomorphism, the comparison `De_! ⟶ Rf_!(c)` is an isomorphism.** The candidate
unit is invertible: `Lq^* ⟶ Dσ_! Lσ^* Lq^*` is the unit of an adjunction whose left adjoint
`Lq^* ⋙ Lσ^* ≅ 𝟭` is fully faithful, and `Lq_Z^* Dj_!` lies in the image of `Dσ_!`, the
projection `q_Z` being an isomorphism; and the counit of `De_! ⊣ Le^*` is invertible, `Le^*`
being an equivalence. -/
theorem isIso_compactificationEtaleComparison_of_isIso [IsIso e] :
    IsIso (compactificationEtaleComparison Λ e c) := by
  -- the candidate unit is invertible
  have hu : ∀ N, IsIso ((compactificationEtaleUnit Λ e c).app N) := by
    intro N
    let adj := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (pullback.snd c.g e)).comp (clopenUpperStarLowerShriekAdjunction Λ c.selfGraph)
    have hff : (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} Λ]) ⋙
        L((c.selfGraph)^*[ModuleCat.{u + 1} Λ])).FullyFaithful :=
      (Functor.FullyFaithful.id _).ofIso (leftDerivedUpperStarCompSectionIso _ c.selfGraph
        (pullback.snd c.g e) c.selfGraph_snd).symm
    have := hff.full
    have := hff.faithful
    have h₁ : IsIso (adj.unit.app N) := inferInstance
    -- the target of the counit lies in the image of `Dσ_!`
    have hpb : IsPullback (𝟙 X) c.selfGraph c.i (pullback.fst c.g e) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Compactification.selfGraph_fst]⟩
    let T := (D((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙
      L((pullback.fst c.g e)^*[ModuleCat.{u + 1} Λ])).obj N
    have hε : IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ
        c.selfGraph).counit.app T) := by
      rw [NatTrans.isIso_app_iff_of_iso _
        ((derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hpb).app N).symm]
      dsimp only [Functor.comp_obj]
      have ht := (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ
        c.selfGraph).left_triangle_components (L((𝟙 X)^*[ModuleCat.{u + 1} Λ]).obj N)
      have : IsIso (D((c.selfGraph)_!open[ModuleCat.{u + 1} Λ]).map
          ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.selfGraph).unit.app
            (L((𝟙 X)^*[ModuleCat.{u + 1} Λ]).obj N)) ≫
          (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.selfGraph).counit.app
            _) := by
        rw [ht]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_left (D((c.selfGraph)_!open[ModuleCat.{u + 1} Λ]).map
        ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.selfGraph).unit.app
          (L((𝟙 X)^*[ModuleCat.{u + 1} Λ]).obj N))) _
    rw [compactificationEtaleUnit_app, compactificationEtaleGraphMap_app]
    simp only [clopenTransfer, Functor.map_comp]
    have : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (pullback.snd c.g e)).unit.app N ≫ R((pullback.snd c.g e)_*[ModuleCat.{u + 1} Λ]).map
          ((clopenUpperStarLowerShriekAdjunction Λ c.selfGraph).unit.app
            (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} Λ]).obj N))) := by
      simp only [adj, Adjunction.comp_unit_app] at h₁
      exact h₁
    simp only [← Category.assoc]
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  simp only [compactificationEtaleComparison, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.id_comp]
  have := hu N
  have : IsIso (derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) e).counit :=
    inferInstance
  have : IsIso (D(etaleLowerShriek (ModuleCat.{u + 1} Λ) e inferInstance).map
    ((compactificationEtaleUnit Λ e c).app N)) := Functor.map_isIso _ _
  have : IsIso ((derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) e).counit.app
    (Rf_!(c)[ModuleCat.{u + 1} Λ].obj N)) := NatIso.isIso_app_of_isIso _ _
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance (IsIso.id _))


/-- **The compactly supported direct image along an étale morphism is the extension by zero**:
for an étale `e` with a compactification `c`, the comparison `De_! ⟶ Rf_!(c)` is an
isomorphism. Isomorphisms are detected by the derived pullbacks to the geometric points of `Y`,
and the comparison commutes with base change
(`AlgebraicGeometry.Etale.compactificationEtaleComparison_baseChange`). Over a separably closed
field, `X` is covered by sections of `e`, which are open immersions over which `e` is an
isomorphism, and the comparison is local on `X`
(`AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison_of_cover`). -/
theorem isIso_compactificationEtaleComparison :
    IsIso (compactificationEtaleComparison Λ e c) := by
  -- over a separably closed field
  have hpt : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X₁ : Scheme.{u}}
      (e₁ : X₁ ⟶ Spec (.of Ω)) [_root_.AlgebraicGeometry.Etale e₁] (c₁ : Compactification e₁),
      IsIso (compactificationEtaleComparison Λ e₁ c₁) := by
    intro Ω _ _ X₁ e₁ _ c₁
    choose l hl hlx using fun x : X₁ ↦
      Scheme.exists_fac_of_etale_of_isSepClosed e₁ (𝟙 _) x (Subsingleton.elim _ _)
    have (x : X₁) : IsOpenImmersion (l x) :=
      IsOpenImmersion.of_section_of_etale e₁ (l x) (hl x)
    refine isIso_compactificationEtaleComparison_of_cover Λ e₁ c₁ l
      (fun x ↦ ⟨x, default, hlx x⟩) (fun x ↦ ?_)
    have : IsIso (l x ≫ e₁) := by
      rw [hl x]
      infer_instance
    exact isIso_compactificationEtaleComparison_of_isIso Λ (l x ≫ e₁) (c₁.restrictOpen (l x))
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  refine isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map Λ _ fun y ↦ ?_
  have sq := IsPullback.of_hasPullback e (Y.algClosurePoint y)
  have h := compactificationEtaleComparison_baseChange Λ sq c N
  have := hpt (pullback.snd e (Y.algClosurePoint y)) (c.ofIsPullback sq)
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite Λ sq c
  have h₂ : IsIso ((derivedEtaleLowerShriekBaseChangeIso _ sq).hom.app N ≫
      L((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ]).map
        ((compactificationEtaleComparison Λ e c).app N) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq c).app N) := by
    rw [h]
    infer_instance
  have h₃ := IsIso.of_isIso_comp_left ((derivedEtaleLowerShriekBaseChangeIso _ sq).hom.app N)
    (L((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ]).map
        ((compactificationEtaleComparison Λ e c).app N) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq c).app N)
  exact IsIso.of_isIso_comp_right _ ((rightDerivedLowerShriekOfCompactificationBaseChangeMap _
    sq c).app N)

end Iso

end Etale

end AlgebraicGeometry
