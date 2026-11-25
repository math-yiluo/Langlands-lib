/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaBaseChange
public import WeilConjectures.PoincareDuality.ProjectionFormulaCoherence
public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.ProperKunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence

/-!

# The left side of the base-change core of the source exchange

For a proper morphism `f`, the left side of the base-change core of the exceptional Künneth part
of the source exchange, transposed along `Lf^* ⊣ Rf_*`, is the compact-support base change
followed by the projection formula of `z` (`ProEtale.CondensedRing.sourceExchange_leftTranspose`).
The ingredient is the compatibility of the exceptional projection morphism with the
compact-support base change (`ProEtale.CondensedRing.exceptionalProjection_baseChange`,
blueprint `prop-sf-pf-coherence`), the componentwise form of
`ProEtale.CondensedRing.pfBaseChange_boundedConstructibleExceptionalProjection`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

section TransposeAbstract

/-- The abstract form of `sourceExchange_leftTranspose`: the projection morphisms commute with the
base change `ex`, and the unit parts agree. -/
lemma Adjunction.map_comp_counit_eq_of_projection_baseChange {𝒱 𝒲 𝒳 𝒴 : Type*} [Category 𝒱]
    [Category 𝒲] [Category 𝒳] [Category 𝒴] [MonoidalCategory 𝒱] [MonoidalCategory 𝒲]
    [MonoidalCategory 𝒳] [MonoidalCategory 𝒴] {fs : 𝒴 ⥤ 𝒳} [fs.Monoidal] {hs : 𝒱 ⥤ 𝒲}
    [hs.Monoidal] {Lπ : 𝒱 ⥤ 𝒴} {LzX : 𝒲 ⥤ 𝒳} {Sf : 𝒳 ⥤ 𝒴} (adjf : fs ⊣ Sf) {π₁s : 𝒴 ⥤ 𝒱}
    {zXs : 𝒳 ⥤ 𝒲} (pfπ : ∀ (T : 𝒱) (M : 𝒴), Lπ.obj T ⊗ M ⟶ Lπ.obj (T ⊗ π₁s.obj M))
    (pfz : ∀ (T : 𝒲) (M : 𝒳), LzX.obj T ⊗ M ⟶ LzX.obj (T ⊗ zXs.obj M))
    [∀ T M, IsIso (pfπ T M)] [∀ T M, IsIso (pfz T M)] (ex : Lπ ⋙ fs ⟶ hs ⋙ LzX)
    (Θ : ∀ M, hs.obj (π₁s.obj M) ⟶ zXs.obj (fs.obj M))
    (hnatl : ∀ {T T' : 𝒲} (t : T ⟶ T') (M : 𝒳),
      LzX.map t ▷ M ≫ pfz T' M = pfz T M ≫ LzX.map (t ▷ zXs.obj M))
    (hnatr : ∀ (T : 𝒲) {M M' : 𝒳} (y : M ⟶ M'),
      LzX.obj T ◁ y ≫ pfz T M' = pfz T M ≫ LzX.map (T ◁ zXs.map y))
    {A : 𝒱} {K : 𝒳} {A'' : 𝒲} {Q : 𝒴} {Q₁ Q₂ : 𝒳} [IsIso (ex.app A)]
    (hL0 : fs.map (pfπ A (Sf.obj K)) ≫ ex.app (A ⊗ π₁s.obj (Sf.obj K)) ≫
      LzX.map (Functor.OplaxMonoidal.δ hs A _ ≫ (hs.obj A ◁ Θ (Sf.obj K))) =
      Functor.OplaxMonoidal.δ fs (Lπ.obj A) (Sf.obj K) ≫ (ex.app A ▷ fs.obj (Sf.obj K)) ≫
        pfz (hs.obj A) (fs.obj (Sf.obj K)))
    (β : π₁s.obj (Sf.obj K) ⊗ A ⟶ A ⊗ π₁s.obj (Sf.obj K)) (c₁ : Lπ.obj A ⟶ Q)
    (c₂ : Q ⟶ 𝟙_ 𝒴) (u : hs.obj A ⟶ A'') (puc : hs.obj (π₁s.obj (Sf.obj K)) ⟶ zXs.obj K)
    (hpuc : puc = Θ (Sf.obj K) ≫ zXs.map (adjf.counit.app K))
    (c₁'' : LzX.obj A'' ⟶ Q₁) (c₂'' : Q₁ ⟶ Q₂) (c₃'' : Q₂ ⟶ 𝟙_ 𝒳)
    (hc : inv (ex.app A) ≫ fs.map c₁ ≫ fs.map c₂ ≫ (Functor.Monoidal.εIso fs).inv =
      LzX.map u ≫ c₁'' ≫ c₂'' ≫ c₃'') :
    fs.map (Lπ.map β ≫ inv (pfπ A (Sf.obj K)) ≫ (c₁ ▷ Sf.obj K) ≫ (c₂ ▷ Sf.obj K) ≫
        (λ_ _).hom) ≫ adjf.counit.app K =
      ex.app (π₁s.obj (Sf.obj K) ⊗ A) ≫
        LzX.map (hs.map β ≫ Functor.OplaxMonoidal.δ hs A (π₁s.obj (Sf.obj K)) ≫ (u ⊗ₘ puc)) ≫
        inv (pfz A'' K) ≫ (c₁'' ▷ K) ≫ (c₂'' ▷ K) ≫ (c₃'' ▷ K) ≫ (λ_ K).hom := by
  have hL0' : fs.map (inv (pfπ A (Sf.obj K))) = ex.app (A ⊗ π₁s.obj (Sf.obj K)) ≫
      LzX.map (Functor.OplaxMonoidal.δ hs A _ ≫ (hs.obj A ◁ Θ (Sf.obj K))) ≫
      inv (pfz (hs.obj A) (fs.obj (Sf.obj K))) ≫ (inv (ex.app A) ▷ fs.obj (Sf.obj K)) ≫
      Functor.LaxMonoidal.μ fs (Lπ.obj A) (Sf.obj K) := by
    rw [Functor.map_inv]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [reassoc_of% hL0]
    simp [← MonoidalCategory.comp_whiskerRight_assoc]
  have hex := ex.naturality β
  simp only [Functor.comp_map] at hex
  have hl : Functor.LaxMonoidal.μ fs (𝟙_ 𝒴) (Sf.obj K) ≫ fs.map (λ_ (Sf.obj K)).hom =
      ((Functor.Monoidal.εIso fs).inv ▷ _) ≫ (λ_ _).hom := by
    rw [Functor.LaxMonoidal.left_unitality fs (Sf.obj K)]
    simp [← MonoidalCategory.comp_whiskerRight_assoc]
  have hr := hnatr (hs.obj A) (adjf.counit.app K)
  simp only [Functor.id_obj, Functor.comp_obj] at hr
  have hr' : inv (pfz (hs.obj A) (fs.obj (Sf.obj K))) ≫ (LzX.obj (hs.obj A) ◁ adjf.counit.app K) =
      LzX.map (hs.obj A ◁ zXs.map (adjf.counit.app K)) ≫ inv (pfz (hs.obj A) K) := by
    rw [IsIso.inv_comp_eq, ← reassoc_of% hr, IsIso.hom_inv_id, Category.comp_id]
  have hl' : inv (pfz (hs.obj A) K) ≫ (LzX.map u ▷ K) =
      LzX.map (u ▷ zXs.obj K) ≫ inv (pfz A'' K) := by
    rw [IsIso.inv_comp_eq, ← reassoc_of% (hnatl u K), IsIso.hom_inv_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [hL0']
  simp only [Category.assoc]
  rw [reassoc_of% hex]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc, ← Functor.LaxMonoidal.μ_natural_left_assoc,
    reassoc_of% hl, ← MonoidalCategory.leftUnitor_naturality]
  have hw : (inv (ex.app A) ▷ fs.obj (Sf.obj K)) ≫ (fs.map c₁ ▷ fs.obj (Sf.obj K)) ≫
      (fs.map c₂ ▷ fs.obj (Sf.obj K)) ≫ ((Functor.Monoidal.εIso fs).inv ▷ _) ≫
      (𝟙_ 𝒳 ◁ adjf.counit.app K) =
      (LzX.obj (hs.obj A) ◁ adjf.counit.app K) ≫ (LzX.map u ▷ K) ≫ (c₁'' ▷ K) ≫ (c₂'' ▷ K) ≫
        (c₃'' ▷ K) := by
    have hcw : (inv (ex.app A) ▷ fs.obj (Sf.obj K)) ≫ (fs.map c₁ ▷ fs.obj (Sf.obj K)) ≫
        (fs.map c₂ ▷ fs.obj (Sf.obj K)) ≫ ((Functor.Monoidal.εIso fs).inv ▷ _) =
        ((LzX.map u ≫ c₁'' ≫ c₂'' ≫ c₃'') ▷ fs.obj (Sf.obj K)) := by
      rw [← hc]
      simp only [MonoidalCategory.comp_whiskerRight]
    rw [reassoc_of% hcw, ← MonoidalCategory.whisker_exchange]
    simp only [MonoidalCategory.comp_whiskerRight]
    rfl
  rw [reassoc_of% hw, reassoc_of% hr', reassoc_of% hl', hpuc, MonoidalCategory.tensorHom_def']
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rfl

/-- The abstract form of the unit part of `sourceExchange_leftTranspose`: the inverse base
changes of a horizontally pasted rectangle, read through the unit comparisons. -/
lemma inv_app_comp_map_comp_eq_of_paste {𝒮 𝒴 𝒱 𝒳 𝒲 : Type*} [Category 𝒮] [Category 𝒴]
    [Category 𝒱] [Category 𝒳] [Category 𝒲] {aYs : 𝒮 ⥤ 𝒴} {fs : 𝒴 ⥤ 𝒳} {faYs : 𝒮 ⥤ 𝒳}
    {π₂s : 𝒴 ⥤ 𝒱} {hs : 𝒱 ⥤ 𝒲} {hπ₂s : 𝒴 ⥤ 𝒲} {LaY : 𝒴 ⥤ 𝒮} {Lπ : 𝒱 ⥤ 𝒴} {LzX : 𝒲 ⥤ 𝒳}
    (exY : LaY ⋙ aYs ⟶ π₂s ⋙ Lπ) (exA : Lπ ⋙ fs ⟶ hs ⋙ LzX) (exP : LaY ⋙ faYs ⟶ hπ₂s ⋙ LzX)
    [IsIso exY] [IsIso exA] [IsIso exP] (ucf : faYs ≅ aYs ⋙ fs) (uch : hπ₂s ≅ π₂s ⋙ hs)
    (hpaste : ∀ X, exP.app X = ucf.hom.app (LaY.obj X) ≫ fs.map (exY.app X) ≫
      exA.app (π₂s.obj X) ≫ LzX.map (uch.inv.app X))
    {oP : 𝒮} {oY : 𝒴} {oX : 𝒳} (eaY : aYs.obj oP ⟶ oY) (ef : fs.obj oY ⟶ oX)
    (efaY : faYs.obj oP ⟶ oX) (hunit : ucf.hom.app oP ≫ fs.map eaY ≫ ef = efaY)
    {M N' : 𝒴} (ρ : M ⟶ N') (κ : LaY.obj N' ⟶ oP) :
    inv (exA.app (π₂s.obj M)) ≫ fs.map ((inv exY).app M ≫ aYs.map (LaY.map ρ ≫ κ)) ≫
        fs.map eaY ≫ ef =
      LzX.map (uch.inv.app M ≫ hπ₂s.map ρ) ≫ (inv exP).app N' ≫ faYs.map κ ≫ efaY := by
  have hP : (inv exP).app N' = LzX.map (uch.hom.app N') ≫ (inv exA).app (π₂s.obj N') ≫
      fs.map ((inv exY).app N') ≫ ucf.inv.app (LaY.obj N') := by
    rw [NatIso.isIso_inv_app]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hpaste]
    simp [← Functor.map_comp_assoc]
  have h1 := congrArg fs.map ((inv exY).naturality ρ)
  have h2 := (inv exA).naturality (π₂s.map ρ)
  have h3 := congrArg LzX.map (uch.hom.naturality ρ)
  have h4 := ucf.hom.naturality κ
  have h5 : LzX.map (uch.inv.app M) ≫ LzX.map (uch.hom.app M) = 𝟙 _ := by
    rw [← LzX.map_comp, Iso.inv_hom_id_app, LzX.map_id]
  simp only [Functor.comp_map, Functor.map_comp] at h1 h2 h3 h4
  rw [← hunit, hP, NatIso.isIso_inv_app exA]
  simp only [Functor.map_comp, Category.assoc, ← NatIso.isIso_inv_app]
  rw [reassoc_of% h4, Iso.inv_hom_id_app_assoc, reassoc_of% h3, reassoc_of% h5, reassoc_of% h2,
    reassoc_of% h1]

end TransposeAbstract

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The exceptional projection morphism commutes with the compact-support base change**
(blueprint `prop-sf-pf-coherence`, compatibility with base change): for a cartesian square
`g' ≫ f = f' ≫ g`, the square
```
Lg^*(Rf_!T ⊗ M) ──Lg^* PF──▶ Lg^*Rf_!(T ⊗ Lf^*M) ──Ex_!──▶ Rf'_!Lg'^*(T ⊗ Lf^*M)
       │                                                          │
       ▼                                                          ▼
Lg^*Rf_!T ⊗ Lg^*M ──Ex_! ⊗ 1──▶ Rf'_!Lg'^*T ⊗ Lg^*M ──PF──▶ Rf'_!(Lg'^*T ⊗ Lf'^*Lg^*M)
```
commutes, where the vertical arrows are the tensor comparisons of the derived pullbacks, the
right one followed by `Lg'^*Lf^* ≅ Lf'^*Lg^*`. -/
theorem exceptionalProjection_baseChange (sq : IsPullback g' f' f g)
    (T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ g).map
        (((boundedConstructibleExceptionalProjection ℓ f).app T).app M) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
        (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj M) ≫
      (boundedConstructibleLowerShriek ℓ f').map
        (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ g') T
            ((boundedConstructibleUpperStar _ ℓ f).obj M) ≫
          ((boundedConstructibleUpperStar _ ℓ g').obj T ◁
            ((boundedConstructibleUpperStarComp _ ℓ g' f).inv.app M ≫
              eqToHom (by rw [sq.w]) ≫ (boundedConstructibleUpperStarComp _ ℓ f' g).hom.app M))) =
    Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ g)
        ((boundedConstructibleLowerShriek ℓ f).obj T) M ≫
      ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app T ▷
        (boundedConstructibleUpperStar _ ℓ g).obj M) ≫
      ((boundedConstructibleExceptionalProjection ℓ f').app
        ((boundedConstructibleUpperStar _ ℓ g').obj T)).app
        ((boundedConstructibleUpperStar _ ℓ g).obj M) := by
  have h := pfBaseChange_boundedConstructibleExceptionalProjection ℓ sq T M
  rw [boundedConstructibleExceptionalProjection_app_app,
    boundedConstructibleExceptionalProjection_app_app,
    boundedConstructiblePullbackSquareComparison_inv_app] at h
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp] at h ⊢
  exact h

end BaseChange

section Transpose

variable {P X Y W V : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  (aY : Y ⟶ P) (f : X ⟶ Y) [IsProper f.left] (π₁ π₂ : V ⟶ Y)
  (zX : W ⟶ X) (h : W ⟶ V) (hA : IsPullback h zX π₁ f)
  (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- The left side of the base-change core, transposed along `Lf^* ⊣ Rf_*`. -/
theorem sourceExchange_leftTranspose (sqY : IsPullback π₂ π₁ aY aY)
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY)]
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (hA.paste_horiz sqY))] :
    (boundedConstructibleUpperStar _ ℓ f).map
        ((boundedConstructibleLowerShriek ℓ π₁).map (β_ _ _).hom ≫
          inv (((boundedConstructibleExceptionalProjection ℓ π₁).app
            ((boundedConstructibleUpperStar _ ℓ π₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj
                ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))).app
            ((boundedConstructibleLowerStar ℓ f).obj K)) ≫
          (((inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY)).app
              ((boundedConstructibleLowerStar ℓ f).obj
                ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ≫
            (boundedConstructibleUpperStar _ ℓ aY).map
              ((boundedConstructibleLowerShriek ℓ aY).map
                  ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
                    ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ≫
                (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f aY).inv.app
                  ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)) ≫
                (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ aY)).counit.app (𝟙_ _))) ▷
            (boundedConstructibleLowerStar ℓ f).obj K) ≫
          ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ aY)).inv ▷ _) ≫
          (λ_ _).hom) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K =
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hA).app _ ≫
      (boundedConstructibleLowerShriek ℓ zX).map
        ((boundedConstructibleUpperStar _ ℓ h).map
          (β_ ((boundedConstructibleUpperStar _ ℓ π₁).obj
              ((boundedConstructibleLowerStar ℓ f).obj K))
            ((boundedConstructibleUpperStar _ ℓ π₂).obj ((boundedConstructibleLowerStar ℓ f).obj
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))).hom ≫
        Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ h) _ _ ≫
        (((boundedConstructibleUpperStarComp _ ℓ h π₂).inv.app
            ((boundedConstructibleLowerStar ℓ f).obj
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ≫
          (boundedConstructibleUpperStar _ ℓ (h ≫ π₂)).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))) ⊗ₘ
          prodUpperStarCounit ℓ hA.w K)) ≫
      inv (((boundedConstructibleExceptionalProjection ℓ zX).app
        ((boundedConstructibleUpperStar _ ℓ (h ≫ π₂)).obj
          ((boundedConstructibleLowerShriek ℓ f).obj
          ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))).app K) ≫
      ((inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (hA.paste_horiz sqY))).app
          ((boundedConstructibleLowerShriek ℓ f).obj
            ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ▷ K) ≫
      ((boundedConstructibleUpperStar _ ℓ (f ≫ aY)).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f aY).inv.app
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)) ≫
            (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ aY)).counit.app (𝟙_ _)) ▷ K) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (f ≫ aY))).inv ▷ K) ≫
      (λ_ K).hom :=
  by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hA
  exact Adjunction.map_comp_counit_eq_of_projection_baseChange
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (fun T M ↦ ((boundedConstructibleExceptionalProjection ℓ π₁).app T).app M)
    (fun T M ↦ ((boundedConstructibleExceptionalProjection ℓ zX).app T).app M)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hA)
    (fun M ↦ (boundedConstructibleUpperStarComp _ ℓ h π₁).inv.app M ≫
      eqToHom (by rw [hA.w]) ≫ (boundedConstructibleUpperStarComp _ ℓ zX f).hom.app M)
    (fun t M ↦ boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ zX t M)
    (fun T _ _ y ↦ boundedConstructibleExceptionalProjectionMorphism_natural_right ℓ zX T y)
    (exceptionalProjection_baseChange ℓ hA _ _) _ _ _ _ _
    (by unfold prodUpperStarCounit; simp only [Category.assoc]) _ _ _
    (inv_app_comp_map_comp_eq_of_paste
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY)
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hA)
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (hA.paste_horiz sqY))
      (boundedConstructibleUpperStarComp _ ℓ f aY) (boundedConstructibleUpperStarComp _ ℓ h π₂)
      (fun X ↦ boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ hA sqY X)
      _ _ _ (boundedConstructibleUpperStarComp_hom_app_unit ℓ f aY) _ _)

end Transpose

end AlgebraicGeometry.ProEtale.CondensedRing
