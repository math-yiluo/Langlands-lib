/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnit
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeLowerStar

/-!
# Coefficient comparisons and the compact-support exchange map

We reduce the compatibility of the coefficient comparison
`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerShriekIso` with the
compact-support exchange map `AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`
to the compatibility of each of its building blocks, through the abstract predicate
`AlgebraicGeometry.Etale.CoeffCompatible` and its stability under composition, whiskering and
inversion, and proves the building blocks (A), (B), (C). The file then deduces the
coefficient-change statements used by `AlgebraicGeometry.Etale.AdicSystem`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Abstract

variable {A A' B B' C C' D D' : Type*} [Category A] [Category A'] [Category B] [Category B']
  [Category C] [Category C'] [Category D] [Category D'] {RA : A' ⥤ A} {RB : B' ⥤ B}
  {RC : C' ⥤ C} {RD : D' ⥤ D}

/-- Two natural transformations `α : F ⟶ G` and `α' : F' ⟶ G'` are compatible with the
coefficient comparisons `ιF : RB ⋙ F ≅ F' ⋙ RA` and `ιG : RB ⋙ G ≅ G' ⋙ RA`. -/
def CoeffCompatible {F G : B ⥤ A} {F' G' : B' ⥤ A'} (ιF : RB ⋙ F ≅ F' ⋙ RA)
    (ιG : RB ⋙ G ≅ G' ⋙ RA) (α : F ⟶ G) (α' : F' ⟶ G') : Prop :=
  ∀ K, ιF.hom.app K ≫ RA.map (α'.app K) = α.app (RB.obj K) ≫ ιG.hom.app K

namespace CoeffCompatible

variable {F G H : B ⥤ A} {F' G' H' : B' ⥤ A'} {ιF : RB ⋙ F ≅ F' ⋙ RA}
  {ιG : RB ⋙ G ≅ G' ⋙ RA} {ιH : RB ⋙ H ≅ H' ⋙ RA}

lemma comp {α : F ⟶ G} {α' : F' ⟶ G'} {β : G ⟶ H} {β' : G' ⟶ H'}
    (h₁ : CoeffCompatible ιF ιG α α') (h₂ : CoeffCompatible ιG ιH β β') :
    CoeffCompatible ιF ιH (α ≫ β) (α' ≫ β') := by
  intro K
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp, reassoc_of% (h₁ K), h₂ K,
    Category.assoc]

lemma inv {e : F ≅ G} {e' : F' ≅ G'} (h : CoeffCompatible ιF ιG e.hom e'.hom) :
    CoeffCompatible ιG ιF e.inv e'.inv := by
  intro K
  rw [← cancel_epi (e.hom.app (RB.obj K)), ← reassoc_of% (h K)]
  simp [← Functor.map_comp]

lemma whiskerLeft {E : C ⥤ B} {E' : C' ⥤ B'} (ιE : RC ⋙ E ≅ E' ⋙ RB) {α : F ⟶ G}
    {α' : F' ⟶ G'} (h : CoeffCompatible ιF ιG α α') :
    CoeffCompatible (pasteTwoSquaresIso ιE ιF) (pasteTwoSquaresIso ιE ιG)
      (Functor.whiskerLeft E α) (Functor.whiskerLeft E' α') := by
  intro K
  simp only [pasteTwoSquaresIso_hom_app, Functor.whiskerLeft_app, Category.assoc, h (E'.obj K)]
  exact α.naturality_assoc _ _

lemma whiskerRight {E : A ⥤ D} {E' : A' ⥤ D'} (ιE : RA ⋙ E ≅ E' ⋙ RD) {α : F ⟶ G}
    {α' : F' ⟶ G'} (h : CoeffCompatible ιF ιG α α') :
    CoeffCompatible (pasteTwoSquaresIso ιF ιE) (pasteTwoSquaresIso ιG ιE)
      (Functor.whiskerRight α E) (Functor.whiskerRight α' E') := by
  intro K
  have := ιE.hom.naturality (α'.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at this
  simp only [pasteTwoSquaresIso_hom_app, Functor.whiskerRight_app, Category.assoc, ← this,
    ← Functor.map_comp_assoc]
  rw [h K]

lemma associator_hom {F₁ : C ⥤ B} {F₂ : B ⥤ A} {F₃ : A ⥤ D} {F₁' : C' ⥤ B'} {F₂' : B' ⥤ A'}
    {F₃' : A' ⥤ D'} (ι₁ : RC ⋙ F₁ ≅ F₁' ⋙ RB) (ι₂ : RB ⋙ F₂ ≅ F₂' ⋙ RA)
    (ι₃ : RA ⋙ F₃ ≅ F₃' ⋙ RD) :
    CoeffCompatible (pasteTwoSquaresIso (pasteTwoSquaresIso ι₁ ι₂) ι₃)
      (pasteTwoSquaresIso ι₁ (pasteTwoSquaresIso ι₂ ι₃))
      (Functor.associator F₁ F₂ F₃).hom (Functor.associator F₁' F₂' F₃').hom := by
  intro K
  simp [pasteTwoSquaresIso_hom_app]

lemma associator_inv {F₁ : C ⥤ B} {F₂ : B ⥤ A} {F₃ : A ⥤ D} {F₁' : C' ⥤ B'} {F₂' : B' ⥤ A'}
    {F₃' : A' ⥤ D'} (ι₁ : RC ⋙ F₁ ≅ F₁' ⋙ RB) (ι₂ : RB ⋙ F₂ ≅ F₂' ⋙ RA)
    (ι₃ : RA ⋙ F₃ ≅ F₃' ⋙ RD) :
    CoeffCompatible (pasteTwoSquaresIso ι₁ (pasteTwoSquaresIso ι₂ ι₃))
      (pasteTwoSquaresIso (pasteTwoSquaresIso ι₁ ι₂) ι₃)
      (Functor.associator F₁ F₂ F₃).inv (Functor.associator F₁' F₂' F₃').inv := by
  intro K
  simp [pasteTwoSquaresIso_hom_app]

end CoeffCompatible

end Abstract

section DerivedLift

open _root_.CategoryTheory.Functor

variable {X X' Y Y' Z Z' : Type*} [Category X] [Category X'] [Category Y] [Category Y']
  [Category Z] [Category Z']

/-- The coefficient comparison `ι` conjugated by isomorphisms `φ : G ≅ F` and `φ' : G' ≅ F'` is
compatible with `φ` and `φ'`. -/
lemma CoeffCompatible.of_conj {rX : X' ⥤ X} {rY : Y' ⥤ Y} {F G : X ⥤ Y} {F' G' : X' ⥤ Y'}
    (ι : rX ⋙ F ≅ F' ⋙ rY) (φ : G ≅ F) (φ' : G' ≅ F') :
    CoeffCompatible (isoWhiskerLeft rX φ ≪≫ ι ≪≫ isoWhiskerRight φ'.symm rY) ι φ.hom φ'.hom := by
  intro K
  simp [← Functor.map_comp]

variable [Abelian X] [Abelian X'] [Abelian Y] [Abelian Y'] [Abelian Z] [Abelian Z']
  [HasDerivedCategory X] [HasDerivedCategory X'] [HasDerivedCategory Y] [HasDerivedCategory Y']
  [HasDerivedCategory Z] [HasDerivedCategory Z']
  {rX : X' ⥤ X} {rY : Y' ⥤ Y} {rZ : Z' ⥤ Z}
  [rX.Additive] [PreservesFiniteLimits rX] [PreservesFiniteColimits rX]
  [rY.Additive] [PreservesFiniteLimits rY] [PreservesFiniteColimits rY]
  [rZ.Additive] [PreservesFiniteLimits rZ] [PreservesFiniteColimits rZ]

/-- Compatibility with coefficient comparisons passes to the isomorphisms induced on derived
categories by exact functors. -/
lemma CoeffCompatible.mapDerivedCategoryNatIso {P Q : X ⥤ Y} {P' Q' : X' ⥤ Y'}
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [P'.Additive] [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
    [Q'.Additive] [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
    {α : rX ⋙ P ≅ P' ⋙ rY} {γ : rX ⋙ Q ≅ Q' ⋙ rY} {β : P ≅ Q} {β' : P' ≅ Q'}
    (h : CoeffCompatible α γ β.hom β'.hom) :
    CoeffCompatible (mapDerivedCategorySquareIso α) (mapDerivedCategorySquareIso γ)
      (Functor.mapDerivedCategoryNatIso β).hom (Functor.mapDerivedCategoryNatIso β').hom := by
  have hiso : α ≪≫ isoWhiskerRight β' rY = isoWhiskerLeft rX β ≪≫ γ := by
    ext K
    simpa using h K
  have hm : (Functor.mapDerivedCategoryNatIso α).hom ≫
      (Functor.mapDerivedCategoryNatIso (isoWhiskerRight β' rY)).hom =
      (Functor.mapDerivedCategoryNatIso (isoWhiskerLeft rX β)).hom ≫
        (Functor.mapDerivedCategoryNatIso γ).hom := by
    rw [← mapDerivedCategoryNatIso_trans, ← mapDerivedCategoryNatIso_trans, hiso]
  have hR := mapDerivedCategoryNatIso_isoWhiskerRight β' rY
  have hL := mapDerivedCategoryNatIso_isoWhiskerLeft rX β
  have H : (mapDerivedCategorySquareIso α).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso β').hom rY.mapDerivedCategory =
      Functor.whiskerLeft rX.mapDerivedCategory (Functor.mapDerivedCategoryNatIso β).hom ≫
        (mapDerivedCategorySquareIso γ).hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hR, reassoc_of% hm]
    rw [← cancel_epi (mapDerivedCategoryCompIso rX P).inv, Iso.inv_hom_id_assoc,
      ← reassoc_of% hL, Iso.inv_hom_id_assoc]
  intro K
  simpa using NatTrans.congr_app H K

/-- The isomorphism induced on derived categories by a pasted square is the pasting of the
induced isomorphisms, up to the composition isomorphisms. -/
lemma CoeffCompatible.mapDerivedCategoryCompIso {F₁ : X ⥤ Y} {F₂ : Y ⥤ Z} {F₁' : X' ⥤ Y'}
    {F₂' : Y' ⥤ Z'}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₁'.Additive] [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
    [F₂'.Additive] [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']
    (ι₁ : rX ⋙ F₁ ≅ F₁' ⋙ rY) (ι₂ : rY ⋙ F₂ ≅ F₂' ⋙ rZ) :
    CoeffCompatible (mapDerivedCategorySquareIso (pasteTwoSquaresIso ι₁ ι₂))
      (pasteTwoSquaresIso (mapDerivedCategorySquareIso ι₁) (mapDerivedCategorySquareIso ι₂))
      (Functor.mapDerivedCategoryCompIso F₁ F₂).inv
      (Functor.mapDerivedCategoryCompIso F₁' F₂').inv := by
  intro K
  have := mapDerivedCategorySquareIso_hom_app_comp ι₁ ι₂ (pasteTwoSquaresIso ι₁ ι₂)
    (Iso.refl _) (Iso.refl _) (by simp [pasteTwoSquaresIso_hom_app]) K
  simp only [mapDerivedCategoryTriangleIso, Iso.trans_hom, NatTrans.comp_app,
    mapDerivedCategoryNatIso_refl, Category.id_comp] at this
  rw [pasteTwoSquaresIso_hom_app]
  exact this

end DerivedLift

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- The derived extension by zero along an open immersion carries derived base changes to
derived base changes: if `η : K ⟶ Res K'` exhibits `K'` as `K ⊗ᴸ_Λ Λ'`, then `Dj_! η` followed
by the comparison `Dj_! Res ≅ Res Dj_!` exhibits `Dj_! K'` as `Dj_! K ⊗ᴸ_Λ Λ'`. The extension by
zero is left adjoint to the exact restriction `j^*`, which commutes with restriction of
scalars. -/
lemma isDerivedBaseChange_openImmersionLowerShriek_map_comp {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    {K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars U.smallEtaleTopology ρ).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Sheaf.IsDerivedBaseChange (D((j)_!open[ModuleCat.{u + 1} Λ]).map η ≫
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j).hom.app K') := by
  have (Γ : Type (u + 1)) [CommRing Γ] :
      (openImmersionRestriction (ModuleCat.{u + 1} Γ) j).IsLeftAdjoint :=
    (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Γ) j).isLeftAdjoint
  let adj (Γ : Type (u + 1)) [CommRing Γ] :=
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Γ) j).mapDerivedCategoryAdjunction
  have hβ := Adjunction.mapDerivedCategoryAdjunction_mate
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ') j)
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j)
      (Iso.refl _) (openImmersionLowerShriekRestrictScalarsIso ρ j)
      (fun G ↦ (openImmersionLowerShriekAdjunction_unit_app_comp_openImmersionRestrictionMap
        ρ j G).trans (Category.comp_id _).symm)
  exact fun N ↦ Adjunction.bijective_comp_map_of_unit_comp_map (adj Λ') (adj Λ) _ _ hβ η hη N

section Compactification

variable [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y} [CompactSpace Y]

/-- The coefficient comparison `Res ∘ Rf_!(c) ≅ Rf_!(c) ∘ Res` for an arbitrary
compactification `c` over a quasi-compact base. -/
noncomputable def compactificationRestrictScalarsIso (c : Compactification f) :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ ⋙ Rf_!(c)[ModuleCat.{u + 1} Λ] ≅
      Rf_!(c)[ModuleCat.{u + 1} Λ'] ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ :=
  have := c.isProper
  have := c.isOpenImmersion
  have hd := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite c.g
  pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ c.i)
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ c.g hd.choose hd.choose_spec)

lemma derivedRestrictScalarsCompRightDerivedLowerShriekIso_eq (f : X ⟶ Y)
    [HasCompactification f] :
    derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f =
      compactificationRestrictScalarsIso ρ (HasCompactification.compactification f) :=
  rfl

/-- The derived lower shriek along a compactification carries derived base changes to derived
base changes, through the coefficient comparison
`AlgebraicGeometry.Etale.compactificationRestrictScalarsIso`: so do the extension by zero
(`AlgebraicGeometry.Etale.isDerivedBaseChange_openImmersionLowerShriek_map_comp`) and the proper
direct image (`AlgebraicGeometry.Etale.isDerivedBaseChange_rightDerivedLowerStar_map_comp`). -/
lemma isDerivedBaseChange_rightDerivedLowerShriekOfCompactification_map_comp
    (c : Compactification f)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Sheaf.IsDerivedBaseChange ((Rf_!(c)[ModuleCat.{u + 1} Λ]).map η ≫
      (compactificationRestrictScalarsIso ρ c).hom.app K') := by
  have := c.isProper
  have := c.isOpenImmersion
  rw [compactificationRestrictScalarsIso, pasteTwoSquaresIso_hom_app, Functor.comp_map,
    ← Functor.map_comp_assoc]
  exact isDerivedBaseChange_rightDerivedLowerStar_map_comp ρ c.g _ _
    (isDerivedBaseChange_openImmersionLowerShriek_map_comp ρ c.i hη)

end Compactification

section Exchange

variable [Finite Λ]

omit [Finite Λ] in
/-- **(A)**
The derived base change map `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` is compatible with the
coefficient comparisons of `Rf_*`, `Rf'_*`, `Lg^*` and `Lg'^*`. -/
lemma coeffCompatible_derivedBaseChangeMap {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) (d d' : ℕ)
    (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (hd' : ∀ (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d' < q →
      IsZero ((((f')_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    CoeffCompatible
      (pasteTwoSquaresIso (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f d hd)
        (leftDerivedUpperStarRestrictScalarsIso ρ g))
      (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f' d' hd'))
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq)
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ') sq) :=
  fun K ↦ derivedBaseChangeMap_app_restrictScalars ρ sq d d' hd hd' K

omit [Finite Λ] in
/-- **(B)**
The base change isomorphism `Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*` of the extension by
zero is compatible with the coefficient comparisons. -/
lemma coeffCompatible_derivedOpenImmersionLowerShriekBaseChangeIso {U' U X' X : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g'' : X' ⟶ X} [IsOpenImmersion j]
    [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'') :
    CoeffCompatible
      (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j'))
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
        (leftDerivedUpperStarRestrictScalarsIso ρ g''))
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).hom
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ') hsq).hom :=
  fun K ↦ derivedOpenImmersionLowerShriekBaseChangeIso_hom_app_restrictScalars ρ hsq K

variable [Finite Λ'] {X Y : Scheme.{u}} {f : X ⟶ Y} [CompactSpace Y]

omit [Finite Λ'] in
/-- **(C)**
The comparison of derived lower shrieks along a refinement of compactifications is
compatible with the coefficient comparisons. -/
lemma coeffCompatible_rightDerivedLowerShriekOfCompactificationComparison
    {c d : Compactification f} (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    CoeffCompatible (compactificationRestrictScalarsIso ρ d)
      (compactificationRestrictScalarsIso ρ c)
      (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ) r hcart)
      (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ') r hcart) :=
  fun K ↦ rightDerivedLowerShriekOfCompactificationComparison_app_restrictScalars ρ r hcart
    _ _ _ _ K

/-- The isomorphism between the derived lower shrieks of two compactifications is compatible
with the coefficient comparisons. -/
lemma coeffCompatible_rightDerivedLowerShriekOfCompactificationIso [QuasiCompact f]
    (c d : Compactification f) :
    CoeffCompatible (compactificationRestrictScalarsIso ρ c)
      (compactificationRestrictScalarsIso ρ d)
      (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom
      (rightDerivedLowerShriekOfCompactificationIso Λ' c d).hom :=
  (coeffCompatible_rightDerivedLowerShriekOfCompactificationComparison ρ _ _).comp
    (CoeffCompatible.inv (e := asIso _) (e' := asIso _)
      (coeffCompatible_rightDerivedLowerShriekOfCompactificationComparison ρ _ _))

end Exchange

section BaseChangeMap

variable [Finite Λ] [Finite Λ'] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} [CompactSpace Y] [CompactSpace Y']

omit [Finite Λ'] in
/-- The compactly supported base change map along a compactification is compatible with the
coefficient comparisons, by (A) and (B). -/
lemma coeffCompatible_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    CoeffCompatible
      (pasteTwoSquaresIso (compactificationRestrictScalarsIso ρ c)
        (leftDerivedUpperStarRestrictScalarsIso ρ g))
      (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (compactificationRestrictScalarsIso ρ (c.ofIsPullback sq)))
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c)
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ') sq c) := by
  have := c.isProper
  have := c.isOpenImmersion
  have := (c.ofIsPullback sq).isProper
  have := (c.ofIsPullback sq).isOpenImmersion
  exact (CoeffCompatible.associator_hom _ _ _).comp
    ((CoeffCompatible.whiskerLeft _
      (coeffCompatible_derivedBaseChangeMap ρ _ _ _ _ _)).comp
    ((CoeffCompatible.associator_inv _ _ _).comp
    ((CoeffCompatible.whiskerRight _ (CoeffCompatible.inv
      (coeffCompatible_derivedOpenImmersionLowerShriekBaseChangeIso ρ
        (c.isPullback_i_ofIsPullback sq)))).comp
    (CoeffCompatible.associator_hom _ _ _))))

/-- The compact-support exchange map is compatible with the coefficient comparisons. -/
lemma coeffCompatible_rightDerivedLowerShriekBaseChangeMap [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    CoeffCompatible
      (pasteTwoSquaresIso (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f)
        (leftDerivedUpperStarRestrictScalarsIso ρ g))
      (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f'))
      (rightDerivedLowerShriekBaseChangeMap Λ sq) (rightDerivedLowerShriekBaseChangeMap Λ' sq) :=
  (coeffCompatible_rightDerivedLowerShriekOfCompactificationBaseChangeMap ρ sq _).comp
    (CoeffCompatible.whiskerLeft _ (coeffCompatible_rightDerivedLowerShriekOfCompactificationIso
      ρ _ (HasCompactification.compactification f')))

end BaseChangeMap

variable [Finite Λ] [Finite Λ'] {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) [HasCompactification aX]

omit [IsSepClosed k] in
/-- The coefficient comparison of `Ra_!` is compatible with the compact-support exchange map
along an automorphism pair `(g, h)`. -/
lemma derivedRestrictScalarsCompRightDerivedLowerShriekIso_baseChangeMap [QuasiCompact aX]
    {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)} (sq : IsPullback g aX aX h)
    (K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (L((h)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ aX).hom.app K') ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ h).hom.app
        ((R(aX)_![ModuleCat.{u + 1} Λ']).obj K') ≫
      (Sheaf.derivedRestrictScalars _ ρ).map
        ((rightDerivedLowerShriekBaseChangeMap Λ' sq).app K') =
    (rightDerivedLowerShriekBaseChangeMap Λ sq).app
        ((Sheaf.derivedRestrictScalars _ ρ).obj K') ≫
      (R(aX)_![ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app K') ≫
      (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ aX).hom.app
        ((L((g)^*[ModuleCat.{u + 1} Λ'])).obj K') := by
  simpa [pasteTwoSquaresIso_hom_app] using
    coeffCompatible_rightDerivedLowerShriekBaseChangeMap ρ sq K'


omit [IsSepClosed k] in
/-- The components of the compact-support base change `AlgebraicGeometry.Etale.compactPullback`. -/
lemma compactPullback_app {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)} [QuasiCompact aX]
    (sq : IsPullback g aX aX h) [IsIso h]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactPullback Λ sq).app K =
      (globalSectionsTransport Λ h).hom.app ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
          ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) := by
  simp [compactPullback]

/-- The coefficient comparison of compact cohomology is compatible with the compact-support base
change along every automorphism pair. -/
lemma isCompactPullbackCompatible_compactlySupportedGlobalSectionsRestrictScalarsIso
    [QuasiCompact aX] {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)}
    (sq : IsPullback g aX aX h) [IsIso h] :
    IsCompactPullbackCompatible ρ (compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX) sq := by
  intro K'
  rw [compactPullback_app, compactPullback_app]
  exact pasteTwoSquaresIso_hom_app_comp_map_of_comm
    (α₁ := derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ aX)
    (α₂ := derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ)
    (εg := leftDerivedUpperStarRestrictScalarsIso ρ g)
    (εh := leftDerivedUpperStarRestrictScalarsIso ρ h)
    (Ex := rightDerivedLowerShriekBaseChangeMap Λ sq)
    (Ex' := rightDerivedLowerShriekBaseChangeMap Λ' sq)
    (T := (globalSectionsTransport Λ h).hom) (T' := (globalSectionsTransport Λ' h).hom)
    (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso_hom_app_globalSectionsTransport ρ h)
    (derivedRestrictScalarsCompRightDerivedLowerShriekIso_baseChangeMap ρ aX sq) K'

-- The proof uses neither the surjectivity of `ρ` nor the finiteness of `Λ'`.
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- Blueprint `lemma-sp-reduction--1` (subsection
`sk-def-sfb-coefficient-comparisons`): for a surjection `ρ : Λ →+* Λ'` of finite rings whose
exponent is invertible on the separably closed field `k` and a separated finite-type
`a_X : X ⟶ Spec k`, the canonical coefficient comparison
`RΓ_c(X, K) ⊗ᴸ_Λ Λ' ⟶ RΓ_c(X, K ⊗ᴸ_Λ Λ')`
(`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsRestrictScalarsIso`) is an
isomorphism for every `K ∈ Dᵇctf(X, Λ)`. -/
theorem isCoefficientChange_compactlySupportedGlobalSectionsRestrictScalarsIso [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent Λ (Spec (.of k))]
    (hρ : Function.Surjective ρ) :
    IsCoefficientChange ρ (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX)
      (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ') aX)
      (compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX) := by
  intro K K' η _ hη
  unfold compactlySupportedGlobalSections
  rw [compactlySupportedGlobalSectionsRestrictScalarsIso, pasteTwoSquaresIso_hom_app,
    Functor.comp_map, ← Functor.map_comp_assoc,
    derivedRestrictScalarsCompRightDerivedLowerShriekIso_eq]
  exact isDerivedBaseChange_rightDerivedGlobalSections_map_comp ρ
    (isDerivedBaseChange_rightDerivedLowerShriekOfCompactification_map_comp ρ _ hη)

variable [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]


/-- Blueprint `lemma-sp-reduction--1` (subsection
`sk-def-sfb-coefficient-comparisons`):
compact cohomology commutes with finite-level coefficient reduction, compatibly with pullback.
For a surjection `ρ : Λ →+* Λ'` of finite coefficient rings whose exponent is invertible on the
separably closed field `k` and a separated finite-type `a_X : X ⟶ Spec k`, compact cohomology
commutes with restriction of scalars along `ρ` through a coefficient comparison `α` for which
`RΓ_c(X, K) ⊗ᴸ_Λ Λ' ⟶ RΓ_c(X, K ⊗ᴸ_Λ Λ')` is an isomorphism for every `K ∈ Dᵇctf(X, Λ)`, and `α`
is compatible with the compact-support base change along every pair of automorphisms
(`AlgebraicGeometry.Etale.IsCompactPullbackCompatible`). -/
theorem exists_isCoefficientChange_compactlySupportedGlobalSections
    [HasInvertibleExponent Λ (Spec (.of k))] (hρ : Function.Surjective ρ) :
    ∃ α, IsCoefficientChange ρ (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX)
        (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ') aX) α ∧
      ∀ (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (sq : IsPullback g aX aX h) [IsIso h],
        IsCompactPullbackCompatible ρ α sq :=
  ⟨compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX,
    isCoefficientChange_compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX hρ,
    fun _ _ sq _ ↦
      isCompactPullbackCompatible_compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX sq⟩

/-- Blueprint `theorem-grothendieck-lefschetz-trace-formula--7` (subsection
`theorem-grothendieck-lefschetz-trace-formula--7`), the pullback isomorphism at a geometric point:
geometric stalks commute with finite-level coefficient reduction, compatibly with the stalk
transports. For a morphism `ρ : Λ →+* Λ'` of finite coefficient rings whose exponent is invertible
on `k` and a geometric point `x̄ : Spec k ⟶ X`, the geometric stalk commutes with restriction of
scalars along `ρ` through a coefficient comparison `β` for which `K_x̄ ⊗ᴸ_Λ Λ' ⟶ (K ⊗ᴸ_Λ Λ')_x̄` is
an isomorphism for every `K ∈ Dᵇctf(X, Λ)`, and `β` is compatible with the stalk transport at `x̄`
along every pair of automorphisms fixing `x̄`
(`AlgebraicGeometry.Etale.IsStalkPullbackCompatible`). -/
theorem exists_isCoefficientChange_geometricStalk
    [HasInvertibleExponent Λ (Spec (.of k))] (x : Spec (.of k) ⟶ X) :
    ∃ β, IsCoefficientChange ρ (geometricStalk Λ x) (geometricStalk Λ' x) β ∧
      ∀ (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (hx : h ≫ x = x ≫ g) [IsIso h],
        IsStalkPullbackCompatible ρ β hx :=
  ⟨geometricStalkRestrictScalarsIso ρ x,
    isCoefficientChange_geometricStalkRestrictScalarsIso ρ x,
    fun _ _ hx _ ↦ isStalkPullbackCompatible_geometricStalkRestrictScalarsIso ρ x hx⟩

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} (S : AdicSystem I X)
  [∀ n, Finite (R ⧸ I ^ n)] [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))]

include aX in
/-- Levelwise perfectness and normalization: each `P_n = RΓ_c(X, L_n)` and each geometric stalk
`P_{x̄, n} = (L_n)_x̄` is a perfect complex of `A_n`-modules, and the transition `ν_n` induces,
through an identification of `RΓ_c(X, -)` (resp. `(-)_x̄`) of a restriction of scalars with the
restriction of scalars of `RΓ_c(X, -)` (resp. `(-)_x̄`), a map `P_{n+1} ⟶ Res P_n` exhibiting `P_n`
as `P_{n+1} ⊗ᴸ_{A_{n+1}} A_n`, i.e. an isomorphism `P_{n+1} ⊗ᴸ_{A_{n+1}} A_n ≅ P_n`. -/
theorem isPerfect_and_exists_isDerivedBaseChange (n : ℕ) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ n)) aX).obj
        (S.obj n)).IsPerfect ∧
      (∃ e : (compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX).obj
          ((_root_.DerivedCategory.levelTransitionRestrictScalars _ I n.le_succ).obj (S.obj n)) ≅
          (ModuleCat.derivedRestrictScalars
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ))).obj
            ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ n)) aX).obj
              (S.obj n)),
        ModuleCat.IsDerivedBaseChange
          ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX).map
            (S.map n) ≫ e.hom)) ∧
      ∀ x : Spec (.of k) ⟶ X,
        ((geometricStalk (R ⧸ I ^ n) x).obj (S.obj n)).IsPerfect ∧
        ∃ e : (geometricStalk (R ⧸ I ^ (n + 1)) x).obj
            ((_root_.DerivedCategory.levelTransitionRestrictScalars _ I n.le_succ).obj
              (S.obj n)) ≅
            (ModuleCat.derivedRestrictScalars
              (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ))).obj
              ((geometricStalk (R ⧸ I ^ n) x).obj (S.obj n)),
          ModuleCat.IsDerivedBaseChange
            ((geometricStalk (R ⧸ I ^ (n + 1)) x).map (S.map n) ≫ e.hom) := by
  have hsurj : Function.Surjective
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ)) :=
    Ideal.Quotient.factor_surjective _
  refine ⟨isPerfect_compactlySupportedGlobalSections _ aX _ (S.boundedConstructibleFiniteTor n),
    ?_, fun x ↦ ⟨isPerfect_geometricStalk _ x _ (S.boundedConstructibleFiniteTor n), ?_⟩⟩
  · obtain ⟨α, hα, -⟩ := exists_isCoefficientChange_compactlySupportedGlobalSections _ aX hsurj
    exact ⟨α.app _, hα _ (S.boundedConstructibleFiniteTor (n + 1)) (S.isDerivedBaseChange n)⟩
  · obtain ⟨β, hβ, -⟩ := exists_isCoefficientChange_geometricStalk
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ)) x
    exact ⟨β.app _, hβ _ (S.boundedConstructibleFiniteTor (n + 1)) (S.isDerivedBaseChange n)⟩

include aX in
/-- The coefficient identifications from which
`AlgebraicGeometry.Etale.AdicSystem.compactSupportTower` is built exist, compatibly with the
compact-support base change along every pair of automorphisms
(`AlgebraicGeometry.Etale.exists_isCoefficientChange_compactlySupportedGlobalSections`). -/
lemma exists_compactSupportTower :
    ∃ (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n)),
      (∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n)) ∧
      ∀ (n : ℕ) (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (sq : IsPullback g aX aX h)
        [IsIso h], IsCompactPullbackCompatible (I.powSuccFactor n) (α n) sq := by
  choose α hα hα' using fun n : ℕ ↦ exists_isCoefficientChange_compactlySupportedGlobalSections
    (I.powSuccFactor n) aX (Ideal.Quotient.factor_surjective _)
  exact ⟨α, hα, hα'⟩

/-- The coefficient identifications from which `AlgebraicGeometry.Etale.AdicSystem.stalkTower`
is built exist, compatibly with the stalk transports
(`AlgebraicGeometry.Etale.exists_isCoefficientChange_geometricStalk`). -/
lemma exists_stalkTower (x : Spec (.of k) ⟶ X) :
    ∃ (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n)),
      (∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n)) ∧
      ∀ (n : ℕ) (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (hx : h ≫ x = x ≫ g)
        [IsIso h], IsStalkPullbackCompatible (I.powSuccFactor n) (β n) hx := by
  choose β hβ hβ' using fun n : ℕ ↦ exists_isCoefficientChange_geometricStalk
    (I.powSuccFactor n) x
  exact ⟨β, hβ, hβ'⟩

end AdicSystem

end AlgebraicGeometry.Etale
