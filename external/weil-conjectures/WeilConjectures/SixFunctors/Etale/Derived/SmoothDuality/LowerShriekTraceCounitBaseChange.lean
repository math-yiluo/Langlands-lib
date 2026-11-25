/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace

/-!
# Base change of trace counits

For a morphism `f : X ⟶ Y` with a trace `t : Rf_! T ⟶ Λ_Y` and identifications
`γ_K : G K ≅ T ⊗ᴸ Lf^* K`, the *trace counit* `Rf_!(G K) ⟶ K`
(`AlgebraicGeometry.Etale.lowerShriekTraceCounit`) is the inverse of the projection map followed
by the trace. For a cartesian square `g' ≫ f = f' ≫ g`, the trace counits of `f` and `f'` are
compatible with the compact-support base change `Ex_!` as soon as the traces are, and the
identifications `γ` are compatible with pullback
(`AlgebraicGeometry.Etale.lowerShriekTraceCounit_baseChange`). For the identifications
`K(m)[2m] ≅ Λ(m)[2m] ⊗ᴸ K` (`AlgebraicGeometry.Etale.twistShiftTensorIso`), the compatibility
with pullback is
`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftIso_hom_twistShiftTensorIso_hom`.

## Main statements

- `AlgebraicGeometry.Etale.lowerShriekTraceCounit_baseChange`
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftIso_hom_twistShiftTensorIso_hom`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- As in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`, whose
-- compatibility of the projection map with base change is used below.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

attribute [local instance 20000] Etale.sheafBraidedCategory

section Braiding

variable {X X' : Scheme.{u}}

omit [Finite Λ] in
/-- The tensor comparison of `Lh^*` commutes with the symmetry of `⊗ᴸ`
(`AlgebraicGeometry.Etale.derivedTensorBraiding`). -/
@[reassoc]
lemma leftDerivedUpperStar_map_derivedTensorBraiding_comp_tensorComparison (h : X' ⟶ X)
    (A B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((h)^*[ModuleCat.{u + 1} Λ]).map
        (((derivedTensorBraiding (ModuleCat.{u + 1} Λ) X).hom.app A).app B) ≫
      ((leftDerivedUpperStarTensorComparison _ h).app B).app A =
    ((leftDerivedUpperStarTensorComparison _ h).app A).app B ≫
      ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) X').hom.app
        (L((h)^*[ModuleCat.{u + 1} Λ]).obj A)).app (L((h)^*[ModuleCat.{u + 1} Λ]).obj B) :=
  leftDerivedUpperStar_map_braiding_hom_δ _ h A B

end Braiding

section TwistShift

variable [HasTateTwist Λ]

variable (Λ) in
/-- The identification `K(m)[2m] ≅ Λ(m)[2m] ⊗ᴸ K`: the shift is moved into the second factor of
`K ⊗ᴸ Λ(m)`, and the factors are exchanged by the symmetry of `⊗ᴸ`
(`AlgebraicGeometry.Etale.derivedTensorBraiding`). For the projective line it is
`AlgebraicGeometry.Etale.projectiveLineTwistShiftIso`. -/
noncomputable def twistShiftTensorIso (X : Scheme.{u}) (m : ℤ)
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ X m).obj F ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((tateObject Λ X m)⟦2 * m⟧)).obj F :=
  (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj F).commShiftIso (2 * m)).symm.app _ ≪≫
    ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) X).app _).app _

omit [Finite Λ] in
/-- The identification `K(m)[2m] ≅ Λ(m)[2m] ⊗ᴸ K` is natural in `K`. -/
@[reassoc]
lemma twistShiftTensorIso_hom_naturality (X : Scheme.{u})
    (m : ℤ) {F F' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (κ : F ⟶ F') :
    (twistShift Λ X m).map κ ≫ (twistShiftTensorIso Λ X m F').hom =
      (twistShiftTensorIso Λ X m F).hom ≫ (tateObject Λ X m)⟦2 * m⟧ ◁ κ := by
  have h₁ := NatTrans.shift_app ((derivedTensor (ModuleCat.{u + 1} Λ) X).map κ) (2 * m)
    (tateObject Λ X m)
  have h₂ := NatTrans.congr_app ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) X).hom.naturality κ)
    ((tateObject Λ X m)⟦2 * m⟧)
  simp only [NatTrans.comp_app, Functor.flip_map_app] at h₂
  simp only [twistShiftTensorIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  erw [h₁]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [h₂]
  rfl

variable {X X' : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X']

omit [Finite Λ] in
/-- **Pullback of the identification `K(m)[2m] ≅ Λ(m)[2m] ⊗ᴸ K`.** Along `h : X' ⟶ X`, the
identification `AlgebraicGeometry.Etale.twistShiftTensorIso` is compatible with the commutation
of `Lh^*` with twist-and-shift (`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftIso`), the
tensor comparison of `Lh^*` and `Lh^*(Λ(m)[2m]) ≅ Λ(m)[2m]`. -/
@[reassoc]
theorem leftDerivedUpperStarTwistShiftIso_hom_twistShiftTensorIso_hom (h : X' ⟶ X) (m : ℤ)
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarTwistShiftIso Λ h m F).hom ≫
        (twistShiftTensorIso Λ X' m (L((h)^*[ModuleCat.{u + 1} Λ]).obj F)).hom =
      L((h)^*[ModuleCat.{u + 1} Λ]).map (twistShiftTensorIso Λ X m F).hom ≫
        ((leftDerivedUpperStarTensorComparison _ h).app _).app F ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X').map
          (leftDerivedUpperStarTateShiftIso Λ h m).hom).app
            (L((h)^*[ModuleCat.{u + 1} Λ]).obj F) := by
  have hs := leftDerivedUpperStarTensorComparison_shift_right (ModuleCat.{u + 1} Λ) h F
    (tateObject Λ X m) (2 * m)
  simp only [twistShiftTensorIso, leftDerivedUpperStarTwistShiftIso,
    leftDerivedUpperStarTateShiftIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, leftDerivedUpperStarTensorIso_hom, Functor.map_comp, Category.assoc,
    NatTrans.comp_app]
  have hb := ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) X').hom.app
    (L((h)^*[ModuleCat.{u + 1} Λ]).obj F)).naturality
      ((L((h)^*[ModuleCat.{u + 1} Λ]).commShiftIso (2 * m)).hom.app (tateObject Λ X m) ≫
        (leftDerivedUpperStarTateObjectIso h m).hom⟦2 * m⟧')
  rw [Functor.flip_obj_map] at hb
  rw [leftDerivedUpperStar_map_derivedTensorBraiding_comp_tensorComparison_assoc,
    ← NatTrans.comp_app, ← Functor.map_comp]
  erw [← hb]
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  refine congrArg (· ≫ _) ?_
  simp only [Category.assoc]
  erw [Functor.commShiftIso_inv_naturality]
  simp only [← Category.assoc]
  refine congrArg (· ≫ _) ?_
  simp only [Category.assoc]
  rw [← cancel_epi (L((h)^*[ModuleCat.{u + 1} Λ]).map
    ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj F).commShiftIso (2 * m)).hom.app
      (tateObject Λ X m))), ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% hs]
  rw [Iso.hom_inv_id_app]
  erw [Category.comp_id]

end TwistShift

section Counit

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Base change of trace counits.** For a cartesian square `g' ≫ f = f' ≫ g`, traces
`t : Rf_! T ⟶ Λ_Y` and `t' : Rf'_! T' ⟶ Λ_{Y'}` compatible with `Ex_!` through
`τ : Lg'^* T ⟶ T'`, and identifications `γ_K : G K ≅ T ⊗ᴸ Lf^* K`,
`γ'_K : G' K ≅ T' ⊗ᴸ Lf'^* K` compatible with pullback through `φ_K : Lg'^* G K ⟶ G' Lg^* K`, the
trace counits (`AlgebraicGeometry.Etale.lowerShriekTraceCounit`) are compatible with `Ex_!`:
`Ex_! ≫ Rf'_! φ_K ≫ ε'_{Lg^* K} = Lg^* ε_K`. This is the projection map commuting with `Ex_!`
(`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`) and the
monoidality of `Lg^*`. -/
theorem lowerShriekTraceCounit_baseChange (sq : IsPullback g' f' f g) [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f']
    (T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (T' : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (t : (R(f)_![ModuleCat.{u + 1} Λ]).obj T ⟶ 𝟙_ _)
    (t' : (R(f')_![ModuleCat.{u + 1} Λ]).obj T' ⟶ 𝟙_ _)
    (τ : L((g')^*[ModuleCat.{u + 1} Λ]).obj T ⟶ T')
    (ht : L((g)^*[ModuleCat.{u + 1} Λ]).map t ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom =
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app T ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map τ ≫ t')
    {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {G' : _root_.DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : ∀ K, G.obj K ≅ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj T).obj
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))
    (γ' : ∀ K, G'.obj K ≅ ((derivedTensor (ModuleCat.{u + 1} Λ) X').obj T').obj
      ((L((f')^*[ModuleCat.{u + 1} Λ])).obj K))
    (φ : ∀ K, L((g')^*[ModuleCat.{u + 1} Λ]).obj (G.obj K) ⟶
      G'.obj (L((g)^*[ModuleCat.{u + 1} Λ]).obj K))
    (hγ : ∀ K, φ K ≫ (γ' (L((g)^*[ModuleCat.{u + 1} Λ]).obj K)).hom =
      L((g')^*[ModuleCat.{u + 1} Λ]).map (γ K).hom ≫
        ((leftDerivedUpperStarTensorComparison _ g').app T).app
          (L((f)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        L((g')^*[ModuleCat.{u + 1} Λ]).obj T ◁
          derivedSquareUpperStarIsoInvApp _ sq.toCommSq K ≫
        τ ▷ L((f')^*[ModuleCat.{u + 1} Λ]).obj (L((g)^*[ModuleCat.{u + 1} Λ]).obj K))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekBaseChangeMap Λ sq).app (G.obj K) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map (φ K) ≫
        lowerShriekTraceCounit Λ f' T' t' γ' (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) =
      L((g)^*[ModuleCat.{u + 1} Λ]).map (lowerShriekTraceCounit Λ f T t γ K) := by
  have hlib : L((g)^*[ModuleCat.{u + 1} Λ]).map (((projectionMap _ f).app T).app K) ≫
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj T).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
      (R(f')_![ModuleCat.{u + 1} Λ]).map
        (((leftDerivedUpperStarTensorComparison _ g').app T).app
          (L((f)^*[ModuleCat.{u + 1} Λ]).obj K)) ≫
      (R(f')_![ModuleCat.{u + 1} Λ]).map (L((g')^*[ModuleCat.{u + 1} Λ]).obj T ◁
          derivedSquareUpperStarIsoInvApp _ sq.toCommSq K) =
      ((leftDerivedUpperStarTensorComparison _ g).app ((R(f)_![ModuleCat.{u + 1} Λ]).obj T)).app
          K ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sq).app T ▷ L((g)^*[ModuleCat.{u + 1} Λ]).obj K ≫
        ((projectionMap _ f').app (L((g')^*[ModuleCat.{u + 1} Λ]).obj T)).app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) :=
    projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq T K
  have := isIso_projectionMap_of_finite Λ f
  have := isIso_projectionMap_of_finite Λ f'
  rw [lowerShriekTraceCounit, lowerShriekTraceCounit, ← Functor.map_comp_assoc, hγ]
  have hn := (rightDerivedLowerShriekBaseChangeMap Λ sq).naturality (γ K).hom
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  refine congrArg (_ ≫ ·) ?_
  rw [← cancel_epi (L((g)^*[ModuleCat.{u + 1} Λ]).map (((projectionMap _ f).app T).app K))]
  conv_rhs => rw [← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [reassoc_of% hlib, ← reassoc_of% (projectionMap_app_app_naturality_left f' τ
      (L((g)^*[ModuleCat.{u + 1} Λ]).obj K)), IsIso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc, ← ht,
    comp_whiskerRight_assoc]
  erw [← leftDerivedUpperStarTensorIso_hom_naturality_left_assoc]
  rw [leftDerivedUpperStarTensorIso_hom, leftDerivedUpperStarTensorComparison_leftUnitor_hom,
    ← Functor.map_comp, Functor.map_comp]
  rfl

/-- **Base change of twisted trace counits.** For a cartesian square `g' ≫ f = f' ≫ g` and traces
`t : Rf_!(Λ(m)[2m]) ⟶ Λ_Y`, `t' : Rf'_!(Λ(m)[2m]) ⟶ Λ_{Y'}` compatible with `Ex_!` and
`Lg'^*(Λ(m)[2m]) ≅ Λ(m)[2m]`, the trace counits `Rf_!(Lf^* K(m)[2m]) ⟶ K` built from the
identifications `K(m)[2m] ≅ Λ(m)[2m] ⊗ᴸ K` (`AlgebraicGeometry.Etale.twistShiftTensorIso`) are
compatible with `Ex_!` and `Lg'^*(Lf^* K(m)[2m]) ≅ Lf'^* Lg^* K(m)[2m]`. -/
theorem lowerShriekTraceCounit_twistShift_baseChange [HasTateTwist Λ]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X']
    (sq : IsPullback g' f' f g) [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (m : ℤ) (t : (R(f)_![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X m)⟦2 * m⟧) ⟶ 𝟙_ _)
    (t' : (R(f')_![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X' m)⟦2 * m⟧) ⟶ 𝟙_ _)
    (ht : L((g)^*[ModuleCat.{u + 1} Λ]).map t ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom =
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app _ ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map (leftDerivedUpperStarTateShiftIso Λ g' m).hom ≫ t')
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekBaseChangeMap Λ sq).app
        ((twistShift Λ X m).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
      (R(f')_![ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarTwistShiftIso Λ g' m _).hom ≫
          (twistShift Λ X' m).map ((derivedSquareUpperStarIso _ sq.toCommSq).inv.app K)) ≫
        lowerShriekTraceCounit Λ f' _ t' (G := L((f')^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X' m)
          (fun K ↦ twistShiftTensorIso Λ X' m ((L((f')^*[ModuleCat.{u + 1} Λ])).obj K))
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) =
      (L((g)^*[ModuleCat.{u + 1} Λ])).map
        (lowerShriekTraceCounit Λ f _ t (G := L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X m)
          (fun K ↦ twistShiftTensorIso Λ X m ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) K) := by
  refine lowerShriekTraceCounit_baseChange sq _ _ t t' _ ht
    (G := L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X m)
    (G' := L((f')^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X' m) _ _
    (fun K ↦ (leftDerivedUpperStarTwistShiftIso Λ g' m _).hom ≫
      (twistShift Λ X' m).map ((derivedSquareUpperStarIso _ sq.toCommSq).inv.app K))
    (fun K ↦ ?_) K
  rw [Category.assoc, twistShiftTensorIso_hom_naturality,
    leftDerivedUpperStarTwistShiftIso_hom_twistShiftTensorIso_hom_assoc]
  erw [whisker_exchange]
  rfl

end Counit

end Etale

end AlgebraicGeometry
