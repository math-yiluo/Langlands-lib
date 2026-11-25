/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunctionBaseChange

/-!
# The affine-space adjunction from the projective-line adjunction

For a normalized Tate twist and every scheme `S` on which the exponent of `Λ` is invertible, the
projection `p_d : 𝔸^d_S ⟶ S` satisfies `Rp_{d!} ⊣ Lp_d^*(d)[2d]`
(`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`, blueprint
`lemma-affine-space-etale-localization--1`, `lemma-affine-space-etale-localization`).

The proof composes *twisted adjunctions* `Rf_! ⊣ Lf^*(a)[2a]`
(`AlgebraicGeometry.Etale.nonempty_adjunction_twistShift_comp`): étale morphisms have one with
`a = 0` (`Rf_!` is the extension by zero, left adjoint to `Lf^*`), the projective line
`q : ℙ¹_S ⟶ S` has one with `a = 1` (`proposition-adjunction-projective-line--1`), so the affine
line, which is the standard chart `𝔸¹_S ⊆ ℙ¹_S` followed by `q`, has one with `a = 1`, and affine
spaces follow by induction through `𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`.

## Main statements

- `AlgebraicGeometry.Etale.twistShiftZeroNatIso`, `AlgebraicGeometry.Etale.twistShiftAddNatIso`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftNatIso`: the functorial forms of the
  identifications `K(0)[0] ≅ K`, `K(b)[2b](a)[2a] ≅ K(b + a)[2(b + a)]` and
  `Lf^*(K(m)[2m]) ≅ (Lf^* K)(m)[2m]`.
- `AlgebraicGeometry.Etale.nonempty_adjunction_twistShift_comp`
- `AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

section NatIso

/-- Tensoring on the right with `M` then with `N` is tensoring on the right with `M ⊗ᴸ N`:
the associator `(K ⊗ᴸ M) ⊗ᴸ N ≅ K ⊗ᴸ (M ⊗ᴸ N)`, natural in `K`. -/
noncomputable def derivedTensorFlipObjCompIso (X : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj M ⋙
        (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj N ≅
      (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj N) :=
  (tensorRightTensor M N).symm

/-- Tensoring on the right with the unit is the identity: the right unitor `K ⊗ᴸ Λ_X ≅ K`,
natural in `K`. -/
noncomputable def derivedTensorFlipObjUnitIso (X : Scheme.{u}) :
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj (𝟙_ _) ≅ 𝟭 _ :=
  rightUnitorNatIso _

/-- The functorial form of `AlgebraicGeometry.Etale.twistShiftZeroIso`: `K(0)[0] ≅ K`,
naturally in `K`. -/
noncomputable def twistShiftZeroNatIso (X : Scheme.{u}) [HasInvertibleExponent Λ X] :
    twistShift Λ X 0 ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft (tateTwist Λ X 0) (shiftFunctorZero' _ (2 * 0) (by simp)) ≪≫
    Functor.rightUnitor _ ≪≫
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso (HasTateTwist.twistObjectZeroIso X) ≪≫
    derivedTensorFlipObjUnitIso Λ X

/-- The functorial form of `AlgebraicGeometry.Etale.twistShiftTwistShiftIso`:
`(K(b)[2b])(a)[2a] ≅ K(b + a)[2(b + a)]`, naturally in `K`. -/
noncomputable def twistShiftAddNatIso (X : Scheme.{u}) [HasInvertibleExponent Λ X] (a b : ℤ) :
    twistShift Λ X b ⋙ twistShift Λ X a ≅ twistShift Λ X (b + a) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tateTwist Λ X b) ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj
        (tateObject Λ X a)).commShiftIso (2 * b)) _ ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (shiftFunctorAdd' _ (2 * b) (2 * a) (2 * (b + a)) (by ring)).symm ≪≫
    Functor.isoWhiskerRight (derivedTensorFlipObjCompIso Λ X _ _ ≪≫
      (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso (HasTateTwist.twistObjectAddIso X b a))
      _

/-- The derived pullback commutes with tensoring on the right with a fixed complex `M`:
`Lf^*(K ⊗ᴸ M) ≅ Lf^* K ⊗ᴸ Lf^* M`, naturally in `K`. -/
noncomputable def leftDerivedUpperStarFlipObjIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedTensor (ModuleCat.{u + 1} Λ) Y).flip.obj M ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M) :=
  NatIso.ofComponents (fun K ↦ leftDerivedUpperStarTensorIso _ f K M)
    fun φ ↦ leftDerivedUpperStarTensorIso_hom_naturality_left f φ M

/-- The functorial form of `AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftIso`:
`Lf^*(K(m)[2m]) ≅ (Lf^* K)(m)[2m]`, naturally in `K`. -/
noncomputable def leftDerivedUpperStarTwistShiftNatIso {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (m : ℤ) :
    twistShift Λ Y m ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X m :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tateTwist Λ Y m)
      ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarFlipObjIso Λ f (tateObject Λ Y m) ≪≫
      Functor.isoWhiskerLeft _ ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso
        (leftDerivedUpperStarTateObjectIso f m))) _ ≪≫
    Functor.associator _ _ _

end NatIso

section Adjunction

/-- **Twisted adjunctions compose.** If `Rf_! ⊣ Lf^*(a)[2a]` and `Rg_! ⊣ Lg^*(b)[2b]`, then
`R(f ≫ g)_! ⊣ L(f ≫ g)^*(c)[2c]` for `c = b + a`: compose the adjunctions, identify
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`)
and `Lf^*(Lg^* K(b)[2b])(a)[2a] ≅ L(f ≫ g)^* K(b + a)[2(b + a)]`. -/
theorem nonempty_adjunction_twistShift_comp {X Y Z : Scheme.{u}} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (w : f ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification h] {a b c : ℤ}
    (habc : b + a = c)
    (hf : Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⊣
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X a))
    (hg : Nonempty (R(g)_![ModuleCat.{u + 1} Λ] ⊣
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ Y b)) :
    Nonempty (R(h)_![ModuleCat.{u + 1} Λ] ⊣
      L((h)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X c) := by
  subst w habc
  obtain ⟨adjf⟩ := hf
  obtain ⟨adjg⟩ := hg
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f g
  exact ⟨((adjf.comp adjg).ofNatIsoLeft e.symm).ofNatIsoRight
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L((g)^*[ModuleCat.{u + 1} Λ]) ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarTwistShiftNatIso Λ f b) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft L((f)^*[ModuleCat.{u + 1} Λ]) (twistShiftAddNatIso Λ X a b)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarComp _ f g).symm _)⟩

/-- **The twisted adjunction of an étale morphism.** For `e` étale admitting a compactification,
`Re_! ⊣ Le^*(0)[0]`: `Re_!` is the extension by zero
(`AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`), left adjoint to `Le^*`. -/
theorem nonempty_adjunction_twistShift_of_etale {X Y : Scheme.{u}} [HasInvertibleExponent Λ X]
    (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] {m : ℤ}
    (hm : m = 0) :
    Nonempty (R(e)_![ModuleCat.{u + 1} Λ] ⊣
      L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X m) := by
  subst hm
  have := isIso_compactificationEtaleComparison Λ e (HasCompactification.compactification e)
  exact ⟨(compactificationEtaleAdjunction Λ e
    (HasCompactification.compactification e)).ofNatIsoRight
    ((Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ (twistShiftZeroNatIso Λ X).symm)⟩

/-- **The projective-line adjunction** `Rq_! ⊣ Lq^*(1)[2]` for `q : ℙ¹_S ⟶ S` and a normalized
Tate twist, over any scheme `S` on which the exponent of `Λ` is invertible
(blueprint `proposition-adjunction-projective-line--1`; it is part of
`AlgebraicGeometry.Etale.projectiveLineAdjunctionBaseChange_of_isNormalized`). -/
theorem nonempty_adjunction_projectiveLine [HasTateTwist.IsNormalized Λ] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    haveI : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) := .of_hom (_ ↘ S)
    Nonempty (R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
      L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1) := by
  obtain ⟨adj, -, -⟩ := projectiveLineAdjunctionBaseChange_of_isNormalized Λ (𝟙 S)
  exact ⟨adj⟩

/-- **The affine-line adjunction** `Rp_! ⊣ Lp^*(1)[2]` for `p : 𝔸¹_S ⟶ S` and a normalized
Tate twist: `p` is the standard chart `j : 𝔸¹_S ⟶ ℙ¹_S`, an open immersion with
`Rj_! ⊣ Lj^*`, followed by the projective line `q : ℙ¹_S ⟶ S`, with `Rq_! ⊣ Lq^*(1)[2]`. -/
theorem nonempty_adjunction_affineLine [HasTateTwist.IsNormalized Λ] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    haveI : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); S) := .of_hom (_ ↘ S)
    Nonempty (R((𝔸(ULift.{u} (Fin 1); S) ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
      L(((𝔸(ULift.{u} (Fin 1); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ 𝔸(ULift.{u} (Fin 1); S) 1) := by
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); S) := .of_hom (_ ↘ S)
  have : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) := .of_hom (_ ↘ S)
  have : HasCompactification (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  exact nonempty_adjunction_twistShift_comp Λ
    (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)
    (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) (AffineSpace.toRelativeProjectiveSpace_over _ S)
    (by norm_num) (nonempty_adjunction_twistShift_of_etale Λ _ rfl)
    (nonempty_adjunction_projectiveLine Λ S)

/-- Blueprint `lemma-affine-space-etale-localization--1`: affine-space ambient adjunction.

For the projection `p_d : 𝔸^d_S ⟶ S` of relative affine space over a scheme `S` on which the
exponent of `Λ` is invertible, on the entire derived categories of étale sheaves of
`Λ`-modules,

`Rp_{d!} ⊣ p_d^*(d)[2d]`.

This is also clause 1 of `lemma-affine-space-etale-localization`. For `d = 0` the
projection is an isomorphism; for `d + 1` it is, through `𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`, the
composite of the affine-line projection over `𝔸^d_S` and of `p_d`, and twisted adjunctions
compose (`AlgebraicGeometry.Etale.nonempty_adjunction_twistShift_comp`). -/
theorem nonempty_rightDerivedLowerShriek_adjunction_affineSpace [HasTateTwist.IsNormalized Λ]
    (d : ℕ) (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    Nonempty (R((𝔸(ULift.{u} (Fin d); S) ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
      L(((𝔸(ULift.{u} (Fin d); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ 𝔸(ULift.{u} (Fin d); S) d) := by
  induction d with
  | zero =>
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 0); S) := .of_hom (_ ↘ S)
    exact nonempty_adjunction_twistShift_of_etale Λ _ (by simp)
  | succ d ih =>
    set φ : 𝔸(ULift.{u} (Fin (d + 1)); S) ≅ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) :=
      AffineSpace.reindexIso S ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
        (finSumFinEquiv.trans Equiv.ulift.symm)) ≪≫ AffineSpace.sumIso S
    set q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) ↘ 𝔸(ULift.{u} (Fin d); S)
    set p := 𝔸(ULift.{u} (Fin d); S) ↘ S
    have : HasCompactification (φ.hom ≫ q) := HasCompactification.comp_of_isOpenImmersion q φ.hom
    have : HasCompactification φ.hom := (Compactification.ofIsOpenImmersion _).hasCompactification
    have h : (φ.hom ≫ q) ≫ p = 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S := by
      rw [Category.assoc, Iso.trans_hom, Category.assoc, AffineSpace.sumIso_hom_over_over,
        AffineSpace.reindexIso_hom, AffineSpace.reindex_over]
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin d); S) := .of_hom p
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin (d + 1)); S) := .of_hom (_ ↘ S)
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) := .of_hom q
    exact nonempty_adjunction_twistShift_comp Λ (φ.hom ≫ q) p h (by push_cast; ring)
      (nonempty_adjunction_twistShift_comp Λ φ.hom q rfl (add_zero 1)
        (nonempty_adjunction_twistShift_of_etale Λ _ rfl)
        (nonempty_adjunction_affineLine Λ _)) ih

end Adjunction

end Etale

end AlgebraicGeometry
