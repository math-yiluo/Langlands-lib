/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange

/-!
# Maps out of an open and closed piece

Let `σ : X ⟶ W` be an immersion which is both open and closed. The extension by zero `Dσ_!` is
then both left adjoint (as for every open immersion) and right adjoint (through `Dσ_! ≅ Rσ_*`)
to the derived pullback `Lσ^*`. Consequently a morphism `ψ : Lσ^* T₁ ⟶ Lσ^* T₂` on the piece
`X` induces a morphism `T₁ ⟶ T₂` on `W`, "restrict to `X`, apply `ψ` and extend by zero"
(`AlgebraicGeometry.Etale.clopenTransfer`):

`T₁ ⟶ Dσ_! Lσ^* T₁ ⟶ Dσ_! Lσ^* T₂ ⟶ T₂`.

This construction is natural in `T₁`, `T₂` and commutes with base change
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_clopenTransfer`). We also record that the
derived base change isomorphism of the extension by zero along an open immersion is the mate of
the square isomorphism of the derived pullbacks, for the adjunctions `Dj_! ⊣ Lj^*`
(`AlgebraicGeometry.Etale.unit_map_derivedOpenImmersionLowerShriekBaseChangeIso'`).

## Main definitions

- `AlgebraicGeometry.Etale.clopenUpperStarLowerShriekAdjunction`: `Lσ^* ⊣ Dσ_!`.
- `AlgebraicGeometry.Etale.clopenTransfer`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section BaseChange

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **The derived base change isomorphism of the extension by zero along open immersions is the
mate of the square isomorphism of the derived pullbacks**, for the adjunctions `Dj_! ⊣ Lj^*`
and `Dj'_! ⊣ Lj'^*`. -/
lemma unit_map_derivedOpenImmersionLowerShriekBaseChangeIso' (hsq : IsPullback g' j' j g'')
    (K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j').unit.app
        (L((g')^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      L((j')^*[ModuleCat.{u + 1} Λ]).map
        ((derivedOpenImmersionLowerShriekBaseChangeIso _ hsq).hom.app K) =
    L((g')^*[ModuleCat.{u + 1} Λ]).map
        ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).unit.app K) ≫
      (derivedSquareUpperStarIso _ hsq.toCommSq).inv.app
        (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K) := by
  have h := unit_map_derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq K
  rw [derivedOpenImmersionSquareMap_app] at h
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j').inv.naturality
    ((derivedOpenImmersionLowerShriekBaseChangeIso _ hsq).hom.app K)
  simp only [derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc, Functor.map_comp]
  dsimp at hn ⊢
  rw [← hn, reassoc_of% h]
  simp

/-- The mate form of `unit_map_derivedOpenImmersionLowerShriekBaseChangeIso'`. -/
lemma mateEquiv_derivedOpenImmersionLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'') :
    mateEquiv (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j)
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j')
      (TwoSquare.mk _ _ _ _ (derivedOpenImmersionLowerShriekBaseChangeIso _ hsq).hom) =
    TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso _ hsq.toCommSq).inv :=
  mateEquiv_eq_of_unit _ _ _ _ fun K ↦
    (unit_map_derivedOpenImmersionLowerShriekBaseChangeIso' Λ hsq K).symm

/-- **The counit of the extension by zero commutes with base change**: for a cartesian square
of open immersions, `Lg''^*` of the counit of `Dj_! ⊣ Lj^*` is, through the base change
isomorphism and the square isomorphism of the pullbacks, the counit of `Dj'_! ⊣ Lj'^*`. -/
lemma leftDerivedUpperStar_map_counit_derivedOpenImmersionLowerShriek
    (hsq : IsPullback g' j' j g'')
    (T : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g'')^*[ModuleCat.{u + 1} Λ]).map
        ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).counit.app T) =
      (derivedOpenImmersionLowerShriekBaseChangeIso _ hsq).inv.app
          (L((j)^*[ModuleCat.{u + 1} Λ]).obj T) ≫
        D((j')_!open[ModuleCat.{u + 1} Λ]).map
          ((derivedSquareUpperStarIso _ hsq.toCommSq).inv.app T) ≫
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j').counit.app
          (L((g'')^*[ModuleCat.{u + 1} Λ]).obj T) := by
  have h := mateEquiv_counit (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j')
    (TwoSquare.mk _ _ _ _ (derivedOpenImmersionLowerShriekBaseChangeIso _ hsq).hom) T
  rw [mateEquiv_derivedOpenImmersionLowerShriekBaseChangeIso] at h
  dsimp only [TwoSquare.mk] at h
  rw [h, Iso.inv_hom_id_app_assoc]

end BaseChange

section Clopen

variable {X W : Scheme.{u}} (σ : X ⟶ W) [IsOpenImmersion σ] [IsClosedImmersion σ]

/-- For an open and closed immersion `σ`, the extension by zero `Dσ_!` is right adjoint to the
derived pullback `Lσ^*`: the adjunction `Dσ^* ⊣ Rσ_*` transported along the isomorphism
`Dσ_! ≅ Rσ_*` (`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekToLowerStar`) and
`Lσ^* ≅ Dσ^*`. -/
noncomputable def clopenUpperStarLowerShriekAdjunction :
    L((σ)^*[ModuleCat.{u + 1} Λ]) ⊣ D((σ)_!open[ModuleCat.{u + 1} Λ]) :=
  ((mapDerivedUpperStarLowerStarAdjunction _ σ).ofNatIsoRight
    (asIso (derivedOpenImmersionLowerShriekToLowerStar _ σ)).symm).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory _ σ).symm

/-- The counit of `Lσ^* ⊣ Dσ_!` is the inverse of the unit of `Dσ_! ⊣ Lσ^*`. -/
@[reassoc (attr := simp)]
lemma unit_app_clopenUpperStarLowerShriekAdjunction_counit_app
    (S : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ σ).unit.app S ≫
      (clopenUpperStarLowerShriekAdjunction Λ σ).counit.app S = 𝟙 S := by
  have ht :=
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) σ).left_triangle_components
    (D((σ)_!open[ModuleCat.{u + 1} Λ]).obj S)
  have hn := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) σ).counit.naturality
    (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) σ).unit.app S))
  simp only [clopenUpperStarLowerShriekAdjunction,
    derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    Adjunction.ofNatIsoLeft_counit, Adjunction.ofNatIsoRight_counit,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Iso.symm_inv, asIso_hom, Category.assoc,
    derivedOpenImmersionLowerShriekToLowerStar, Functor.associator_inv_app, NatIso.isIso_inv_app,
    Functor.map_comp, Functor.map_inv]
  dsimp at hn ht ⊢
  rw [CategoryTheory.Functor.map_id, Category.id_comp, ← Functor.map_inv, ← Functor.map_inv, hn,
    reassoc_of% ht, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id]


/-- The counit of `Lσ^* ⊣ Dσ_!` is the inverse of the unit of `Dσ_! ⊣ Lσ^*`. -/
lemma clopenUpperStarLowerShriekAdjunction_counit_app
    (S : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (clopenUpperStarLowerShriekAdjunction Λ σ).counit.app S =
      inv ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ σ).unit.app S) := by
  rw [← cancel_epi ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ σ).unit.app S),
    unit_app_clopenUpperStarLowerShriekAdjunction_counit_app, IsIso.hom_inv_id]
  rfl

/-- `Lσ^*` of the unit of `Lσ^* ⊣ Dσ_!` is the unit of `Dσ_! ⊣ Lσ^*`. -/
lemma leftDerivedUpperStar_map_clopenUpperStarLowerShriekAdjunction_unit_app
    (T : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((σ)^*[ModuleCat.{u + 1} Λ]).map ((clopenUpperStarLowerShriekAdjunction Λ σ).unit.app T) =
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ σ).unit.app
        (L((σ)^*[ModuleCat.{u + 1} Λ]).obj T) := by
  have h := (clopenUpperStarLowerShriekAdjunction Λ σ).left_triangle_components T
  rw [clopenUpperStarLowerShriekAdjunction_counit_app] at h
  rw [← cancel_mono (inv
    ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ σ).unit.app
    (L((σ)^*[ModuleCat.{u + 1} Λ]).obj T))), h, IsIso.hom_inv_id]
  rfl

variable {σ} in
/-- **Restrict to an open and closed piece, apply a map there, and extend by zero.** For an open
and closed immersion `σ : X ⟶ W` and a morphism `ψ : Lσ^* T₁ ⟶ Lσ^* T₂`, the morphism
`T₁ ⟶ Dσ_! Lσ^* T₁ ⟶ Dσ_! Lσ^* T₂ ⟶ T₂`, by the unit of `Lσ^* ⊣ Dσ_!` and the counit of
`Dσ_! ⊣ Lσ^*`. -/
noncomputable def clopenTransfer
    {T₁ T₂ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁ ⟶ L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₂) :
    T₁ ⟶ T₂ :=
  (clopenUpperStarLowerShriekAdjunction Λ σ).unit.app T₁ ≫
    D((σ)_!open[ModuleCat.{u + 1} Λ]).map ψ ≫
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ σ).counit.app T₂

/-- `clopenTransfer` is natural in both variables. -/
lemma clopenTransfer_comp
    {T₀ T₁ T₂ T₃ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (a : T₀ ⟶ T₁)
    (ψ : L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁ ⟶ L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₂)
    (b : T₂ ⟶ T₃) :
    clopenTransfer Λ (L((σ)^*[ModuleCat.{u + 1} Λ]).map a ≫ ψ ≫
      L((σ)^*[ModuleCat.{u + 1} Λ]).map b) = a ≫ clopenTransfer Λ ψ ≫ b := by
  simp only [clopenTransfer, Functor.map_comp, Category.assoc]
  rw [← Adjunction.counit_naturality,
    ← (clopenUpperStarLowerShriekAdjunction Λ σ).unit_naturality_assoc]

lemma clopenTransfer_comp_left
    {T₀ T₁ T₂ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (a : T₀ ⟶ T₁)
    (ψ : L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁ ⟶ L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₂) :
    clopenTransfer Λ (L((σ)^*[ModuleCat.{u + 1} Λ]).map a ≫ ψ) = a ≫ clopenTransfer Λ ψ := by
  simpa using clopenTransfer_comp Λ σ a ψ (𝟙 _)

lemma clopenTransfer_comp_right
    {T₁ T₂ T₃ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁ ⟶ L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₂)
    (b : T₂ ⟶ T₃) :
    clopenTransfer Λ (ψ ≫ L((σ)^*[ModuleCat.{u + 1} Λ]).map b) = clopenTransfer Λ ψ ≫ b := by
  simpa using clopenTransfer_comp Λ σ (𝟙 _) ψ b

/-- On the piece `X`, `clopenTransfer ψ` is `ψ`. -/
lemma leftDerivedUpperStar_map_clopenTransfer_self
    {T₁ T₂ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁ ⟶ L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₂) :
    L((σ)^*[ModuleCat.{u + 1} Λ]).map (clopenTransfer Λ ψ) = ψ := by
  simp only [clopenTransfer, Functor.map_comp,
    leftDerivedUpperStar_map_clopenUpperStarLowerShriekAdjunction_unit_app]
  rw [Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components, Category.comp_id]

-- the base change of the unit of `Lσ^* ⊣ Dσ_!` unfolds large derived functors
/-- **`clopenTransfer` commutes with base change**: for a cartesian square
`k ≫ σ = σ' ≫ h` of open and closed immersions `σ`, `σ'`, `Lh^*` of `clopenTransfer ψ` is
`clopenTransfer` of `ψ` pulled back along `k`, read through the square isomorphisms
`Lσ'^* Lh^* ≅ Lk^* Lσ^*`. -/
lemma leftDerivedUpperStar_map_clopenTransfer {X' W' : Scheme.{u}} {k : X' ⟶ X} {σ' : X' ⟶ W'}
    {h : W' ⟶ W} [IsOpenImmersion σ'] [IsClosedImmersion σ'] (hsq : IsPullback k σ' σ h)
    {T₁ T₂ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁ ⟶ L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₂) :
    L((h)^*[ModuleCat.{u + 1} Λ]).map (clopenTransfer Λ ψ) =
      clopenTransfer Λ ((derivedSquareUpperStarIso _ hsq.toCommSq).hom.app T₁ ≫
        L((k)^*[ModuleCat.{u + 1} Λ]).map ψ ≫
        (derivedSquareUpperStarIso _ hsq.toCommSq).inv.app T₂) := by
  -- the unit of `Lσ^* ⊣ Dσ_!` commutes with base change
  have e₂ : L((h)^*[ModuleCat.{u + 1} Λ]).map
      ((clopenUpperStarLowerShriekAdjunction Λ σ).unit.app T₁) ≫
        (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).inv.app
          (L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁) =
      (clopenUpperStarLowerShriekAdjunction Λ σ').unit.app
          (L((h)^*[ModuleCat.{u + 1} Λ]).obj T₁) ≫
        D((σ')_!open[ModuleCat.{u + 1} Λ]).map
          ((derivedSquareUpperStarIso _ hsq.toCommSq).hom.app T₁) := by
    apply ((clopenUpperStarLowerShriekAdjunction Λ σ').homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      clopenUpperStarLowerShriekAdjunction_counit_app,
      leftDerivedUpperStar_map_clopenUpperStarLowerShriekAdjunction_unit_app]
    have hJ := unit_map_derivedOpenImmersionLowerShriekBaseChangeIso' Λ hsq
      (L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁)
    have hn := (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) hsq.toCommSq).hom.naturality
      ((clopenUpperStarLowerShriekAdjunction Λ σ).unit.app T₁)
    have hn' :=
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ σ').unit.naturality
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) hsq.toCommSq).hom.app T₁)
    dsimp at hn hn' hJ ⊢
    rw [leftDerivedUpperStar_map_clopenUpperStarLowerShriekAdjunction_unit_app] at hn
    have hn2 : L((σ')^*[ModuleCat.{u + 1} Λ]).map (L((h)^*[ModuleCat.{u + 1} Λ]).map
        ((clopenUpperStarLowerShriekAdjunction Λ σ).unit.app T₁)) =
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) hsq.toCommSq).hom.app T₁ ≫
          L((k)^*[ModuleCat.{u + 1} Λ]).map
            ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ σ).unit.app
              (L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁)) ≫
          (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) hsq.toCommSq).inv.app _ := by
      rw [← cancel_mono ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
        hsq.toCommSq).hom.app _)]
      erw [hn]
      simp
    have hJ2 : L((k)^*[ModuleCat.{u + 1} Λ]).map
          ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ σ).unit.app
            (L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁)) ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) hsq.toCommSq).inv.app _ ≫
        L((σ')^*[ModuleCat.{u + 1} Λ]).map
          ((derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).inv.app
            (L((σ)^*[ModuleCat.{u + 1} Λ]).obj T₁)) =
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ σ').unit.app _ := by
      rw [← reassoc_of% hJ, ← Functor.map_comp, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      rfl
    rw [hn2, Category.assoc, Category.assoc, reassoc_of% hJ2, IsIso.hom_inv_id,
      ← reassoc_of% hn', IsIso.hom_inv_id]
  -- the counit of `Dσ_! ⊣ Lσ^*` commutes with base change
  have e₁ := leftDerivedUpperStar_map_counit_derivedOpenImmersionLowerShriek Λ hsq T₂
  have hj :=
    (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).inv.naturality ψ
  simp only [clopenTransfer, Functor.map_comp, Category.assoc]
  rw [e₁]
  dsimp at hj ⊢
  rw [reassoc_of% hj, reassoc_of% e₂]

end Clopen

end Etale

end AlgebraicGeometry
