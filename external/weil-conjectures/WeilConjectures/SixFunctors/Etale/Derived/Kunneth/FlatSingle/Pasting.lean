/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit

/-!
# The base change map for a pushforward tensored with a complex: unit and pasting

For a commutative square `h ≫ f' = e ≫ g` of schemes, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)`

is, at the unit `M = Λ`, the derived base change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F`
(`AlgebraicGeometry.Etale.derivedBaseChangeMap`), up to the unitors
(`AlgebraicGeometry.Etale.tensorBaseChangeMap_tensorUnit`). For two squares pasted horizontally,
the base change map of the outer square is the base change map of the right square followed by
the base change map of the left square (`AlgebraicGeometry.Etale.tensorBaseChangeMap_paste`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

/-- The base change map for a pushforward tensored with a complex is the transpose of the tensor
comparison of `Lh^*` followed by `Lh^* M ⊗ᴸ -` applied to
`AlgebraicGeometry.Etale.tensorBaseChangeCounitApp`. -/
lemma tensorBaseChangeMap_eq {X' S' T Y : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T)
    (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    tensorBaseChangeMap A h e f' g w M F =
      (derivedUpperStarLowerStarAdjunction A h).homEquiv _ _
        (((leftDerivedUpperStarTensorComparison A h).app M).app _ ≫
          ((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M)).map (tensorBaseChangeCounitApp A h e f' g w F)) :=
  rfl

omit [UpperStarPreservesFlat A] in
/-- The morphism `Lh^* Lf'^* Rg_* F ⟶ Le^* F` of the base change map for a pushforward tensored
with a complex is the transpose of the derived base change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F`. -/
lemma tensorBaseChangeCounitApp_eq {X' S' T Y : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T)
    (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    tensorBaseChangeCounitApp A h e f' g w F =
      L((h)^*[A]).map ((derivedBaseChangeMap A (CommSq.mk w.symm)).app F) ≫
        (derivedUpperStarLowerStarAdjunction A h).counit.app _ := by
  have key (d : Y ⟶ S') (h₁ : d = h ≫ f') (h₂ : d = e ≫ g) :
      (leftDerivedUpperStarComp A h f' d h₁).inv.app (R((g)_*[A]).obj F) ≫
        (leftDerivedUpperStarComp A e g d h₂).hom.app (R((g)_*[A]).obj F) =
      (leftDerivedUpperStarComp A h f').inv.app (R((g)_*[A]).obj F) ≫
        (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app (R((g)_*[A]).obj F) := by
    subst h₁
    rfl
  rw [derivedUpperStar_map_derivedBaseChangeMap_app_counit]
  simp only [tensorBaseChangeCounitApp, derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [← reassoc_of% (key (e ≫ g) w.symm rfl)]

/-- **The base change map at the unit**: for a commutative square `h ≫ f' = e ≫ g`, the base change
map `Λ ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Λ ⊗ᴸ Le^* F)` is the derived base change map
`Lf'^* Rg_* F ⟶ Rh_* Le^* F`, up to the left unitors and the identification `Lh^* Λ ≅ Λ`. -/
lemma tensorBaseChangeMap_tensorUnit {X' S' T Y : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T)
    (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    tensorBaseChangeMap A h e f' g w (𝟙_ _) F ≫
        R((h)_*[A]).map ((leftDerivedUpperStarUnitIso A h).hom ▷ L((e)^*[A]).obj F ≫
          (λ_ _).hom) =
      (λ_ _).hom ≫ (derivedBaseChangeMap A (CommSq.mk w.symm)).app F := by
  apply ((derivedUpperStarLowerStarAdjunction A h).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm,
    tensorBaseChangeMap_eq, Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
    ← tensorBaseChangeCounitApp_eq A h e f' g w]
  dsimp only [derivedTensor_obj_map]
  rw [Category.assoc, whisker_exchange_assoc, leftUnitor_naturality,
    ← reassoc_of% (leftDerivedUpperStarTensorComparison_leftUnitor_hom A h _)]
  rfl

/-- The base change map at the unit is an isomorphism if the derived base change map is. -/
lemma isIso_tensorBaseChangeMap_tensorUnit {X' S' T Y : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T)
    (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A))
    (hBC : IsIso ((derivedBaseChangeMap A (CommSq.mk w.symm)).app F)) :
    IsIso (tensorBaseChangeMap A h e f' g w (𝟙_ _) F) := by
  have : IsIso (tensorBaseChangeMap A h e f' g w (𝟙_ _) F ≫
      R((h)_*[A]).map ((leftDerivedUpperStarUnitIso A h).hom ▷ L((e)^*[A]).obj F ≫
        (λ_ _).hom)) := by
    rw [tensorBaseChangeMap_tensorUnit]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (R((h)_*[A]).map
    ((leftDerivedUpperStarUnitIso A h).hom ▷ L((e)^*[A]).obj F ≫ (λ_ _).hom))

-- the pasting computation in the derived category is expensive to elaborate
/-- **Pasting of base change maps**: for two commutative squares pasted horizontally,

```
  Y --e₁--> T₁ --e₂--> T
  |         |          |
  h         g₁         g
  v         v          v
  X' --a--> S₁ --b---> S'
```

the base change map of the outer square at `(M, F)`, followed by `Le₁^* Le₂^* ≅ L(e₁ ≫ e₂)^*`, is
`M ⊗ᴸ -` applied to `L(a ≫ b)^* ≅ La^* Lb^*` and to `La^*` of the derived base change map
`Lb^* Rg_* F ⟶ Rg₁_* Le₂^* F` of the right square, followed by the base change map of the left
square at `(M, Le₂^* F)`. -/
lemma tensorBaseChangeMap_paste {X' S₁ S' T₁ T Y : Scheme.{u}} (h : Y ⟶ X') (e₁ : Y ⟶ T₁)
    (a : X' ⟶ S₁) (g₁ : T₁ ⟶ S₁) (wL : h ≫ a = e₁ ≫ g₁) (e₂ : T₁ ⟶ T) (b : S₁ ⟶ S')
    (g : T ⟶ S') (wR : g₁ ≫ b = e₂ ≫ g) (w : h ≫ a ≫ b = (e₁ ≫ e₂) ≫ g)
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    tensorBaseChangeMap A h (e₁ ≫ e₂) (a ≫ b) g w M F ≫
        R((h)_*[A]).map (((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M)).map
          ((leftDerivedUpperStarComp A e₁ e₂).hom.app F)) =
      ((-⊗ᴸ-(X')[A]).obj M).map ((leftDerivedUpperStarComp A a b).hom.app (R((g)_*[A]).obj F) ≫
          L((a)^*[A]).map ((derivedBaseChangeMap A (CommSq.mk wR.symm)).app F)) ≫
        tensorBaseChangeMap A h e₁ a g₁ wL M (L((e₂)^*[A]).obj F) := by
  apply ((derivedUpperStarLowerStarAdjunction A h).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm,
    tensorBaseChangeMap_eq, tensorBaseChangeMap_eq, Equiv.symm_apply_apply]
  erw [Equiv.symm_apply_apply]
  have hn := ((leftDerivedUpperStarTensorComparison A h).app M).naturality
    ((leftDerivedUpperStarComp A a b).hom.app (R((g)_*[A]).obj F) ≫
      L((a)^*[A]).map ((derivedBaseChangeMap A (CommSq.mk wR.symm)).app F))
  erw [reassoc_of% hn]
  rw [Category.assoc]
  congr 1
  have hc : tensorBaseChangeCounitApp A h (e₁ ≫ e₂) (a ≫ b) g w F ≫
      (leftDerivedUpperStarComp A e₁ e₂).hom.app F =
      L((h)^*[A]).map ((leftDerivedUpperStarComp A a b).hom.app (R((g)_*[A]).obj F) ≫
        L((a)^*[A]).map ((derivedBaseChangeMap A (CommSq.mk wR.symm)).app F)) ≫
        tensorBaseChangeCounitApp A h e₁ a g₁ wL (L((e₂)^*[A]).obj F) := by
    -- the counit level
    have hBC := derivedUpperStar_map_derivedBaseChangeMap_app_counit A (CommSq.mk wR.symm) F
    have hcoh : (leftDerivedUpperStarComp A h (a ≫ b)).inv.app (R((g)_*[A]).obj F) ≫
        (leftDerivedUpperStarComp A (e₁ ≫ e₂) g (h ≫ a ≫ b) w).hom.app (R((g)_*[A]).obj F) ≫
        (leftDerivedUpperStarComp A e₁ e₂).hom.app (L((g)^*[A]).obj (R((g)_*[A]).obj F)) =
        L((h)^*[A]).map ((leftDerivedUpperStarComp A a b).hom.app (R((g)_*[A]).obj F)) ≫
          (leftDerivedUpperStarComp A h a).inv.app _ ≫
          (leftDerivedUpperStarComp A e₁ g₁ (h ≫ a) wL).hom.app _ ≫
          L((e₁)^*[A]).map ((derivedSquareUpperStarIso A (CommSq.mk wR.symm)).hom.app
            (R((g)_*[A]).obj F)) := by
      rw [map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app_assoc A h a b
        (h ≫ a) (a ≫ b) (h ≫ a ≫ b) rfl rfl (Category.assoc _ _ _).symm]
      simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.map_comp]
      rw [leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app_assoc A e₁ g₁ b
        (h ≫ a) (e₂ ≫ g) (h ≫ a ≫ b) wL wR.symm (Category.assoc _ _ _).symm,
        Iso.hom_inv_id_app_assoc,
        leftDerivedUpperStarComp_assoc'_app A e₁ e₂ g (e₁ ≫ e₂) (e₂ ≫ g) (h ≫ a ≫ b) rfl rfl w]
    simp only [tensorBaseChangeCounitApp, Functor.map_comp, Category.assoc]
    erw [(leftDerivedUpperStarComp A e₁ e₂).hom.naturality
      ((derivedUpperStarLowerStarAdjunction A g).counit.app F)]
    erw [reassoc_of% hcoh]
    have n1 := (leftDerivedUpperStarComp A h a).inv.naturality
      ((derivedBaseChangeMap A (CommSq.mk wR.symm)).app F)
    have n2 := (leftDerivedUpperStarComp A e₁ g₁ (h ≫ a) wL).hom.naturality
      ((derivedBaseChangeMap A (CommSq.mk wR.symm)).app F)
    simp only [Functor.comp_map] at n1 n2 ⊢
    dsimp only [Functor.comp_obj] at n1 n2 hBC
    rw [reassoc_of% n1]
    simp only [reassoc_of% n2]
    have hBC' := congrArg (fun φ ↦ L((e₁)^*[A]).map φ) hBC
    simp only [Functor.map_comp] at hBC'
    simp only [hBC']
  rw [← Functor.map_comp, hc, Functor.map_comp]
  rfl

end Etale

end AlgebraicGeometry
