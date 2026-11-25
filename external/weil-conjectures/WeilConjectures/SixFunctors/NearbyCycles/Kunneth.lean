/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange

/-!

# The Künneth map of nearby cycles

Let `Ψ = Li^* Rj_* Lε^*` be the nearby cycles of a model
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nearbyCycles`). This file constructs,
on the unbounded derived categories of module objects,

* the *lax tensor map* `μ_j : Rj_* A ⊗ Rj_* B ⟶ Rj_* (A ⊗ B)` of a derived pushforward, the
  adjoint of the tensor product of the counits of `Lj^* ⊣ Rj_*`
  (`ProEtale.CondensedRing.lowerStarTensorMap'`);
* the *lax tensor map* `μ_Ψ : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` of nearby cycles, the restriction to the
  special fibre of `μ_j` (`NearbyCyclesModel.tensorMap`);
* for two morphisms of models `φ₁ : P ⟶ M` over `f₁` and `φ₂ : P ⟶ N` over `f₂`, the *Künneth
  map* (`NearbyCyclesModel.kunnethMap`, blueprint
  `proposition-external-kunneth-formula-nearby-cycles`)
  ```
  Π_{A,B} : Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B ⟶ Ψ_P (Lf₁^* A ⊗ Lf₂^* B),
  ```
  the tensor product of the pullback exchanges `α_{φ₁}`, `α_{φ₂}` followed by `μ_Ψ`. When `P` is
  the product of `M` and `N` over the trait, `f₁, f₂` and `f₁', f₂'` are the projections and both
  sides are the external products `Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)`: this is the map `Π_{L,M}` of
  the blueprint, the restriction to the special fibre of the map
  `Rj_{X*} L ⊠ Rj_{Y*} M ⟶ Rj_{X × Y *} (L ⊠ M)` defined by the pullback exchanges and the lax
  tensor map of direct image.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section LowerStar

variable {U T : Scheme.{u}} (j : U ⟶ T)

/-- The *lax tensor map* `μ_j : Rj_* A ⊗ Rj_* B ⟶ Rj_* (A ⊗ B)` of the derived pushforward on
module objects: the adjoint for `Lj^* ⊣ Rj_*` of
```
Lj^* (Rj_* A ⊗ Rj_* B) ≅ Lj^* Rj_* A ⊗ Lj^* Rj_* B --ε ⊗ ε--> A ⊗ B,
```
the monoidal structure of `Lj^*` followed by the counits. -/
noncomputable def lowerStarTensorMap'
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    R((j)_*⟦Λ⟧).obj A ⊗ R((j)_*⟦Λ⟧).obj B ⟶ R((j)_*⟦Λ⟧).obj (A ⊗ B) :=
  (derivedUpperStarLowerStarAdjunction Λ j).homEquiv _ _
    (Functor.OplaxMonoidal.δ L((j)^*⟦Λ⟧) _ _ ≫
      ((derivedUpperStarLowerStarAdjunction Λ j).counit.app A ⊗ₘ
        (derivedUpperStarLowerStarAdjunction Λ j).counit.app B))

/-- The adjoint of the lax tensor map of `Rj_*` is the tensor product of the counits. -/
lemma lowerStarTensorMap'_comp_counit
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    L((j)^*⟦Λ⟧).map (lowerStarTensorMap' Λ j A B) ≫
        (derivedUpperStarLowerStarAdjunction Λ j).counit.app (A ⊗ B) =
      Functor.OplaxMonoidal.δ L((j)^*⟦Λ⟧) _ _ ≫
        ((derivedUpperStarLowerStarAdjunction Λ j).counit.app A ⊗ₘ
          (derivedUpperStarLowerStarAdjunction Λ j).counit.app B) := by
  exact ((derivedUpperStarLowerStarAdjunction Λ j).homEquiv_counit (g := _)).symm.trans
    (((derivedUpperStarLowerStarAdjunction Λ j).homEquiv _ _).symm_apply_apply _)

/-- The lax tensor map of the derived pushforward is natural. -/
lemma lowerStarTensorMap'_natural
    {A A' B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))} (x : A ⟶ A') (y : B ⟶ B') :
    (R((j)_*⟦Λ⟧).map x ⊗ₘ R((j)_*⟦Λ⟧).map y) ≫ lowerStarTensorMap' Λ j A' B' =
      lowerStarTensorMap' Λ j A B ≫ R((j)_*⟦Λ⟧).map (x ⊗ₘ y) := by
  let := (derivedUpperStarLowerStarAdjunction Λ j).rightAdjointLaxMonoidal
  have := Functor.LaxMonoidal.μ_natural R((j)_*⟦Λ⟧) x y
  simp only [Adjunction.rightAdjointLaxMonoidal_μ] at this
  exact this

section Kunneth

variable {X X₁ Y Y₁ Z Z₁ : Scheme.{u}} {f₁ : Z ⟶ X} {f₂ : Z ⟶ Y} {g : X ⟶ X₁} {h : Y ⟶ Y₁}
  {k : Z ⟶ Z₁} {e₁ : Z₁ ⟶ X₁} {e₂ : Z₁ ⟶ Y₁}

/-- The *ordinary Künneth map* `κ_{A,B} : Le₁^* Rg_* A ⊗ Le₂^* Rh_* B ⟶ Rk_* (Lf₁^* A ⊗ Lf₂^* B)`
of two commutative squares `f₁ ≫ g = k ≫ e₁` and `f₂ ≫ h = k ≫ e₂` (blueprint
`lemma-kunneth-one-identity-factor--1`, for the squares of a product `f × g`): the tensor product of
the base change morphisms followed by the lax tensor map of `Rk_*`. -/
noncomputable def lowerStarKunnethMap' (sq₁ : CommSq f₁ k g e₁) (sq₂ : CommSq f₂ k h e₂)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    L((e₁)^*⟦Λ⟧).obj (R((g)_*⟦Λ⟧).obj A) ⊗ L((e₂)^*⟦Λ⟧).obj (R((h)_*⟦Λ⟧).obj B) ⟶
      R((k)_*⟦Λ⟧).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) :=
  ((baseChangeMap Λ sq₁).app A ⊗ₘ (baseChangeMap Λ sq₂).app B) ≫ lowerStarTensorMap' Λ k _ _

end Kunneth

end LowerStar

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

/-- The *lax tensor map* `μ_Ψ : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` of the nearby cycles `Ψ = Li^* Rj_* Lε^*`:
the monoidal structure of `Li^*`, then `Li^*` of the lax tensor map `μ_j` of `Rj_*`, and finally
`Li^* Rj_*` of the monoidal structure of `Lε^*`. -/
noncomputable def tensorMap
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (M.nearbyCycles Λ).obj A ⊗ (M.nearbyCycles Λ).obj B ⟶ (M.nearbyCycles Λ).obj (A ⊗ B) :=
  Functor.LaxMonoidal.μ L((M.i)^*⟦Λ⟧) _ _ ≫
    L((M.i)^*⟦Λ⟧).map (lowerStarTensorMap' Λ M.j _ _ ≫
      R((M.j)_*⟦Λ⟧).map (Functor.LaxMonoidal.μ L((M.ε)^*⟦Λ⟧) A B))

private lemma tensorMap_natural_aux {C D T S : Type*} [Category C] [Category D] [Category T]
    [Category S] [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory T]
    [MonoidalCategory S] {E : C ⥤ D} {R : D ⥤ T} {I : T ⥤ S} [E.LaxMonoidal] [I.LaxMonoidal]
        (μR : ∀ U V, R.obj U ⊗ R.obj V ⟶ R.obj (U ⊗ V))
    (hμR : ∀ {U U' V V' : D} (x : U ⟶ U') (y : V ⟶ V'),
      (R.map x ⊗ₘ R.map y) ≫ μR U' V' = μR U V ≫ R.map (x ⊗ₘ y))
    {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B') :
    ((E ⋙ R ⋙ I).map x ⊗ₘ (E ⋙ R ⋙ I).map y) ≫ Functor.LaxMonoidal.μ I _ _ ≫
        I.map (μR _ _ ≫ R.map (Functor.LaxMonoidal.μ E A' B')) =
      (Functor.LaxMonoidal.μ I _ _ ≫ I.map (μR _ _ ≫ R.map (Functor.LaxMonoidal.μ E A B))) ≫
        (E ⋙ R ⋙ I).map (x ⊗ₘ y) := by
  simp only [Functor.comp_map, Functor.LaxMonoidal.μ_natural_assoc, ← I.map_comp,
    Category.assoc, ← R.map_comp]
  rw [reassoc_of% (hμR (E.map x) (E.map y)), ← R.map_comp, Functor.LaxMonoidal.μ_natural]

/-- The lax tensor map of nearby cycles is natural. -/
lemma tensorMap_natural
    {A A' B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (x : A ⟶ A') (y : B ⟶ B') :
    ((M.nearbyCycles Λ).map x ⊗ₘ (M.nearbyCycles Λ).map y) ≫ M.tensorMap Λ A' B' =
      M.tensorMap Λ A B ≫ (M.nearbyCycles Λ).map (x ⊗ₘ y) :=
  tensorMap_natural_aux (E := L((M.ε)^*⟦Λ⟧)) (I := L((M.i)^*⟦Λ⟧))
    (lowerStarTensorMap' Λ M.j) (fun x y ↦ lowerStarTensorMap'_natural Λ M.j x y) x y

variable {Y Y' Z Z' : Scheme.{u}} {M} {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

/-- The **Künneth map of nearby cycles** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, the map `Π_{L,M}`): for morphisms of models
`φ₁ : P ⟶ M` over `f₁, f₁'` and `φ₂ : P ⟶ N` over `f₂, f₂'`,
```
Π_{A,B} : Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B ⟶ Ψ_P (Lf₁^* A) ⊗ Ψ_P (Lf₂^* B) ⟶ Ψ_P (Lf₁^* A ⊗ Lf₂^* B),
```
the tensor product of the pullback exchanges `α_{φ₁}(A)` and `α_{φ₂}(B)` followed by the lax
tensor map `μ_Ψ` of `Ψ_P`. For the product `P` of `M` and `N` over the trait, with the
projections, it is the map `Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)`. -/
noncomputable def kunnethMap (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    L((f₁')^*⟦Λ⟧).obj ((M.nearbyCycles Λ).obj A) ⊗ L((f₂')^*⟦Λ⟧).obj ((N.nearbyCycles Λ).obj B) ⟶
      (P.nearbyCycles Λ).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) :=
  ((φ₁.pullbackExchange Λ).app A ⊗ₘ (φ₂.pullbackExchange Λ).app B) ≫ P.tensorMap Λ _ _

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
