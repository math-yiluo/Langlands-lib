/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift

/-!
# The projection map commutes with shifts

For `f : X ⟶ Y` with a compactification `c = (X ⟶[i] Z ⟶[g] Y)` and a fixed `K` in
`D(X_ét)`, the projection map `PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)`
(`AlgebraicGeometry.Etale.projectionMapOfCompactification`) commutes with the shifts in `L`.
Each of its ingredients does:

* the projection map `Rg_*M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^*L)` of the derived pushforward, built from the
  adjunction `Lg^* ⊣ Rg_*` and the tensor comparison of `Lg^*`, which commute with shifts;
* the projection formula `i_!(K ⊗ᴸ Li^*M) ≅ i_!K ⊗ᴸ M` for the open immersion `i`, built from
  the adjunction `D(i_!) ⊣ D(i^*)` and the tensor comparison of `Li^*`;
* the composition isomorphism `Lg^* ⋙ Li^* ≅ Lf^*` of derived pullbacks.

## Main results

- `AlgebraicGeometry.Etale.commShift_rightDerivedLowerStarProjectionMap_app`
- `AlgebraicGeometry.Etale.commShift_derivedOpenImmersionLowerShriekProjectionIso_inv_app`
- `AlgebraicGeometry.Etale.commShift_projectionMapOfCompactification_app`
- `AlgebraicGeometry.Etale.commShift_projectionMap_app`: the projection map
  `Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` commutes with the shifts in `L`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

/-- The image of a morphism under the derived tensor product commutes with the shifts in the
second variable. -/
instance commShift_derivedTensor_map {X : Scheme.{u}}
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K') :
    NatTrans.CommShift ((-⊗ᴸ-(X)[A]).map φ) ℤ :=
  inferInstanceAs (NatTrans.CommShift
    ((curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology A))).map φ) ℤ)

variable [Etale.UpperStarPreservesFlat A]

/-- The projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` of the derived pushforward commutes
with the shifts in `L`. -/
instance commShift_rightDerivedLowerStarProjectionMap_app {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    NatTrans.CommShift (F₁ := (-⊗ᴸ-(Y)[A]).obj (R((p)_*[A]).obj M))
      (F₂ := (L((p)^*[A]) ⋙ (-⊗ᴸ-(X)[A]).obj M) ⋙ R((p)_*[A]))
      ((rightDerivedLowerStarProjectionMap A p).app M) ℤ :=
  Adjunction.commShift_rightAdjointProjectionMap_app (derivedUpperStarLowerStarAdjunction A p)
    (leftDerivedUpperStarTensorComparison A p) M

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The derived adjunction `D(j_!) ⊣ D(j^*)` along an open immersion commutes with the
shifts. -/
instance commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).CommShift ℤ :=
  inferInstanceAs
    ((openImmersionLowerShriekUpperStarAdjunction A j).mapDerivedCategoryAdjunction.CommShift ℤ)

/-- The isomorphism `j^*K ⊗ᴸ Lj^*M ≅ j^*(K ⊗ᴸ M)` commutes with the shifts in `M`. -/
instance commShift_mapDerivedCategoryUpperStarDerivedTensorIso_hom_app
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    NatTrans.CommShift (F₁ := L((j)^*[A]) ⋙ (-⊗ᴸ-(U)[A]).obj (D((j)^*[A]).obj K))
      (F₂ := (-⊗ᴸ-(X)[A]).obj K ⋙ D((j)^*[A]))
      ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app K) ℤ := by
  let eK : (-⊗ᴸ-(X)[A]).obj K ⋙ L((j)^*[A]) ≅
      L((j)^*[A]) ⋙ (-⊗ᴸ-(U)[A]).obj (L((j)^*[A]).obj K) :=
    (leftDerivedUpperStarTensorNatIso A j).app K
  have : NatTrans.CommShift eK.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A j K) ℤ)
  have e : (mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app K =
      Functor.whiskerLeft L((j)^*[A])
        ((-⊗ᴸ-(U)[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app K)) ≫
      eK.inv ≫
      Functor.whiskerLeft ((-⊗ᴸ-(X)[A]).obj K)
        (leftDerivedUpperStarIsoMapDerivedCategory A j).hom := by
    ext M
    simp [mapDerivedCategoryUpperStarDerivedTensorIso, eK]
  rw [e]
  infer_instance

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The projection formula `j_!K ⊗ᴸ M ≅ j_!(K ⊗ᴸ Lj^*M)` for an open immersion `j` commutes
with the shifts in `M`. -/
instance commShift_derivedOpenImmersionLowerShriekProjectionIso_inv_app
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    NatTrans.CommShift (F₁ := (-⊗ᴸ-(X)[A]).obj (D((j)_!open[A]).obj K))
      (F₂ := (L((j)^*[A]) ⋙ (-⊗ᴸ-(U)[A]).obj K) ⋙ D((j)_!open[A]))
      ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K) ℤ := by
  let eK : (L((j)^*[A]) ⋙ (-⊗ᴸ-(U)[A]).obj K) ⋙ D((j)_!open[A]) ≅
      (-⊗ᴸ-(X)[A]).obj (D((j)_!open[A]).obj K) :=
    (derivedOpenImmersionLowerShriekProjectionIso A j).app K
  have : NatTrans.CommShift eK.hom ℤ :=
    Adjunction.commShift_projectionMap_app (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
      L((j)^*[A]) (-⊗ᴸ-(U)[A]) (-⊗ᴸ-(X)[A]) (mapDerivedCategoryUpperStarDerivedTensorIso A j).hom K
  exact NatTrans.CommShift.of_iso_inv eK ℤ

end OpenImmersion

section Compactification

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The isomorphism `Lg^* ⋙ Li^* ≅ Lf^*` for a compactification `(i, g)` of `f` commutes with
the shifts. -/
instance commShift_leftDerivedUpperStarCompactificationIso_hom (c : Compactification f) :
    NatTrans.CommShift (leftDerivedUpperStarCompactificationIso A c).hom ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarComp A c.i c.g (c.i ≫ c.g) rfl).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  have h : ∀ (h₁ h₂ : X ⟶ Y) (e : h₁ = h₂),
      NatTrans.CommShift (eqToIso (congrArg (fun h : X ⟶ Y ↦ L((h)^*[A])) e)).hom ℤ := by
    rintro h₁ _ rfl
    exact inferInstanceAs (NatTrans.CommShift (𝟙 L((h₁)^*[A])) ℤ)
  have := h _ _ c.comm.symm
  dsimp only [leftDerivedUpperStarCompactificationIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The projection map `PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)` for a compactification `c`
commutes with the shifts in `L`. -/
instance commShift_projectionMapOfCompactification_app (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    NatTrans.CommShift (F₁ := (-⊗ᴸ-(Y)[A]).obj ((Rf_!(c)[A]).obj K))
      (F₂ := (L((f)^*[A]) ⋙ (-⊗ᴸ-(X)[A]).obj K) ⋙ Rf_!(c)[A])
      ((projectionMapOfCompactification A c).app K) ℤ := by
  let τ₁ : (-⊗ᴸ-(Y)[A]).obj ((Rf_!(c)[A]).obj K) ⟶
      (L((c.g)^*[A]) ⋙ (-⊗ᴸ-(c.Z)[A]).obj (D((c.i)_!open[A]).obj K)) ⋙ R((c.g)_*[A]) :=
    (rightDerivedLowerStarProjectionMap A c.g).app (D((c.i)_!open[A]).obj K)
  have : NatTrans.CommShift τ₁ ℤ :=
    commShift_rightDerivedLowerStarProjectionMap_app A c.g (D((c.i)_!open[A]).obj K)
  let τ₂ : (-⊗ᴸ-(c.Z)[A]).obj (D((c.i)_!open[A]).obj K) ⟶
      (L((c.i)^*[A]) ⋙ (-⊗ᴸ-(X)[A]).obj K) ⋙ D((c.i)_!open[A]) :=
    (derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K
  have : NatTrans.CommShift τ₂ ℤ :=
    commShift_derivedOpenImmersionLowerShriekProjectionIso_inv_app A c.i K
  let τ₃ : L((c.g)^*[A]) ⋙ L((c.i)^*[A]) ⟶ L((f)^*[A]) :=
    (leftDerivedUpperStarCompactificationIso A c).hom
  have : NatTrans.CommShift τ₃ ℤ := commShift_leftDerivedUpperStarCompactificationIso_hom A c
  have e : (projectionMapOfCompactification A c).app K =
      τ₁ ≫ Functor.whiskerRight (Functor.whiskerLeft L((c.g)^*[A]) τ₂) R((c.g)_*[A]) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L((c.g)^*[A]) (Functor.associator _ _ _).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv
        (D((c.i)_!open[A]) ⋙ R((c.g)_*[A])) ≫
      Functor.whiskerRight (Functor.whiskerRight τ₃ ((-⊗ᴸ-(X)[A]).obj K))
        (D((c.i)_!open[A]) ⋙ R((c.g)_*[A])) := by
    ext L
    simp [projectionMapOfCompactification_app_app, τ₁, τ₂, τ₃]
  rw [e]
  infer_instance

/-- The projection map `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` commutes with the shifts in `L`. -/
instance commShift_projectionMap_app [HasCompactification f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    NatTrans.CommShift (F₁ := (-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj K))
      (F₂ := L((f)^*[A]) ⋙ (-⊗ᴸ-(X)[A]).obj K ⋙ R(f)_![A]) ((projectionMap A f).app K) ℤ := by
  let τ : (-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj K) ⟶
      (L((f)^*[A]) ⋙ (-⊗ᴸ-(X)[A]).obj K) ⋙ R(f)_![A] := (projectionMap A f).app K
  have : NatTrans.CommShift τ ℤ := commShift_projectionMapOfCompactification_app A _ K
  have e : τ ≫ (Functor.associator _ _ _).hom = (projectionMap A f).app K := by
    ext L
    simp [τ]
  rw [← e]
  infer_instance

end Compactification

end Etale

end AlgebraicGeometry
