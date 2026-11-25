/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCupProduct
public import WeilConjectures.CategoryTheory.Monoidal.ProjectionMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal

/-!
# Associativity of the projection map for `Rf_!`

For `f : X ⟶ Y` with a compactification `c`, the projection map
`PF_{K, L} : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` of
`AlgebraicGeometry.Etale.projectionMapOfCompactification` is compatible with the associativity
of the derived tensor products: for `K` on `X` and `L, N` on `Y` the square
```
(Rf_!K ⊗ᴸ L) ⊗ᴸ N --PF ▷ N--> Rf_!(K ⊗ᴸ Lf^*L) ⊗ᴸ N --PF--> Rf_!((K ⊗ᴸ Lf^*L) ⊗ᴸ Lf^*N)
        | α                                                            | Rf_! α
        v                                                              v
Rf_!K ⊗ᴸ (L ⊗ᴸ N) ----PF----> Rf_!(K ⊗ᴸ Lf^*(L ⊗ᴸ N)) --Rf_!(K ◁ δ)--> Rf_!(K ⊗ᴸ (Lf^*L ⊗ᴸ Lf^*N))
```
commutes, where `δ` is the tensor comparison of `Lf^*`
(`AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`).

This is the associativity of the projection map of a composite
(`CategoryTheory.Adjunction.compProjectionMap_associativity`) applied to `Rg_*` and the extension
by zero `i_!`, using the monoidal coherence of their ingredients proved in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal`.

It is the formal input of the compatibility of the projection formula with finite reduction
of the coefficients, blueprint `sk-prop-sf-pf-reduction`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The projection map `PF_c` is the projection map of the composite `Rg_* ∘ i_!`
(`CategoryTheory.Adjunction.compProjectionMap`). -/
lemma projectionMapOfCompactification_app_app_eq_compProjectionMap
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c).app K).app L =
      (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap
        (leftDerivedUpperStarTensorComparison A c.g) D((c.i)_!open[A])
        (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
        (fun L ↦ (leftDerivedUpperStarCompactificationIso A c).hom.app L) K L :=
  rfl

/-- **Associativity of the projection map for `Rf_!`.** For a compactification `c` of
`f : X ⟶ Y`, `K` on `X` and `L, N` on `Y`, the projection map
`PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` of
`AlgebraicGeometry.Etale.projectionMapOfCompactification` makes the square
```
(Rf_!K ⊗ᴸ L) ⊗ᴸ N --PF ▷ N--> Rf_!(K ⊗ᴸ Lf^*L) ⊗ᴸ N --PF--> Rf_!((K ⊗ᴸ Lf^*L) ⊗ᴸ Lf^*N)
        | α                                                            | Rf_! α
        v                                                              v
Rf_!K ⊗ᴸ (L ⊗ᴸ N) ----PF----> Rf_!(K ⊗ᴸ Lf^*(L ⊗ᴸ N)) --Rf_!(K ◁ δ)--> Rf_!(K ⊗ᴸ (Lf^*L ⊗ᴸ Lf^*N))
```
commute, `δ` being the tensor comparison of `Lf^*`. -/
theorem projectionMapOfCompactification_assoc
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c).app K).app L ▷ N ≫
        ((projectionMapOfCompactification A c).app (K ⊗ L((f)^*[A]).obj L)).app N ≫
        Rf_!(c)[A].map (α_ K (L((f)^*[A]).obj L) (L((f)^*[A]).obj N)).hom =
      (α_ ((Rf_!(c)[A]).obj K) L N).hom ≫
        ((projectionMapOfCompactification A c).app K).app (L ⊗ N) ≫
        Rf_!(c)[A].map (K ◁ ((leftDerivedUpperStarTensorComparison A f).app L).app N) := by
  rw [projectionMapOfCompactification_app_app_eq_compProjectionMap,
    projectionMapOfCompactification_app_app_eq_compProjectionMap,
    projectionMapOfCompactification_app_app_eq_compProjectionMap]
  exact (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap_associativity _
    (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A c.i).app N).app N')
    (fun L L' ↦ ((leftDerivedUpperStarTensorComparison A f).app L).app L')
    (leftDerivedUpperStarTensorComparison_associativity A c.g)
    (fun x N ↦ derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_left A c.i x N)
    (fun K _ _ y ↦ derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_right A c.i K y)
    (derivedOpenImmersionLowerShriekProjectionIso_inv_associativity A c.i)
    (leftDerivedUpperStarCompactificationIso_hom_app_tensor A c) K L N

end AlgebraicGeometry.Etale
