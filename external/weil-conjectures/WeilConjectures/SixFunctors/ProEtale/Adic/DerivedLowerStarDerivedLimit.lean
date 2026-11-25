/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# Derived pushforward commutes with derived limits

A derived limit of a tower `(Kₙ, fₙ)` in a triangulated category is the first vertex `L` of a
distinguished triangle `L ⟶ ∏ Kₙ ──1 - t──▶ ∏ Kₙ ⟶ L[1]` (`CategoryTheory.IsDerivedLimitTriangle`,
`def-weil-derived-limit`). A triangulated functor preserving countable products sends such a
triangle to a triangle of the same kind (`CategoryTheory.Functor.isDerivedLimitTriangle_map`),
i.e. it commutes with derived limits: `Φ (R lim Kₙ) = R lim Φ Kₙ`.

The derived pushforward `Rg_*` of pro-étale sheaves is a right adjoint
(`AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction`), so it preserves products,
and it is triangulated; hence `Rg_* (R lim Kₙ) = R lim Rg_* Kₙ`
(`AlgebraicGeometry.ProEtale.isDerivedLimitTriangle_rightDerivedLowerStar`), the formal input
`Rf_* R lim = R lim Rf_*` of the passage from the finite levels `ℤ/ℓⁿ` to `ℤ_ℓ` (Stacks 08U1,
blueprint `lem-pc-derived-functor-commutes-derived-limit`).
-/

@[expose] public section

universe u u' v v' w w'

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A triangulated functor preserving countable products commutes with derived limits**: it
sends a derived limit triangle `L ⟶ ∏ Kₙ ──1 - t──▶ ∏ Kₙ ⟶ L[1]` of a tower to a derived limit
triangle of the image tower, after identifying `Φ (∏ Kₙ)` with `∏ Φ Kₙ` compatibly with the
projections (Stacks 08U1). -/
theorem isDerivedLimitTriangle_map (Φ : C ⥤ D) [Φ.CommShift ℤ] [Φ.IsTriangulated]
    {K : ℕ → C} [HasProduct K] [HasProduct fun n ↦ Φ.obj (K n)]
    [PreservesLimit (Discrete.functor K) Φ]
    (f : ∀ n, K (n + 1) ⟶ K n) (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f L p δ) :
    ∃ e : Φ.obj (∏ᶜ K) ≅ ∏ᶜ fun n ↦ Φ.obj (K n),
      (∀ n, e.hom ≫ Pi.π _ n = Φ.map (Pi.π K n)) ∧
      IsDerivedLimitTriangle (fun n ↦ Φ.map (f n)) (Φ.obj L) (Φ.map p ≫ e.hom)
        (e.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app L) := by
  let e := PreservesProduct.iso Φ K
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = Φ.map (Pi.π K n) := by
    simp [e]
  refine ⟨e, he, ?_⟩
  have ht : Φ.map (towerTransitionEndomorphism f) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ Φ.map (f n)) := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp only [Category.assoc, he, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Pi.lift_comp_π, Functor.map_sub]
    rw [← Category.assoc, he, ← Functor.map_comp, ← Functor.map_comp, Pi.lift_comp_π,
      Category.id_comp, Functor.map_comp]
  refine isomorphic_distinguished _ (Φ.map_distinguished _ h) (Triangle.mk (Φ.map p ≫ e.hom)
    (towerTransitionEndomorphism fun n ↦ Φ.map (f n))
    (e.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app L))
    (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_)
  · simp
  · rw [← cancel_mono e.hom]
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (Iso.inv_hom_id_assoc e _).symm.trans (congrArg (e.inv ≫ ·) ht.symm)
  · simp

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme MonoidalCategory
open scoped CategoryTheory.Functor

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **`Rg_* R lim = R lim Rg_*`** on pro-étale sheaves (Stacks 08U1): the derived pushforward
along any morphism of schemes, being a triangulated right adjoint, sends a derived limit
triangle of a tower of complexes to a derived limit triangle of the image tower. -/
theorem isDerivedLimitTriangle_rightDerivedLowerStar {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {K : ℕ → DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)} [HasProduct K]
    [HasProduct fun n ↦ R((g)_*[A]).obj (K n)]
    (f : ∀ n, K (n + 1) ⟶ K n) (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))
    (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧) (h : IsDerivedLimitTriangle f L p δ) :
    ∃ e : R((g)_*[A]).obj (∏ᶜ K) ≅ ∏ᶜ fun n ↦ R((g)_*[A]).obj (K n),
      (∀ n, e.hom ≫ Pi.π _ n = R((g)_*[A]).map (Pi.π K n)) ∧
      IsDerivedLimitTriangle (fun n ↦ R((g)_*[A]).map (f n)) (R((g)_*[A]).obj L)
        (R((g)_*[A]).map p ≫ e.hom)
        (e.inv ≫ R((g)_*[A]).map δ ≫ (R((g)_*[A]).commShiftIso (1 : ℤ)).hom.app L) := by
  have := (derivedUpperStarLowerStarAdjunction A g).rightAdjoint_preservesLimits
  exact R((g)_*[A]).isDerivedLimitTriangle_map f L p δ h

/-- **`Rg_* R lim = R lim Rg_*`**, homotopy limit form: the derived pushforward along any
morphism of schemes sends a homotopy limit cone of a tower in `D(Z_proét)` to a homotopy limit
cone of the image tower in `D(Y_proét)`, being a triangulated right adjoint. -/
theorem isHomotopyLimit_rightDerivedLowerStar_mapCone {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)} {c : Cone F}
    (hc : IsHomotopyLimit c) : IsHomotopyLimit (R((g)_*[A]).mapCone c) := by
  have := (derivedUpperStarLowerStarAdjunction A g).rightAdjoint_preservesLimits
  exact hc.map _

end AlgebraicGeometry.ProEtale
