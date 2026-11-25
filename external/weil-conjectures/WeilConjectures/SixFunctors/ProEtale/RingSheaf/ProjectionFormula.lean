/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence

/-!
# The projection formula for the extension by zero along a quasi-compact open immersion

Let `R` be a commutative ring, `j : U ⟶ X` a quasi-compact open immersion and `i : Z ⟶ X` a
closed immersion onto the complement of its range. For pro-étale sheaves of `R`-modules, the
canonical projection formula map `j_!(j^* L ⊗ M) ⟶ L ⊗ j_! M` (the adjoint of
`j^* L ⊗ M ⟶ j^* L ⊗ j^* j_! M ≅ j^*(L ⊗ j_! M)`) is an isomorphism
(`AlgebraicGeometry.ProEtale.hasProjectionFormula_openImmersion_of_isCompl`).

Since `i^*` and `j^*` jointly detect isomorphisms
(`AlgebraicGeometry.ProEtale.isIso_of_isIso_upperStar_of_isCompl`), it suffices to check this
after `j^*`, where it follows from the invertibility of the unit `M ⟶ j^* j_! M` and of the
monoidal structure of `j^*`, and after `i^*`, where both sides vanish: `i^* j_! = 0` and
`i^*(L ⊗ j_! M) ≅ i^* L ⊗ i^* j_! M`.

This is the input that makes the extension by zero linear over an arbitrary sheaf of
`R`-algebras (`WeilConjectures.SixFunctors.ProEtale.RingSheaf.OpenClosed`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R : Type (u + 1)} [CommRing R] {Z U X : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- In a monoidal preadditive category, `X ⊗ Y` is zero if `Y` is. -/
lemma _root_.CategoryTheory.Limits.IsZero.tensorObj_right {C : Type*} [Category* C]
    [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] (X : C) {Y : C} (hY : IsZero Y) :
    IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.whiskerLeft_id, hY.eq_of_src (𝟙 Y) 0,
    MonoidalPreadditive.whiskerLeft_zero]

/-- The projection formula for the extension by zero along a quasi-compact open immersion `j`
with closed complement `i`, on pro-étale sheaves of modules over a commutative ring: the
canonical map `j_!(j^* L ⊗ M) ⟶ L ⊗ j_! M` is an isomorphism. It is checked after `j^*`
and `i^*`, which jointly detect isomorphisms. -/
theorem hasProjectionFormula_openImmersion_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).HasProjectionFormula
    where
  isIso L M := by
    set adj := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j
    have hj : IsIso ((j)^*[ModuleCat.{u + 1} R].map (adj.projectionFormulaMap L M)) := by
      rw [Adjunction.projectionFormulaMap, Adjunction.homEquiv_counit, Functor.map_comp]
      infer_instance
    have hi : IsIso ((i)^*[ModuleCat.{u + 1} R].map (adj.projectionFormulaMap L M)) := by
      have hz : ∀ N, IsZero ((i)^*[ModuleCat.{u + 1} R].obj ((j)_!open[ModuleCat.{u + 1} R].obj
          N)) := fun N ↦ isZero_upperStar_openImmersionLowerShriek _ j i
        (Set.disjoint_iff_inter_eq_empty.1 hij.disjoint.symm) N
      have ht : IsZero ((i)^*[ModuleCat.{u + 1} R].obj (L ⊗ (j)_!open[ModuleCat.{u + 1} R].obj
          M)) :=
        ((hz M).tensorObj_right _).of_iso
          (Functor.Monoidal.μIso (i)^*[ModuleCat.{u + 1} R] _ _).symm
      exact ⟨⟨0, (hz _).eq_of_src _ _, ht.eq_of_src _ _⟩⟩
    exact isIso_of_isIso_upperStar_of_isCompl i j hij _

end AlgebraicGeometry.ProEtale
