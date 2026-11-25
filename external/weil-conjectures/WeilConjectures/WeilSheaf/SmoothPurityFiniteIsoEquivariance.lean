/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrobeniusOrientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalBaseChangeFinal

/-! # Relative finite-coefficient equivariance of the smooth orientation

For isomorphisms of noetherian schemes, the proved finite base-change laws give
the equivariance needed for integral reconstruction.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor

private lemma map_inv_comm_of_hom_comm
    {C : Type*} [Category C] (F : C ⥤ C) {K T : C} (e : K ≅ T)
    (v : F.obj K ⟶ K) (τ : F.obj T ⟶ T)
    (h : v ≫ e.hom = F.map e.hom ≫ τ) :
    F.map e.inv ≫ v = τ ≫ e.inv := by
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, h, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Y : Scheme.{u}}
  {gX : X ⟶ X} {gY : Y ⟶ Y} {f : X ⟶ Y}
  (d : ℕ) [SmoothOfRelativeDimension d f]
  [IsSeparated f] [HasCompactification f] [QuasiCompact f]
  [HasInvertibleExponent Λ X] {k : Type u} [Field k]

/-- Relative finite purity intertwines the Tate datum and the exceptional datum for every
cartesian endomorphism square. This is the relative form needed before integral lifting. -/
theorem isWeilMorphism_dualizingComplexTwistShiftIso_inv_of_isIso_of_isNoetherian
    [IsIso gX] [IsIso gY] [IsNoetherian X] [QuasiSeparatedSpace Y]
    (sq : IsPullback gX f f gY)
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] :
    IsWeilMorphism gX
      ((leftDerivedUpperStarTwistShiftIso Λ gX d (constantComplex Λ X)).hom ≫
        (twistShift Λ X d).map (leftDerivedUpperStarUnitIso _ gX).hom)
      (upperShriekMateWeilDatum (Λ := Λ) sq
        (leftDerivedUpperStarUnitIso _ gY).hom)
      (dualizingComplexTwistShiftIso Λ f d aY).inv := by
  exact map_inv_comm_of_hom_comm (L((gX)^*[ModuleCat.{u + 1} Λ]))
    (dualizingComplexTwistShiftIso Λ f d aY)
    (upperShriekMateWeilDatum (Λ := Λ) sq (leftDerivedUpperStarUnitIso _ gY).hom)
    _ (by
      simpa only [upperShriekMateWeilDatum, constantComplex, dualizingComplex,
        Functor.comp_obj, Category.assoc] using
        dualizingComplexTwistShiftIso_baseChange_of_isIso_of_isNoetherian Λ sq d aY aY)

end AlgebraicGeometry.Etale
