/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeSheafSquareStatement
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationTotalTensor
public import WeilConjectures.Algebra.Homology.Monoidal.MapCochainComplexCoherence
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Tactic.ExactModProofs

/-! # The totalized native pullback tensor square -/

@[expose] public noncomputable section

-- Use the coefficient-category instance fixed by the native tensor construction.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

section ComplexComponent
variable {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    [Preadditive C] [Preadditive D] [Preadditive A] [Preadditive B]
    (L : C ⥤ D) (V : D ⥤ B) (F : C ⥤ A) (R : A ⥤ B)
    [L.Additive] [V.Additive] [F.Additive] [R.Additive]
    (a : F ⋙ R ≅ L ⋙ V) (P : CochainComplex C ℤ) (n : ℤ)

/-- The component formula with all object conversions formed abstractly. -/
def ProjectionComplexSquareComponent : Prop :=
  (((mapHomologicalComplexCompIso a.symm (.up ℤ) ≪≫
    (mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).symm).hom.app P).f n) =
    a.inv.app (P.X n)

/-- Termwise evaluation of the square compositor, with the functors kept abstract. -/
lemma projection_complex_square_hom_app_f : ProjectionComplexSquareComponent L V F R a P n := by
  unfold ProjectionComplexSquareComponent
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    mapHomologicalComplexCompIso_hom_app_f, mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app]
  erw [Category.comp_id]

end ComplexComponent

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The termwise pullback square in the orientation of the native tensor square. -/
abbrev condensedRealizationPullComplexIso :=
  Functor.mapHomologicalComplexCompIso (condensedRealizationUpperStarIso k₀ l g).symm
      (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (condensedRealization k₀ l Y ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))))
        (.up ℤ)).symm

omit [Fact (ringChar k₀ ≠ l)] in
@[simp]
lemma condensedRealizationPullComplexIso_hom_app_f
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (n : ℤ) :
    Functor.ProjectionComplexSquareComponent (upperStar k₀ l g)
      (condensedRealization k₀ l Z) (condensedRealization k₀ l Y)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (condensedRealizationUpperStarIso k₀ l g) P n := by
  exact_mod_proofs Functor.projection_complex_square_hom_app_f
    (upperStar k₀ l g) (condensedRealization k₀ l Z) (condensedRealization k₀ l Y)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    (condensedRealizationUpperStarIso k₀ l g) P n

/-- The square of total tensor comparisons, formed over abstract functors. -/
def TotalPullTensorSquare
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) : Prop :=
  PullTensorSquareWithComparison ((upperStar k₀ l g).mapHomologicalComplex (.up ℤ))
    ((condensedRealization k₀ l Z).mapHomologicalComplex (.up ℤ))
    ((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ))
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g
        (comp_over g (Spec (CommRingCat.of k₀))))).mapHomologicalComplex (.up ℤ))
    (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
    (Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
    (nativePullTotalTensor k₀ l g) (condensedRealizationTotalTensorIso k₀ l Y)
    (condensedRealizationTotalTensorIso k₀ l Z) (condensedRealizationPullComplexIso k₀ l g).symm
    (fun A B ↦ ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g
        (comp_over g (Spec (CommRingCat.of k₀))))).mapCochainComplexμIso
        A B).inv) P T

end AlgebraicGeometry.ProEtaleWeilSheaf
