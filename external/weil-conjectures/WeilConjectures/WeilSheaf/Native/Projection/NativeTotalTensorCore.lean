/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeSheafSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTotalSquareStatement
public import WeilConjectures.Algebra.Homology.Monoidal.MapCochainComplexCoherence
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Mathlib.CategoryTheory.Functor.Basic

/-! # The totalized native pullback tensor square -/

@[expose] public noncomputable section

set_option Elab.async false

-- Use the coefficient-category instance fixed by the native tensor construction.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- Paste the restriction, realization and tensor squares on a totalization summand. -/
private lemma tensorSquare_paste_summand {D : Type*} [Category* D]
    {S T₀ T₁ T₂ U₀ U₁ U₂ V₀ V₁ V₂ W₀ W₁ : D}
    {i : S ⟶ T₀} {m : T₀ ⟶ T₁} {z : T₁ ⟶ T₂} {f : T₂ ⟶ U₂}
    {b : T₀ ⟶ U₀} {y : U₀ ⟶ U₁} {d : U₁ ⟶ U₂}
    {v : S ⟶ V₀} {j : V₀ ⟶ T₁} {sz : V₀ ⟶ V₁} {iz : V₁ ⟶ T₂}
    {aa : V₁ ⟶ V₂} {iR : V₂ ⟶ U₂} {a : S ⟶ W₀}
    {sy : W₀ ⟶ W₁} {δ : W₁ ⟶ V₂} {ri : W₀ ⟶ U₀} {iy : W₁ ⟶ U₁}
    (hu : i ≫ m = v ≫ j) (hz : j ≫ z = sz ≫ iz) (hf : iz ≫ f = aa ≫ iR)
    (hs : v ≫ sz ≫ aa = a ≫ sy ≫ δ) (hb : i ≫ b = a ≫ ri)
    (hy : ri ≫ y = sy ≫ iy) (hd : iy ≫ d = δ ≫ iR) :
    i ≫ m ≫ z ≫ f = i ≫ b ≫ y ≫ d := by
  calc
    i ≫ m ≫ z ≫ f = v ≫ sz ≫ aa ≫ iR := by
      rw [reassoc_of% hu, reassoc_of% hz, hf]
    _ = a ≫ sy ≫ δ ≫ iR := by rw [reassoc_of% hs]
    _ = i ≫ b ≫ y ≫ d := by rw [reassoc_of% hb, reassoc_of% hy, hd]

end CategoryTheory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] projection_hasSmallColimits projection_hasTensor
  projection_nativeHasTotal projection_tensorLeftPreservesInitial
  projection_tensorRightPreservesInitial projection_hasGoodTensor12
  projection_hasGoodTensor23 projection_hasTensor4Ext

variable
  (L : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z)
  [L.Additive] [L.IsLeftAdjoint]
  (R : Mod (Sheaf (Scheme.ProEt.topology (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⥤
    Mod (Sheaf (Scheme.ProEt.topology (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber))
  [R.Additive] [R.Monoidal] [R.IsLeftAdjoint]
  (mu : nativeOpenSheafTensor k₀ l Y ⋙ L ≅ L.prod L ⋙ nativeOpenSheafTensor k₀ l Z)
  (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ L.mapHomologicalComplex (.up ℤ) ≅
    (L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
  (a : condensedRealization k₀ l Y ⋙ R ≅ L ⋙ condensedRealization k₀ l Z)

/-- The total tensor square with the pullback functors left abstract. -/
def ProjectionTotalTensorSquare
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) : Prop :=
  PullTensorSquareWithComparison (L.mapHomologicalComplex (.up ℤ))
    ((condensedRealization k₀ l Z).mapHomologicalComplex (.up ℤ))
    ((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ))
    (R.mapHomologicalComplex (.up ℤ))
    (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
    (Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) t
    (condensedRealizationTotalTensorIso k₀ l Y) (condensedRealizationTotalTensorIso k₀ l Z)
    (Functor.mapHomologicalComplexCompIso a.symm (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (condensedRealization k₀ l Y ⋙ R)) (.up ℤ)).symm).symm
    (fun A B ↦ (R.mapCochainComplexμIso A B).inv) P T

variable
  (hmu : NativeRestrictionDescentProof.RestrictionTotalSummands L
    (nativeOpenSheafTensor k₀ l Z) (nativeOpenSheafTensor k₀ l Y)
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeOpenTensorInsertion k₀ l Z) (nativeOpenTensorInsertion k₀ l Y) mu t)
  (hsheaf : ∀ M N, PullTensorSquare L (condensedRealization k₀ l Z)
    (condensedRealization k₀ l Y) R (nativeOpenSheafTensor k₀ l Y)
    (nativeOpenSheafTensor k₀ l Z) mu (condensedRealizationSheafTensorIso k₀ l Y)
    (condensedRealizationSheafTensorIso k₀ l Z) a M N)

include hmu hsheaf in
/-- Equality of the two total-complex tensor squares, checked on each tensor summand. -/
lemma projection_totalTensorSquare_of_sheaf
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) :
    ProjectionTotalTensorSquare k₀ l L R t a P T := by
  unfold ProjectionTotalTensorSquare PullTensorSquareWithComparison
  simp only [Iso.symm_inv]
  ext n : 1
  have hcomp (A : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (i : ℤ) :=
    Functor.projection_complex_square_hom_app_f L (condensedRealization k₀ l Z)
      (condensedRealization k₀ l Y) R a A i
  dsimp only [Functor.ProjectionComplexSquareComponent] at hcomp
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  conv_rhs => arg 1; rw [hcomp]
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (L ⋙ condensedRealization k₀ l Z)
    (F := (nativeTensorBifunctor k₀ l Y).flip)
  intro p q hpq
  simp only [Functor.comp_map L (condensedRealization k₀ l Z)]
  have hpull' := Functor.map_comp_map_eq_map_comp_map (condensedRealization k₀ l Z)
    (hmu P T p q n hpq)
  dsimp only [nativeOpenTensorInsertion, Iso.app_hom] at hpull'
  have hnZ := condensedRealizationTotalTensorIso_summand k₀ l Z
    ((L.mapHomologicalComplex (.up ℤ)).obj P)
    ((L.mapHomologicalComplex (.up ℤ)).obj T) p q n hpq
  dsimp only [nativeOpenTensorInsertion, Iso.app_hom] at hnZ
  have hs := hsheaf (P.X p) (T.X q)
  dsimp only [PullTensorSquare] at hs
  have hn := a.inv.naturality
    (nativeOpenTensorInsertion k₀ l Y P T p q n hpq)
  dsimp only [nativeOpenTensorInsertion] at hn
  simp only [Functor.comp_map L (condensedRealization k₀ l Z),
    Functor.comp_map (condensedRealization k₀ l Y) R] at hn
  have hnY := condensedRealizationTotalTensorIso_summand k₀ l Y P T p q n hpq
  dsimp only [nativeOpenTensorInsertion, Iso.app_hom] at hnY
  have hy := Functor.map_comp_map_eq_map_comp_map R hnY
  have hd := Functor.map_ιTensorObj_mapCochainComplexμIso_inv_f R
    (((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ)).obj P)
    (((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ)).obj T) p q n hpq
  refine tensorSquare_paste_summand hpull' hnZ ?_ hs hn hy hd
  erw [CochainComplex.ιTensorObj_tensorHom_f, hcomp P p, hcomp T q]
  rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
