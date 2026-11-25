/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeTensorTate
public import WeilConjectures.WeilSheaf.SmoothPurityNativeHomShift

/-!
# Native tensor with a shifted Tate sheaf

The shift comparison for native internal Hom identifies the adjunction for
tensoring by a shifted Tate object. Uniqueness of left adjoints then gives the
Tate twist followed by the same shift.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Tensoring by a shifted Tate sheaf is scalar twisting followed by shifting. -/
noncomputable def nativeDerivedTensorTateShiftIso (d n : ℤ) :
    Prod.sectR (((DerivedCategory.singleFunctor _ 0).obj
      (WeilSheaf.tateTwistSheaf k₀ l X d).obj) ⟦n⟧) _ ⋙ nativeDerivedTensor k₀ l X ≅
      (constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ d)).mapDerivedCategory ⋙
        shiftFunctor _ n := by
  let D := DerivedCategory (ProEtaleWeilSheaf k₀ l X)
  let C := nativeDerivedClosedComparison k₀ l X
  letI := C.weilClosed.monoidal
  letI := C.weilSymmetry
  let T := (DerivedCategory.singleFunctor _ 0).obj
    (WeilSheaf.tateTwistSheaf k₀ l X d).obj
  let F := (constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ d)).mapDerivedCategory
  let eT (P : D) : tensorRight P ≅ Prod.sectR P _ ⋙ nativeDerivedTensor k₀ l X :=
    (BraidedCategory.tensorLeftIsoTensorRight P).symm ≪≫
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
        dsimp [nativeDerivedTensor, WeilConjectures.CoefficientClosedStructure.tensor]
        change P ◁ g ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 P ⊗ₘ g)
        simp)
  let adjT := (C.weilClosed.adjunction T).ofNatIsoLeft
    (eT T ≪≫ nativeDerivedTensorTateIso d)
  let adj := ((shiftEquiv' D n (-n) (by simp)).toAdjunction).comp adjT
  exact (eT (T⟦n⟧)).symm ≪≫
    ((C.weilClosed.adjunction (T⟦n⟧)).ofNatIsoRight
      (nativeHomSourceShiftIso T n (-n) (by simp))).leftAdjointUniq adj ≪≫
    F.commShiftIso n

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The corresponding comparison on constructible Weil complexes. -/
noncomputable def nativeConstructibleTensorTateShiftIso (d n : ℤ) :
    Prod.sectR ((WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k₀ l X d)) ⟦n⟧) _ ⋙
      nativeConstructibleTensor k₀ l X ≅ tateTwist k₀ l X d ⋙ shiftFunctor _ n := by
  let G := WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k₀ l X d)
  let ι := (objectProperty k₀ l X).ι
  let e : (ι.obj (G⟦n⟧)) ≅ (ι.obj G) ⟦n⟧ := (ι.commShiftIso n).app G
  let a : Prod.sectR (G⟦n⟧) _ ⋙ ι.prod ι ≅
      ι ⋙ Prod.sectR ((ι.obj G) ⟦n⟧) _ :=
    NatIso.ofComponents (fun K ↦ e.prod (Iso.refl (ι.obj K))) (fun _ ↦ by
      simp only [Functor.comp_obj, Functor.prod_obj, prod_Hom, Functor.comp_map, Prod.sectR_map,
        Functor.prod_map, Iso.prod_hom, Iso.refl_hom, prod_comp, Category.comp_id, Prod.mk.injEq]
      constructor
      · erw [ι.map_id]
        exact Category.id_comp _
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)
  apply ((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
  exact Functor.isoWhiskerRight a (ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X) ≪≫
    Functor.isoWhiskerLeft ι
      (ProEtaleWeilSheaf.nativeDerivedTensorTateShiftIso d n) ≪≫
      Functor.isoWhiskerRight (tateTwistCompιIso d).symm (shiftFunctor _ n) ≪≫
      Functor.isoWhiskerLeft (tateTwist k₀ l X d)
        ((objectProperty k₀ l X).ι.commShiftIso n).symm

end AlgebraicGeometry.WeilComplex
