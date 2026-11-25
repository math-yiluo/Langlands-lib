/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCompactConstant
public import WeilConjectures.WeilSheaf.SmoothPurityNativeTensorTateShift
public import WeilConjectures.WeilSheaf.SmoothPurityDescentSingle
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The Thom functor from compact cohomology of the constant object

Compact base change reduces constant coefficients on a trivial line bundle to
the affine line over the finite field. The projection formula and the native
tensor comparison then give the Thom functor on all Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- Pullback commutes with placing a sheaf in degree zero. -/
noncomputable def purityUpperStarToComplexIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] (A : WeilSheaf k₀ l Y) :
    (upperStar f).obj (WeilSheaf.toComplex.obj A) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.upperStar f).obj A) :=
  ObjectProperty.isoMk _
    (((ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategorySingleFunctor 0).app A.obj)

/-- Pullback preserves the constant Weil complex. -/
noncomputable def purityUpperStarConstantIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] :
    (upperStar f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X) :=
  purityUpperStarToComplexIso f _ ≪≫
    WeilSheaf.toComplex.mapIso (WeilSheaf.upperStarAdicConstantIso f)

/-- Pullback preserves the native Tate sheaf, including its Frobenius datum. -/
noncomputable def purityUpperStarTateSheafIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] (d : ℤ) :
    (WeilSheaf.upperStar f).obj (WeilSheaf.tateTwistSheaf k₀ l Y d) ≅
      WeilSheaf.tateTwistSheaf k₀ l X d :=
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.upperStar k₀ l f).mapIso (WeilSheaf.tateTwistSheafObjIso k₀ l Y d) ≪≫
      (ProEtaleWeilSheaf.constantTwistCompUpperStarIso k₀ l f
        (WeilSheaf.cyclotomicUnit k₀ l ^ d)).app (ProEtaleWeilSheaf.adicConstant k₀ l Y) ≪≫
      (ProEtaleWeilSheaf.constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ d)).mapIso
        (ProEtaleWeilSheaf.upperStarAdicConstantIso f) ≪≫
      (WeilSheaf.tateTwistSheafObjIso k₀ l X d).symm)

/-- Pullback preserves a shifted native Tate complex. -/
noncomputable def purityUpperStarShiftedTateIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] (d n : ℤ) :
    (upperStar f).obj ((WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k₀ l Y d)) ⟦n⟧) ≅
      (WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k₀ l X d)) ⟦n⟧ :=
  ((upperStar f).commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso (purityUpperStarToComplexIso f _ ≪≫
      WeilSheaf.toComplex.mapIso (purityUpperStarTateSheafIso f d))

variable {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Compact constant cohomology determines the pullback/compact-pushforward
functor through the projection formula. -/
theorem nonempty_upperStar_comp_shriek_iso_of_constant_cohomology (d n : ℤ)
    (e : (derivedLowerShriek k₀ l f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) ≅
      (WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k₀ l Y d)) ⟦n⟧) :
    Nonempty (upperStar f ⋙ derivedLowerShriek k₀ l f ≅
      tateTwist k₀ l Y d ⋙ shiftFunctor _ n) := by
  obtain ⟨a⟩ := nonempty_upperStar_comp_shriek_iso_tensor_constant (k₀ := k₀) (l := l) f
  exact ⟨a ≪≫ Functor.isoWhiskerRight
    (NatIso.ofComponents (fun _ ↦ e.prod (Iso.refl _)) (fun _ ↦ by simp))
      (nativeConstructibleTensor k₀ l Y) ≪≫ nativeConstructibleTensorTateShiftIso d n⟩

end AlgebraicGeometry.WeilComplex

namespace AlgebraicGeometry.WeilComplex

attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- Compact base change determines the compact constant object of a trivial line bundle. -/
theorem nonempty_trivialLine_compact_constant_iso
    (e : (derivedLowerShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀))) ≅
      (WeilSheaf.toComplex.obj
        (WeilSheaf.tateTwistSheaf k₀ l (Spec (CommRingCat.of k₀)) (-1))) ⟦(-2 : ℤ)⟧)
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    (π : Y ⟶ X) (s : Y ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty ((derivedLowerShriek k₀ l π).obj
      (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
        (WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k₀ l X (-1))) ⟦(-2 : ℤ)⟧) := by
  have : s.IsOver (Spec (CommRingCat.of k₀)) :=
    ⟨hπ.w.symm.trans (comp_over π _)⟩
  obtain ⟨bc⟩ := nonempty_upperStar_derivedLowerShriek_iso (k₀ := k₀) (l := l) hπ.flip
  let A := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀))
  let a : (upperStar (k₀ := k₀) (l := l) (X ↘ Spec (CommRingCat.of k₀))).obj
      ((derivedLowerShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj A) ≅
      (derivedLowerShriek k₀ l π).obj ((upperStar (k₀ := k₀) (l := l) s).obj A) := bc.app A
  exact ⟨(derivedLowerShriek k₀ l π).mapIso
      (purityUpperStarConstantIso (k₀ := k₀) (l := l) s).symm ≪≫
    a.symm ≪≫ (upperStar (k₀ := k₀) (l := l) (X ↘ Spec (CommRingCat.of k₀))).mapIso e ≪≫
    purityUpperStarShiftedTateIso (k₀ := k₀) (l := l) (X ↘ Spec (CommRingCat.of k₀)) (-1) (-2)⟩

/-- Compact base change transports the constant affine-line calculation to a
trivial line bundle; the projection formula gives the full Thom functor. -/
theorem nonempty_trivialLineThom_of_affineLine_constant
    (e : (derivedLowerShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀))) ≅
      (WeilSheaf.toComplex.obj
        (WeilSheaf.tateTwistSheaf k₀ l (Spec (CommRingCat.of k₀)) (-1))) ⟦(-2 : ℤ)⟧)
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    (π : Y ⟶ X) (s : Y ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (upperStar π ⋙ derivedLowerShriek k₀ l π ≅
      tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)) := by
  have : IsSeparated (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π (Spec (CommRingCat.of k₀))]
    infer_instance
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π (Spec (CommRingCat.of k₀))]
    infer_instance
  obtain ⟨a⟩ := nonempty_trivialLine_compact_constant_iso e π s hπ
  exact nonempty_upperStar_comp_shriek_iso_of_constant_cohomology
    (k₀ := k₀) (l := l) π (-1) (-2) a

end AlgebraicGeometry.WeilComplex
