/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.SmoothPurity.OrientationCanonical

/-!
# Concentration of the smooth dualizing Weil complex

The geometric comparison for an arbitrary right adjoint of compact support identifies
its value on the constant object with the geometric dualizing complex. Geometric purity
and the exact support-interval criterion then give concentration in degree `-2d`.
This argument does not require an equivariant purity isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The exceptional constant object on a smooth scheme is concentrated in degree `-2d`.
Only the underlying geometric purity isomorphism is used. -/
theorem smooth_dualizing_concentration
    (J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X)
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ J)
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] :
    ((J.obj (WeilSheaf.toComplex.obj
        (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))).obj.IsGE (-2 * (d : ℤ))) ∧
    ((J.obj (WeilSheaf.toComplex.obj
        (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))).obj.IsLE (-2 * (d : ℤ))) := by
  let K := J.obj (WeilSheaf.toComplex.obj
    (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))
  let b : ℤ := -2 * (d : ℤ)
  let Xbar := Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
    ⟨by rw [← Algebra.ringChar_eq k₀ (AlgebraicClosure k₀)]
        exact CharP.prime_ringChar k₀⟩
  have : Fact (ringChar (AlgebraicClosure k₀) ≠ l) :=
    ⟨by rw [← Algebra.ringChar_eq k₀ (AlgebraicClosure k₀)]; exact Fact.out⟩
  have : NeZero (l : AlgebraicClosure k₀) :=
    ⟨CharP.cast_ne_zero_of_ne_of_prime _ (Fact.out : l.Prime) Fact.out⟩
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d Xbar.hom :=
    MorphismProperty.pullback_snd _ _ ‹SmoothOfRelativeDimension d
      (X ↘ Spec (CommRingCat.of k₀))›
  have : SmoothOfRelativeDimension d (Over.mkIdTerminal.from Xbar).left := by
    simpa only [Over.mkIdTerminal_from_left] using ‹SmoothOfRelativeDimension d Xbar.hom›
  obtain ⟨e⟩ := nonempty_nativeGeometricForget_obj_iso_of_adjunction adj
  obtain ⟨p⟩ := CondensedRing.nonempty_iso_tateTwist_upperShriekUnit l
    (Over.mkIdTerminal.from Xbar) d
  let e' := e ≪≫ (ObjectProperty.ι _).mapIso p.symm
  have hz : ∀ n : ℤ, n < b ∨ b < n →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        ((ProEtaleWeilSheaf.nativeGeometricForget k₀ l X).obj K.obj)) := by
    intro n hn
    let s := ((_root_.DerivedCategory.singleFunctors _).shiftIso
      (2 * (d : ℤ)) b 0 (by dsimp [b]; omega)).app
        (ProEtale.tateTwist Xbar.left l d)
    refine IsZero.of_iso ?_
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso (e' ≪≫ s))
    change IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((_root_.DerivedCategory.singleFunctor _ b).obj (ProEtale.tateTwist Xbar.left l d)))
    rcases hn with hn | hn
    · exact _root_.DerivedCategory.isZero_of_isGE _ b n hn
        (hX := _root_.DerivedCategory.instIsGEObjSingleFunctor _ _)
    · exact _root_.DerivedCategory.isZero_of_isLE _ b n hn
        (hX := _root_.DerivedCategory.instIsLEObjSingleFunctor _ _)
  have hK := ((ProEtaleWeilSheaf.weil_geometric_hom_constructibility k₀ l X).2.1
    K.obj b b).2 hz
  exact ⟨(_root_.DerivedCategory.isGE_iff K.obj b).2 (fun n hn ↦ hK n (Or.inl hn)),
    (_root_.DerivedCategory.isLE_iff K.obj b).2 (fun n hn ↦ hK n (Or.inr hn))⟩

end AlgebraicGeometry.WeilComplex
