/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.SmoothPurity.Rational.RationalRestrictionPullbackFreeMate
import WeilConjectures.SmoothPurity.Rational.RationalScalarRetractGenerators
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! # The scalar-unit equation for rational restriction and pullback

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14(2), Remark 6.8.15;
step 2 of the finite rational coefficient argument.
(blueprint: lem-sf-rational-restriction-pullback-unit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private theorem restrictionUnit_of_retracts
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (LF : A ⥤ B) (LE : C ⥤ D) (TX : D ⥤ B) (TY : C ⥤ A)
    (UX : B ⥤ D) (UY : A ⥤ C) (bX : UX ⊣ TX) (bY : UY ⊣ TY)
    (α : TY ⋙ LF ⟶ LE ⋙ TX)
    (hgen : ∀ K : A, ∃ M : C, Nonempty (Retract K (TY.obj M)))
    (hiso : ∀ M : C, IsIso
      (((mateEquiv bY bX).symm (TwoSquare.mk _ _ _ _ α)).app (TY.obj M))) :
    ∃ e : LF ⋙ UX ≅ UY ⋙ LE,
      ∀ K, LF.map (bY.unit.app K) ≫ α.app (UY.obj K) =
        bX.unit.app (LF.obj K) ≫ TX.map (e.hom.app K) := by
  let δ := ((mateEquiv bY bX).symm (TwoSquare.mk _ _ _ _ α))
  have hδ (K : A) : IsIso (δ.app K) := by
    obtain ⟨M, ⟨r⟩⟩ := hgen K
    exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms D)
      (δ.retractArrowApp r) (hiso M)
  have : IsIso δ := NatIso.isIso_of_isIso_app δ
  refine ⟨asIso δ, ?_⟩
  intro K
  exact unit_mateEquiv_symm bY bX (TwoSquare.mk _ _ _ _ α) K

/-- Restriction commutes with pullback by an isomorphism satisfying the explicit
unit equation for the normalized scalar comparison.

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14(2), Remark 6.8.15;
step 2 of lem-sf-rational-pullback-scalar-right-mate.
(blueprint: lem-sf-rational-restriction-pullback-unit).

Proof: form delta, the inverse adjunction mate of the specified inverse scalar
comparison. The trace calculation on scalar-extended inputs proves that delta
is invertible at every T_Y(M). Every raw rational F-object K is a retract of
such an input, by finite separability of F/E. Naturality of delta carries this
object retract to a retract in the arrow category. Isomorphisms are closed under
retracts, so delta is invertible at K. Pointwise invertibility supplies the natural
isomorphism e. The identity unit_mateEquiv_symm is exactly the required unit
equation, so no separate choice or normalization of e is needed. The argument
applies directly to the supplied bX and bY and uses no geometric right adjoints. -/
theorem rationalRestrictionPullback_unit
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (UX : sfRationalConstructibleCategory l F X ⥤ sfRationalConstructibleCategory l E X)
    (UY : sfRationalConstructibleCategory l F Y ⥤ sfRationalConstructibleCategory l E Y)
    (bX : UX ⊣ sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι)
    (bY : UY ⊣ sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι) :
    ∃ e : rationalDerivedPullback l F f ⋙ UX ≅ UY ⋙ rationalDerivedPullback l E f,
      ∀ K : sfRationalConstructibleCategory l F Y,
        (rationalDerivedPullback l F f).map (bY.unit.app K) ≫
          (rationalPullbackScalarComparison l E F ι f).inv.app (UY.obj K) =
        bX.unit.app ((rationalDerivedPullback l F f).obj K) ≫
          (sfRationalScalarExtension l E X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map (e.hom.app K) := by
  exact restrictionUnit_of_retracts
    (rationalDerivedPullback l F f) (rationalDerivedPullback l E f)
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι)
    (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι)
    UX UY bX bY (rationalPullbackScalarComparison l E F ι f).inv
    (rationalScalar_retract_generators l E F ι Y)
    (rationalRestrictionPullback_freeMate l E F ι f UX UY bX bY)

end WeilConjectures
