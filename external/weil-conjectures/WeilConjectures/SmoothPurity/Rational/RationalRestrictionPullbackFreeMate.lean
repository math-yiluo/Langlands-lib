/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SmoothPurity.Rational.RationalRestrictionPullbackFreeMateCanonical

/-! # The normalized restriction mate on scalar-extended objects

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
the finite-free trace calculation on scalar-extended complexes.
(blueprint: lem-sf-rational-restriction-pullback-free-mate).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private theorem inverseMate_component_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : L₁' ⊣ R₁) (b₂ : L₂' ⊣ R₂)
    (β : TwoSquare R₁ H G R₂) (K : A)
    [IsIso (((mateEquiv b₁ b₂).symm β).app K)] :
    IsIso (((mateEquiv a₁ a₂).symm β).app K) := by
  let e₁ : L₁' ≅ L₁ := (conjugateIsoEquiv a₁ b₁).symm (Iso.refl R₁)
  let e₂ : L₂' ≅ L₂ := (conjugateIsoEquiv a₂ b₂).symm (Iso.refl R₂)
  have h₁ : conjugateEquiv a₁ b₁ e₁.hom = 𝟙 R₁ :=
    (conjugateEquiv a₁ b₁).apply_symm_apply (𝟙 R₁)
  have h₂ : conjugateEquiv a₂ b₂ e₂.hom = 𝟙 R₂ :=
    (conjugateEquiv a₂ b₂).apply_symm_apply (𝟙 R₂)
  let w := (mateEquiv a₁ a₂).symm β
  let w' := (mateEquiv b₁ b₂).symm β
  have h : w'.whiskerLeft e₁.hom = w.whiskerRight e₂.hom := by
    apply (mateEquiv a₁ b₂).injective
    rw [conjugateEquiv_mateEquiv_vcomp a₁ b₁ b₂ e₁.hom w',
      mateEquiv_conjugateEquiv_vcomp a₁ a₂ b₂ w e₂.hom]
    simp only [w, w', Equiv.apply_symm_apply, h₁, h₂]
    ext X
    simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]
  have hc := congrArg (fun t ↦ t.app K) h
  change w'.app K ≫ H.map (e₁.hom.app K) = e₂.hom.app (G.obj K) ≫ w.app K at hc
  have hi : IsIso (e₂.hom.app (G.obj K) ≫ w.app K) := by
    rw [← hc]
    infer_instance
  exact IsIso.of_isIso_comp_left (e₂.hom.app (G.obj K)) (w.app K)

/-- The left mate of the normalized comparison is invertible on scalar-extended inputs.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
the dual-basis calculation of step 2 of lem-sf-rational-restriction-pullback-unit,
restricted to inputs extended from E.
(blueprint: lem-sf-rational-restriction-pullback-free-mate).

Proof: fix an E-basis b_i of F and its trace-dual basis c_i. For an E-object M,
use bW.homEquiv on T_W(M). Finite-free tensor coordinates identify
Hom_F(T_W(M), T_W(N)) with Hom_E(F-dual tensor_E M, N), naturally in every
E-object N. Thus U_W(T_W(M)) is represented by the finite sum of copies of M
indexed by the basis of F-dual. The trace pairing identifies F-dual with F.
Yoneda identifies these coordinates with the supplied adjunction; its unit on
T_W(M) is x maps to sum_i b_i tensor c_i x and its counit is the trace sum.
This only represents the adjunction on free inputs, without defining a
restriction functor on arbitrary F-objects.

Pullback preserves these finite sums and their basis maps. In these coordinates
the left mate of ordinary tensor/pullback comparison is the identity, hence
invertible. To check the exact recorded comparison, use
finiteFreeCompletedScalarComparison to replace ordinary finite-free tensor by
the normalized completed tensor on complete representatives. Its quotient-tower
normalization and the representative formula for rationalPullbackScalarComparison
identify the comparison in this calculation with the recorded inverse comparison,
including its direction. The unit calculation is equality of the displayed
finite sums; resolving by K-flat complexes and clearing trace denominators
preserve it in the raw localized Hom groups. Naturality and the representing
Hom equivalences identify the resulting mate with mateEquiv for bX and bY.
The calculation does not choose arbitrary data from adjoint existence and covers rank one,
zero complexes and empty schemes, without assuming geometric right adjoints. -/
theorem rationalRestrictionPullback_freeMate
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
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι)
    (M : sfRationalConstructibleCategory l E Y) :
    IsIso (((mateEquiv bY bX).symm
      (TwoSquare.mk _ _ _ _ (rationalPullbackScalarComparison l E F ι f).inv)).app
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M)) := by
  let TY := sfRationalScalarExtension l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  let bX₀ := rationalScalarExtension_leftAdjunction l E F ι X
  let bY₀ := rationalScalarExtension_leftAdjunction l E F ι Y
  have hc := rationalRestrictionPullback_freeMate_canonical l E F ι f M
  letI := hc
  exact inverseMate_component_transport bY bX bY₀ bX₀
    (TwoSquare.mk _ _ _ _ (rationalPullbackScalarComparison l E F ι f).inv)
    (TY.obj M)

end WeilConjectures
