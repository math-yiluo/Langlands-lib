/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SmoothPurity.Rational.RationalScalarExtensionReflectsIsomorphisms
import WeilConjectures.CategoryTheory.Adjunction.MateHomBasis
import WeilConjectures.SmoothPurity.Sf.SfRationalScalarExtensionHomBasis

/-! # The legacy finite-free mate after scalar extension

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
trace-dual-basis coordinates after applying the scalar extension functor.

This compatibility statement belongs to the retired rationalization/Karoubi route.
It remains for existing legacy consumers. The current blueprint definition of
derived direct image uses the condensed module-object construction recorded by
`prose-03-02`; this lemma is not an input to that definition.
(blueprint: new-sf-rational-restriction-pullback-free-mate-after-extension).
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
namespace WeilConjectures

/-- A functor between scalar localizations that is additive and given on pure tensors by an
underlying functor `U` (up to the object equation) is linear over the localized ring. -/
theorem ScalarLocalization.map_smul_of_map_tmul_heq
    {R : Type*} [CommRing R] {C D : Type*} [Category C] [Preadditive C] [Linear R C]
    [Category D] [Preadditive D] [Linear R D] (t : R) (U : C ⥤ D)
    (G : ScalarLocalization R C t ⥤ ScalarLocalization R D t) [G.Additive]
    (hobj : ∀ K, G.obj K = ⟨U.obj K.obj⟩)
    (hmap : ∀ (K L : C) (g : K ⟶ L) (c : Localization.Away t),
      HEq (G.map (c ⊗ₜ[R] g : (⟨K⟩ : ScalarLocalization R C t) ⟶ ⟨L⟩)) (c ⊗ₜ[R] U.map g))
    {K L : ScalarLocalization R C t} (a : Localization.Away t) (h : K ⟶ L) :
    G.map (a • h) = a • G.map h := by
  induction h using TensorProduct.inductionOn with
  | tmul c g =>
    have h₁ := (conj_eqToHom_iff_heq _ _ (hobj K) (hobj L)).2 (hmap K.obj L.obj g (a * c))
    have h₂ := (conj_eqToHom_iff_heq _ _ (hobj K) (hobj L)).2 (hmap K.obj L.obj g c)
    erw [TensorProduct.smul_tmul', smul_eq_mul, h₁, h₂]
    rw [← Linear.comp_smul, ← Linear.smul_comp]
    erw [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy =>
    rw [smul_add, G.map_add, G.map_add, hx, hy, smul_add]

/-- Applying the canonical E-to-F scalar extension to the finite-free mate at
an extended object gives an isomorphism.

Proof: choose a finite E-basis of F and its trace-dual basis. On K-flat
representatives, finite-free tensor coordinates identify the two composites
with the same finite direct sum after pullback. The normalized completed
comparison and rational localization preserve this coordinate equality, so the
map obtained by applying the X scalar extension to the canonical mate is
invertible. -/
theorem rationalRestrictionPullback_freeMate_after_extension
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : sfRationalConstructibleCategory l E Y) :
    IsIso ((sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map
      (((mateEquiv
        (rationalScalarExtension_leftAdjunction l E F ι Y)
        (rationalScalarExtension_leftAdjunction l E F ι X)).symm
        (TwoSquare.mk _ _ _ _ (rationalPullbackScalarComparison l E F ι f).inv)).app
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M))) := by
  classical
  let := ι.toAlgebra
  have : FiniteDimensional E F := Module.Finite.right ℚ_[l] E F
  let v := Module.finBasis E F
  have hv (x : F) : ∃! c : Fin (Module.finrank E F) → E, ∑ i, ι (c i) * v i = x := by
    have hc (c : Fin (Module.finrank E F) → E) : ∑ i, ι (c i) * v i = v.equivFun.symm c := by
      rw [Module.Basis.equivFun_symm_apply]
      rfl
    refine ⟨v.equivFun x, by simp only [hc, LinearEquiv.symm_apply_apply], fun c h ↦ ?_⟩
    rw [← h, hc, LinearEquiv.apply_symm_apply]
  let GF := rationalDerivedPullback l F f
  have hF := (rationalDerivedPullback_existsUnique l F f).exists.choose_spec
  have hE := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
  have : GF.Additive := hF.1
  have : (rationalDerivedPullback l E f).Additive := hE.1
  have hGF {K L : sfRationalConstructibleCategory l F Y}
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l F)) (h : K ⟶ L) :
      GF.map (a • h) = a • GF.map h :=
    ScalarLocalization.map_smul_of_map_tmul_heq _ _ GF hF.2.1 (by
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      simpa only [GF, rationalDerivedPullback, sfRationalConstructibleLocalization,
        ScalarLocalization.localization] using hF.2.2) a h
  have hδ := isIso_mateEquiv_symm_app_of_homBasis
    (rationalScalarExtension_leftAdjunction l E F ι Y)
    (rationalScalarExtension_leftAdjunction l E F ι X)
    (rationalDerivedPullback l E f) GF (rationalPullbackScalarComparison l E F ι f).inv
    (fun i ↦ (sfRationalCoefficientEquiv l F).symm (v i)) (fun i h ↦ hGF _ h)
    (sfRationalScalarExtension_map_basis_bijective l E Y 0 _ F ι v hv)
    (sfRationalScalarExtension_map_basis_bijective l E X 0 _ F ι v hv) M
  exact Functor.map_isIso _ _

end WeilConjectures
