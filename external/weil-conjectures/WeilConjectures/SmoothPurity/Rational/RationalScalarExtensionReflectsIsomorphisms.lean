/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.SmoothPurity.Rational.RationalScalarExtensionRightAdjoint
import WeilConjectures.SmoothPurity.Rational.RationalScalarExtensionCounitObjectwiseSplit
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Conservativity of finite rational scalar extension

Source: finite separable coefficient extension and the raw rationalization
construction (blueprint: new-sf-rational-scalar-extension-reflects-isomorphisms).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private theorem reflects_of_split_counit
    {C D : Type*} [Category C] [Category D]
    (U : C ⥤ D) (T : D ⥤ C) (b : U ⊣ T)
    (hobj : ∀ X : D, ∃ s : X ⟶ (T ⋙ U).obj X,
      s ≫ b.counit.app X = 𝟙 X) :
    T.ReflectsIsomorphisms := by
  classical
  choose s hs using hobj
  letI : ∀ X, IsSplitEpi (b.counit.app X) := fun X ↦
    IsSplitEpi.mk' { section_ := s X, id := hs X }
  letI : T.Faithful := b.faithful_R_of_epi_counit_app
  constructor
  intro X Y f hf
  letI := hf
  let g : Y ⟶ X := s Y ≫ U.map (inv (T.map f)) ≫ b.counit.app X
  have hgf : g ≫ f = 𝟙 Y := by
    have hc : b.counit.app X ≫ f = U.map (T.map f) ≫ b.counit.app Y := by
      exact (b.counit.naturality f).symm
    calc
      g ≫ f = s Y ≫ U.map (inv (T.map f)) ≫ (b.counit.app X ≫ f) := by
        simp only [g, Category.assoc]
      _ = s Y ≫ U.map (inv (T.map f)) ≫
          (U.map (T.map f) ≫ b.counit.app Y) := by rw [hc]
      _ = s Y ≫ b.counit.app Y := by
        rw [← Category.assoc (U.map (inv (T.map f))) (U.map (T.map f)) _]
        rw [← U.map_comp, IsIso.inv_hom_id, U.map_id]
        simp
      _ = 𝟙 Y := hs Y
  letI : Mono f := T.mono_of_mono_map (by infer_instance)
  letI : IsSplitEpi f := IsSplitEpi.mk' { section_ := g, id := hgf }
  exact isIso_of_mono_of_isSplitEpi f

noncomputable instance rationalScalarExtension_rightAdjoint_instance
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).IsRightAdjoint :=
  rationalScalarExtension_isRightAdjoint l E F ι W

/-- The canonical left adjunction associated with the finite rational scalar extension. -/
noncomputable def rationalScalarExtension_leftAdjunction
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).leftAdjoint ⊣
      sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι := by
  exact Adjunction.ofIsRightAdjoint _

/-- Scalar extension along a finite field extension reflects isomorphisms on the
raw rational constructible categories.

Proof: represent a morphism by a localized integral morphism. Restriction of
scalars along the finite coefficient extension is faithful on the underlying
coefficient sheaves and detects quasi-isomorphisms after finite reduction.
The finite-free completed comparison identifies this restriction with the
recorded rational scalar functor after extension, so an isomorphism after scalar
extension has an invertible cone before extension. The same argument applies
on the full constructible subcategories. -/
theorem rationalScalarExtension_reflects_isomorphisms
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).ReflectsIsomorphisms := by
  let T := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  let U := T.leftAdjoint
  let b : U ⊣ T := Adjunction.ofIsRightAdjoint T
  exact reflects_of_split_counit U T b
    (rationalScalarExtension_counit_objectwise_split l E F ι W U b)

end WeilConjectures
