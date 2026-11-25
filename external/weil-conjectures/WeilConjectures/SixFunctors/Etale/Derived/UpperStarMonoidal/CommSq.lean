/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.KernelAdjunctionClass
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# Derived pullbacks along two morphisms with the same composite

For `a, b : T ⟶ S` and `q : S ⟶ R` with `a ≫ q = b ≫ q`, the composition isomorphisms give
`e : Lq^* ⋙ La^* ≅ L(aq)^* = L(bq)^* ≅ Lq^* ⋙ Lb^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarCompSquareIso`); for `s : U ⟶ T` with
`s ≫ a = s ≫ b` they give `ι : La^* ⋙ Ls^* ≅ Lb^* ⋙ Ls^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarSectionSquareIso`). Both are monoidal, in the forms
of the hypotheses `he`, `he₀` and `hι` of `CategoryTheory.Adjunction.kernelAdjunction` (for the two
projections `a, b` of `ℙ¹_P = P ×_S P` and the diagonal `s`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

attribute [local instance] leftDerivedUpperStarMonoidal

section Square

variable {T S R : Scheme.{u}} (a b : T ⟶ S) (q : S ⟶ R) (fg : T ⟶ R) (ha : fg = a ≫ q)
  (hb : fg = b ≫ q)

/-- For `fg = a ≫ q = b ≫ q`, the isomorphism `Lq^* ⋙ La^* ≅ L(fg)^* ≅ Lq^* ⋙ Lb^*` given by the
composition isomorphisms. -/
noncomputable def leftDerivedUpperStarCompSquareIso :
    L((q)^*[A]) ⋙ L((a)^*[A]) ≅ L((q)^*[A]) ⋙ L((b)^*[A]) :=
  (leftDerivedUpperStarComp A a q fg ha).symm ≪≫ leftDerivedUpperStarComp A b q fg hb

omit [UpperStarPreservesFlat A] in
/-- The isomorphism `Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` does not depend on the chosen composite. -/
lemma leftDerivedUpperStarCompSquareIso_congr (fg' : T ⟶ R) (ha' : fg' = a ≫ q)
    (hb' : fg' = b ≫ q) :
    leftDerivedUpperStarCompSquareIso A a b q fg ha hb =
      leftDerivedUpperStarCompSquareIso A a b q fg' ha' hb' := by
  obtain rfl : fg = fg' := ha.trans ha'.symm
  rfl

omit [UpperStarPreservesFlat A] in
/-- The inverse of `Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` is `Lq^* ⋙ Lb^* ≅ Lq^* ⋙ La^*`. -/
lemma leftDerivedUpperStarCompSquareIso_symm :
    (leftDerivedUpperStarCompSquareIso A a b q fg ha hb).symm =
      leftDerivedUpperStarCompSquareIso A b a q fg hb ha := by
  rw [leftDerivedUpperStarCompSquareIso, leftDerivedUpperStarCompSquareIso, Iso.trans_symm,
    Iso.symm_symm_eq]

/-- The isomorphism `Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` of a commutative square is compatible with the
tensor structures (the hypothesis `he` of `CategoryTheory.Adjunction.kernelAdjunction`). -/
lemma map_μ_comp_leftDerivedUpperStarCompSquareIso_hom_app
    (Y X : _root_.DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    L((a)^*[A]).map (μ L((q)^*[A]) Y X) ≫
        (leftDerivedUpperStarCompSquareIso A a b q fg ha hb).hom.app (Y ⊗ X) =
      δ L((a)^*[A]) (L((q)^*[A]).obj Y) (L((q)^*[A]).obj X) ≫
        ((leftDerivedUpperStarCompSquareIso A a b q fg ha hb).hom.app Y ⊗ₘ
          (leftDerivedUpperStarCompSquareIso A a b q fg ha hb).hom.app X) ≫
        μ L((b)^*[A]) (L((q)^*[A]).obj Y) (L((q)^*[A]).obj X) ≫
          L((b)^*[A]).map (μ L((q)^*[A]) Y X) :=
  Adjunction.map_μ_comp_trans_hom_app _ _
    (leftDerivedUpperStarTensorComparison_comp A a q fg ha)
    (leftDerivedUpperStarTensorComparison_comp A b q fg hb) Y X

/-- The isomorphism `Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` of a commutative square is compatible with the
units (the hypothesis `he₀` of `CategoryTheory.Adjunction.kernelAdjunction`). -/
lemma leftDerivedUpperStarCompSquareIso_hom_app_tensorUnit_comp_η
    [NatTrans.IsMonoidal (Etale.upperStarComp A a q fg ha).hom]
    [NatTrans.IsMonoidal (Etale.upperStarComp A b q fg hb).hom] :
    (leftDerivedUpperStarCompSquareIso A a b q fg ha hb).hom.app (𝟙_ _) ≫
        L((b)^*[A]).map (η L((q)^*[A])) ≫ η L((b)^*[A]) =
      L((a)^*[A]).map (η L((q)^*[A])) ≫ η L((a)^*[A]) :=
  Adjunction.trans_hom_app_tensorUnit_comp_η _ _
    (leftDerivedUpperStarComp_hom_app_unit A a q fg ha)
    (leftDerivedUpperStarComp_hom_app_unit A b q fg hb)

end Square

section Section

variable {U T S : Scheme.{u}} (a b : T ⟶ S) (s : U ⟶ T) (h : s ≫ a = s ≫ b)

/-- For `s ≫ a = s ≫ b`, the isomorphism `La^* ⋙ Ls^* ≅ L(sa)^* = L(sb)^* ≅ Lb^* ⋙ Ls^*` given by
the composition isomorphisms. -/
noncomputable def leftDerivedUpperStarSectionSquareIso :
    L((a)^*[A]) ⋙ L((s)^*[A]) ≅ L((b)^*[A]) ⋙ L((s)^*[A]) :=
  (leftDerivedUpperStarComp A s a (s ≫ a) rfl).symm ≪≫ leftDerivedUpperStarComp A s b (s ≫ a) h

/-- The isomorphism `La^* ⋙ Ls^* ≅ Lb^* ⋙ Ls^*` is compatible with the tensor structures (the
hypothesis `hι` of `CategoryTheory.Adjunction.kernelAdjunction`). -/
lemma leftDerivedUpperStarSectionSquareIso_hom_app_tensor
    (M M' : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    (leftDerivedUpperStarSectionSquareIso A a b s h).hom.app (M ⊗ M') =
      L((s)^*[A]).map (δ L((a)^*[A]) M M') ≫ δ L((s)^*[A]) _ _ ≫
        ((leftDerivedUpperStarSectionSquareIso A a b s h).hom.app M ⊗ₘ
          (leftDerivedUpperStarSectionSquareIso A a b s h).hom.app M') ≫
        μ L((s)^*[A]) _ _ ≫ L((s)^*[A]).map (μ L((b)^*[A]) M M') :=
  Adjunction.trans_hom_app_tensor _ _
    (leftDerivedUpperStarTensorComparison_comp A s a (s ≫ a) rfl)
    (leftDerivedUpperStarTensorComparison_comp A s b (s ≫ a) h) M M'

omit [UpperStarPreservesFlat A] in
/-- On objects pulled back along `q` with `a ≫ q = b ≫ q`, the isomorphism
`La^* ⋙ Ls^* ≅ Lb^* ⋙ Ls^*` is `Ls^*` applied to the isomorphism `Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` (the
hypothesis `hιF` of `CategoryTheory.Adjunction.kernelAdjunction`). -/
lemma leftDerivedUpperStarSectionSquareIso_hom_app_obj {R : Scheme.{u}} (q : S ⟶ R)
    (fg : T ⟶ R) (ha : fg = a ≫ q) (hb : fg = b ≫ q)
    (X : _root_.DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    (leftDerivedUpperStarSectionSquareIso A a b s h).hom.app (L((q)^*[A]).obj X) =
      L((s)^*[A]).map ((leftDerivedUpperStarCompSquareIso A a b q fg ha hb).hom.app X) := by
  have hq : a ≫ q = b ≫ q := ha.symm.trans hb
  rw [leftDerivedUpperStarCompSquareIso_congr A a b q fg ha hb (a ≫ q) rfl hq]
  have h₁ := map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app A s a q
    (s ≫ a) (a ≫ q) ((s ≫ a) ≫ q) rfl rfl rfl X
  have h₂ := leftDerivedUpperStarComp_assoc'_app A s b q (s ≫ a) (a ≫ q) ((s ≫ a) ≫ q) h hq rfl X
  simp only [leftDerivedUpperStarSectionSquareIso, leftDerivedUpperStarCompSquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  rw [← cancel_epi (L((s)^*[A]).map ((leftDerivedUpperStarComp A a q (a ≫ q) rfl).hom.app X)),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% h₁, ← h₂, Iso.inv_hom_id_app_assoc]

end Section

end Etale

end AlgebraicGeometry
