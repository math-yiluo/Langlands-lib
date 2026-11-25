/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroLocalization
public import WeilConjectures.TraceFormula.CurveLocal.SectionsRestrictionOpen

/-!

# From the supported restriction to a punctured restriction

Let `b : B ⟶ T`, `a : G ⟶ T` and `y : Y ⟶ B` be as in
`WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroLocalization`, so that the supported
restriction `ρ_{a,b} : RΓ_G(T, P) ⟶ RΓ_Y(B, b^* P)` is defined, and let `O ⊆ T ∖ G` be an open
subscheme such that the punctured curve `U = B ∖ Y` maps into `O` (in the blueprint,
`O = T ∖ (G ∪ V)` is the complement of the Frobenius graph and the vertical axis, and the
punctured diagonal `B ∖ y` lies in `T ∖ (H ∪ V ∪ G)`). If `RΓ(T, P) = 0` and `RΓ(B, b^* P) = 0`
and the restriction
```
RΓ(O, P) ⟶ RΓ(U, P|_U)
```
vanishes, then `ρ_{a,b} = 0`
(`AlgebraicGeometry.Etale.sectionsWithSupportRestriction_eq_zero_of_restriction`).

This is the reduction step of the proof of blueprint `lemma-vanishing-local-term-zero-stalk`
(`lemma-vanishing-local-term-zero-stalk--1` (iii)): by the localization triangles `ρ_{a,b}` vanishes
if and only if the restriction `RΓ(T ∖ G, P) ⟶ RΓ(B ∖ Y, b^* P)` does, and this restriction
factors through `RΓ(O, P)`, since `U ⊆ O ⊆ T ∖ G`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite Pretriangulated

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- A natural transformation of additive functors vanishes on an object if and only if it
vanishes on an isomorphic object. -/
lemma _root_.CategoryTheory.NatTrans.app_eq_zero_iff_of_iso {C D : Type*} [Category C]
    [Category D] [Preadditive D] {F G : C ⥤ D} (α : F ⟶ G) {K₁ K₂ : C} (e : K₁ ≅ K₂) :
    α.app K₁ = 0 ↔ α.app K₂ = 0 := by
  have h₁ := α.naturality e.hom
  have h₂ := α.naturality e.inv
  constructor
  · intro h
    rw [← Category.id_comp (α.app K₂), ← F.map_id, ← e.inv_hom_id, F.map_comp, assoc, h₁, h,
      zero_comp, comp_zero]
  · intro h
    rw [← Category.id_comp (α.app K₁), ← F.map_id, ← e.hom_inv_id, F.map_comp, assoc, h₂, h,
      zero_comp, comp_zero]

/-- Restrictions of derived sections along equal morphisms vanish simultaneously. -/
lemma sectionsRestriction_app_eq_zero_iff_of_eq {X X' : Scheme.{u}} {e₁ e₂ : X' ⟶ X}
    (he : e₁ = e₂) {V : X.Etale} {W : X'.Etale} {φ₁ φ₂ : W.left ⟶ V.left} (hφ : φ₁ = φ₂)
    (hφ₁ : φ₁ ≫ V.hom = W.hom ≫ e₁) (hφ₂ : φ₂ ≫ V.hom = W.hom ≫ e₂)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (sectionsRestriction A e₁ φ₁ hφ₁).app K = 0 ↔ (sectionsRestriction A e₂ φ₂ hφ₂).app K = 0 := by
  subst he hφ
  rfl

/-- A composite of restrictions vanishes if and only if the restriction along the composite
does. -/
lemma sectionsRestriction_comp_app_eq_zero_iff {X X' X'' : Scheme.{u}} (e : X' ⟶ X)
    (e' : X'' ⟶ X') {V : X.Etale} {W : X'.Etale} {W'' : X''.Etale}
    (φ : W.left ⟶ V.left) (hφ : φ ≫ V.hom = W.hom ≫ e) (φ' : W''.left ⟶ W.left)
    (hφ' : φ' ≫ W.hom = W''.hom ≫ e') (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (sectionsRestriction A e φ hφ).app K ≫
        (sectionsRestriction A e' φ' hφ').app ((e)^*[A].mapDerivedCategory.obj K) = 0 ↔
      (sectionsRestriction A (e' ≫ e) (φ' ≫ φ) (by rw [assoc, hφ, ← assoc, hφ', assoc])).app K
        = 0 := by
  rw [← sectionsRestriction_comp]
  exact Preadditive.IsIso.comp_right_eq_zero _ _

variable {T B G Y : Scheme.{u}} (b : B ⟶ T) (a : G ⟶ T) [IsClosedImmersion a] (y : Y ⟶ B)
  [IsClosedImmersion y] (h : y.openComplement ≤ b ⁻¹ᵁ a.openComplement) (O : T.Opens)
  (hw : O ≤ a.openComplement)
  (ψ : y.openComplement.toScheme ⟶ O.toScheme)
  (hψ : ψ ≫ O.ι = y.openComplement.ι ≫ b)

include hw hψ in
/-- **Reduction of the supported restriction to a punctured restriction** (blueprint
`lemma-vanishing-local-term-zero-stalk--1` (iii), as used in the proof of
`lemma-vanishing-local-term-zero-stalk`): if `RΓ(T, P) = 0`, `RΓ(B, b^* P) = 0`, and the restriction
`RΓ(O, P) ⟶ RΓ(B ∖ Y, P)` along `ψ : B ∖ Y ⟶ O` vanishes, where `O ⊆ T ∖ G`, then the
supported restriction `ρ_{a,b}` vanishes. -/
theorem sectionsWithSupportRestriction_eq_zero_of_restriction
    (P : DerivedCategory.Plus (Sheaf T.smallEtaleTopology A))
    (hT : IsZero ((sectionsWithSupportTriangle A a).obj P).obj₂)
    (hB : IsZero ((sectionsWithSupportTriangle A y).obj
      ((Functor.mapDerivedCategoryPlus (b)^*[A]).obj P)).obj₂)
    (hr : (sectionsRestriction A (ψ ≫ O.ι) (V := Scheme.Etale.mk O.ι)
      (W := Scheme.Etale.mk (𝟙 _)) ψ (Category.id_comp _).symm).app P.obj = 0) :
    sectionsWithSupportRestriction A b a y h P = 0 := by
  rw [sectionsWithSupportRestriction_eq_zero_iff A b a y h P hT hB, puncturedRestrictionMap,
    sectionsWithSupportTrianglePullback_app_hom₃]
  -- the restriction to `B ∖ Y`, composed with the identification of the sections over the open
  -- `B ∖ Y` with the global sections of the scheme `B ∖ Y`, is the restriction along
  -- `B ∖ Y ⟶ T ∖ G`, which factors through `T ∖ W`
  have := isIso_sectionsRestriction_openComplement A y rfl ((b)^*[A].mapDerivedCategory.obj P.obj)
  refine (Preadditive.IsIso.comp_right_eq_zero _ ((sectionsRestriction A y.openComplement.ι
    (V := Scheme.Etale.mk y.openComplement.ι) (W := Scheme.Etale.mk (𝟙 _)) (𝟙 _)
    rfl).app ((b)^*[A].mapDerivedCategory.obj P.obj))).1 ?_
  refine (sectionsRestriction_comp_app_eq_zero_iff A b y.openComplement.ι _ _ _ _ P.obj).2 ?_
  have hfac := (sectionsRestriction_comp_app_eq_zero_iff A (𝟙 T) (ψ ≫ O.ι)
    (V := Scheme.Etale.mk a.openComplement.ι) (W := Scheme.Etale.mk O.ι)
    (W'' := Scheme.Etale.mk (𝟙 _)) (Scheme.Hom.resLE (𝟙 T) a.openComplement O hw)
    (Scheme.Hom.resLE_comp_ι _ _) ψ
    (Category.id_comp _).symm P.obj).1
  refine (sectionsRestriction_app_eq_zero_iff_of_eq A ?_ ?_ _ _ _).1 (hfac ?_)
  · simp [hψ]
  · change ψ ≫ Scheme.Hom.resLE (𝟙 T) a.openComplement O hw =
      𝟙 _ ≫ Scheme.Hom.resLE b _ _ h
    rw [← cancel_mono a.openComplement.ι]
    simp [hψ]
  · have e : (𝟙 T)^*[A].mapDerivedCategory.obj P.obj ≅ P.obj :=
      (Functor.mapDerivedCategoryNatIso (Etale.upperStarId A T) ≪≫
        Functor.mapDerivedCategoryIdIso _).app P.obj
    rw [(NatTrans.app_eq_zero_iff_of_iso _ e).2 hr, comp_zero]

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Restriction from an open subscheme.** For an open `O ⊆ T`, a morphism `ψ : U ⟶ O` and an
isomorphism `F|_O ≅ G`, the restriction `RΓ(O, F) ⟶ RΓ(U, ψ^* F)` of the sections of `F` over the
étale `T`-scheme `O` vanishes as soon as the restriction `RΓ(O, G) ⟶ RΓ(U, ψ^* G)` of the global
sections of the scheme `O` does. -/
lemma sectionsRestriction_app_eq_zero_of_isOpenImmersion {T U : Scheme.{u}} (O : T.Opens)
    (ψ : U ⟶ O.toScheme) (F : DerivedCategory (Sheaf T.smallEtaleTopology A))
    (G : DerivedCategory (Sheaf O.toScheme.smallEtaleTopology A))
    (e : (O.ι)^*[A].mapDerivedCategory.obj F ≅ G)
    (hG : (sectionsRestriction A ψ (V := Scheme.Etale.mk (𝟙 _)) (W := Scheme.Etale.mk (𝟙 _)) ψ
      ((Category.comp_id _).trans (Category.id_comp _).symm)).app G = 0) :
    (sectionsRestriction A (ψ ≫ O.ι) (V := Scheme.Etale.mk O.ι) (W := Scheme.Etale.mk (𝟙 _)) ψ
      (Category.id_comp _).symm).app F = 0 := by
  have := isIso_sectionsRestriction_of_isOpenImmersion A O.ι rfl F
  have h₁ := (sectionsRestriction_comp_app_eq_zero_iff A O.ι ψ
    (V := Scheme.Etale.mk O.ι) (W := Scheme.Etale.mk (𝟙 _)) (W'' := Scheme.Etale.mk (𝟙 _))
    (𝟙 _) rfl ψ ((Category.comp_id _).trans (Category.id_comp _).symm) F).1 (by
      rw [(NatTrans.app_eq_zero_iff_of_iso _ e).2 hG, comp_zero])
  exact (sectionsRestriction_app_eq_zero_iff_of_eq A rfl (Category.comp_id ψ) _ _ F).1 h₁

end AlgebraicGeometry.Etale
