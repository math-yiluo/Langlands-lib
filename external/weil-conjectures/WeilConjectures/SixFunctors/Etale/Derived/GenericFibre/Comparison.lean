/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Comparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Formal criteria for the internal-hom comparison of a monoidal functor

Let `G : C ⥤ D` be a strong monoidal functor between monoidal closed categories. Its comparison
map `ρ : G [K, M] ⟶ [G K, G M]` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), the
transpose of `G K ⊗ G [K, M] ≅ G (K ⊗ [K, M]) ⟶ G M`, is compatible with evaluation by
construction. This file collects formal criteria for `ρ` to be an isomorphism, used for the
internal-hom comparison of blueprint `lemma-restriction-geometric-generic-fibre`
(`WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom`):

* `ρ` is an isomorphism at `K` if `K` has a left dual
  (`CategoryTheory.Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing`): this is the
  site-perfect case;
* if `G ⊣ H` with invertible counit (`H` fully faithful), `ρ` is an isomorphism at every
  `(K, H N)` (`CategoryTheory.Functor.Monoidal.isIso_ihomComparison_app_rightAdjoint`); in
  passing, `[K, H N] ≅ H [G K, N]`
  (`CategoryTheory.Functor.Monoidal.isIso_ihomRightAdjointComparison`);
* `ρ` is transported along monoidal natural isomorphisms
  (`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso`).

It also contains two formal lemmas on pretriangulated categories, used for the dévissage:
`CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃_of_subsingleton`, a five lemma in which the
compatibility with the connecting morphisms is replaced by a vanishing of morphisms, and
`CategoryTheory.Adjunction.isIso_of_isIso_map_of_iso_rightAdjoint_obj`, the conservativity of the
left adjoint on the essential image of a fully faithful right adjoint.
-/

@[expose] public section

namespace CategoryTheory.Functor.Monoidal

open MonoidalCategory MonoidalClosed LaxMonoidal OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D) [G.Monoidal]

/-- If `Y` is a left dual of `X`, the comparison map `G [X, 𝟙] ⟶ [G X, G 𝟙]` is an
isomorphism: precomposed with `G` of `Y ≅ [X, 𝟙]` and followed by `[G X, G 𝟙] ≅ [G X, 𝟙]`, it is
the isomorphism `G Y ≅ [G X, 𝟙]` of the mapped exact pairing. -/
lemma isIso_ihomComparison_app_unit_of_exactPairing (Y X : C) [ExactPairing Y X] :
    IsIso ((ihomComparison G X).app (𝟙_ C)) := by
  let := ExactPairing.map G Y X
  have h : G.map (curry (ε_ Y X)) ≫ (ihomComparison G X).app (𝟙_ C) ≫
      (ihom (G.obj X)).map (η G) = curry (ε_ (G.obj Y) (G.obj X)) := by
    rw [ihomComparison_app_eq_curry]
    simp only [← curry_natural_right, ← curry_natural_left, Category.assoc]
    congr 1
    rw [μ_natural_right_assoc, ← G.map_comp_assoc, ← uncurry_eq, uncurry_curry]
    rfl
  have : IsIso (G.map (curry (ε_ Y X)) ≫ (ihomComparison G X).app (𝟙_ C) ≫
      (ihom (G.obj X)).map (η G)) := by rw [h]; infer_instance
  have : IsIso ((ihomComparison G X).app (𝟙_ C) ≫ (ihom (G.obj X)).map (η G)) :=
    IsIso.of_isIso_comp_left (G.map (curry (ε_ Y X))) _
  exact IsIso.of_isIso_comp_right _ ((ihom (G.obj X)).map (η G))

/-- **The comparison map at a dualizable object.** If `Y` is a left dual of `X`, the comparison
map `G [X, Z] ⟶ [G X, G Z]` of a monoidal functor is an isomorphism for every `Z`: both sides
are `Y ⊗ Z` (`CategoryTheory.Functor.Monoidal.map_ihomUnitTensorToIhom_comp`), and the case
`Z = 𝟙` is `isIso_ihomComparison_app_unit_of_exactPairing`. -/
lemma isIso_ihomComparison_app_of_exactPairing (Y X : C) [ExactPairing Y X] (Z : C) :
    IsIso ((ihomComparison G X).app Z) := by
  let := ExactPairing.map G Y X
  have := isIso_ihomComparison_app_unit_of_exactPairing G Y X
  have := isIso_ihomUnitTensorToIhom Y X Z
  have := isIso_ihomUnitTensorToIhom (G.obj Y) (G.obj X) (G.obj Z)
  have h := map_ihomUnitTensorToIhom_comp G X Z
  have : IsIso (G.map (ihomUnitTensorToIhom X Z) ≫ (ihomComparison G X).app Z) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (G.map (ihomUnitTensorToIhom X Z)) _

variable {G} {H : D ⥤ C} (adj : G ⊣ H)

/-- For an adjunction `G ⊣ H` with `G` strong monoidal, the canonical map
`[K, H N] ⟶ H [G K, N]`: the transpose along `G ⊣ H` of the transpose
`G [K, H N] ⟶ [G K, N]` of `G K ⊗ G [K, H N] ≅ G (K ⊗ [K, H N]) ⟶ G H N ⟶ N`. -/
noncomputable def ihomRightAdjointComparison (K : C) (N : D) :
    (ihom K).obj (H.obj N) ⟶ H.obj ((ihom (G.obj K)).obj N) :=
  adj.homEquiv _ _ (curry (μ G K _ ≫ G.map ((ihom.ev K).app (H.obj N)) ≫ adj.counit.app N))

/-- For an adjunction `G ⊣ H` with `G` strong monoidal, `[K, H N] ≅ H [G K, N]`: maps
`W ⟶ [K, H N]` and `W ⟶ H [G K, N]` both correspond to maps `G K ⊗ G W ≅ G (K ⊗ W) ⟶ N`. -/
lemma isIso_ihomRightAdjointComparison (K : C) (N : D) :
    IsIso (ihomRightAdjointComparison adj K N) := by
  refine isIso_of_yoneda_map_bijective _ fun W ↦ ?_
  have key : ∀ x : W ⟶ (ihom K).obj (H.obj N), x ≫ ihomRightAdjointComparison adj K N =
      adj.homEquiv _ _ (curry (μ G K W ≫ G.map (uncurry x) ≫ adj.counit.app N)) := by
    intro x
    rw [ihomRightAdjointComparison, ← Adjunction.homEquiv_naturality_left,
      ← curry_natural_left, μ_natural_right_assoc, ← G.map_comp_assoc, uncurry_eq]
    rfl
  let e : (W ⟶ (ihom K).obj (H.obj N)) ≃ (W ⟶ H.obj ((ihom (G.obj K)).obj N)) :=
    ((ihom.adjunction K).homEquiv _ _).symm.trans (((adj.homEquiv _ _).symm.trans
      ((asIso (μ G K W)).homCongr (Iso.refl _)).symm).trans
        ((((ihom.adjunction (G.obj K)).homEquiv _ _)).trans (adj.homEquiv _ _)))
  convert e.bijective using 1
  ext x
  rw [key]
  simp only [e, Equiv.trans_apply]
  congr 1
  simp only [Iso.homCongr_symm, Iso.homCongr_apply, Adjunction.homEquiv_counit, Iso.symm_inv,
    asIso_hom, Iso.refl_symm, Iso.refl_hom, Category.comp_id]
  rfl

/-- **The comparison map into a fully faithful right adjoint.** Let `G ⊣ H` with `G` strong
monoidal and invertible counit. Then the comparison map `G [K, H N] ⟶ [G K, G H N]` is an
isomorphism for all `K` and `N`: followed by `[G K, G H N] ≅ [G K, N]`, it is the transpose
`G [K, H N] ⟶ [G K, N]` of the isomorphism `[K, H N] ≅ H [G K, N]`
(`CategoryTheory.Functor.Monoidal.isIso_ihomRightAdjointComparison`). For a closed immersion
`i` this says that `i^* RHom(K, Ri_* N) ≅ RHom(i^* K, i^* Ri_* N)`, and likewise for an open
immersion. -/
lemma isIso_ihomComparison_app_rightAdjoint [IsIso adj.counit] (K : C) (N : D) :
    IsIso ((ihomComparison G K).app (H.obj N)) := by
  let σ : G.obj ((ihom K).obj (H.obj N)) ⟶ (ihom (G.obj K)).obj N :=
    curry (μ G K _ ≫ G.map ((ihom.ev K).app (H.obj N)) ≫ adj.counit.app N)
  have hσ : (ihomComparison G K).app (H.obj N) ≫ (ihom (G.obj K)).map (adj.counit.app N)
      = σ := by
    rw [ihomComparison_app_eq_curry, ← curry_natural_right, Category.assoc]
  have := isIso_ihomRightAdjointComparison adj K N
  have : IsIso σ := by
    have : σ = G.map (ihomRightAdjointComparison adj K N) ≫ adj.counit.app _ := by
      calc σ = (adj.homEquiv _ _).symm (ihomRightAdjointComparison adj K N) := by
            simp [ihomRightAdjointComparison, σ]
        _ = _ := adj.homEquiv_counit _ _ _
    rw [this]; infer_instance
  rw [← hσ] at this
  exact IsIso.of_isIso_comp_right _ ((ihom (G.obj K)).map (adj.counit.app N))

end CategoryTheory.Functor.Monoidal

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory MonoidalClosed

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D]

/-- The comparison maps `F [A, B] ⟶ [F A, F B]` and `F' [A, B] ⟶ [F' A, F' B]` of two monoidally
isomorphic lax monoidal functors are isomorphisms at the same objects
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison_app_comp_map_app`). -/
lemma isIso_ihomComparison_app_iff_of_iso {F F' : C ⥤ D} [F.LaxMonoidal] [F'.LaxMonoidal]
    (τ : F ≅ F') [NatTrans.IsMonoidal τ.hom] (A B : C) :
    IsIso ((ihomComparison F A).app B) ↔ IsIso ((ihomComparison F' A).app B) := by
  have h := ihomComparison_app_comp_map_app τ.hom A B
  constructor
  · intro _
    have : IsIso (τ.hom.app _ ≫ (ihomComparison F' A).app B ≫
        (pre (τ.hom.app A)).app (F'.obj B)) := by rw [← h]; infer_instance
    have : IsIso ((ihomComparison F' A).app B ≫ (pre (τ.hom.app A)).app (F'.obj B)) :=
      IsIso.of_isIso_comp_left (τ.hom.app _) _
    exact IsIso.of_isIso_comp_right _ ((pre (τ.hom.app A)).app (F'.obj B))
  · intro _
    have : IsIso ((ihomComparison F A).app B ≫ (ihom (F.obj A)).map (τ.hom.app B)) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((ihom (F.obj A)).map (τ.hom.app B))

end CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory.Pretriangulated

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **A five lemma without the connecting morphisms.** Let `T₁` and `T₂` be distinguished
triangles and `φᵢ : T₁.objᵢ ⟶ T₂.objᵢ` maps compatible with the first two morphisms of the
triangles, but not necessarily with the connecting morphisms. If there are no nonzero maps
`T₁.obj₁⟦1⟧ ⟶ T₂.obj₃` and `φ₁`, `φ₃` are isomorphisms, then so is `φ₂`: the map
`T₁.obj₃ ⟶ T₂.obj₃` completing `(φ₁, φ₂)` to a morphism of triangles is forced to be `φ₃`. -/
lemma isIso₂_of_isIso₁₃_of_subsingleton {T₁ T₂ : Triangle C} (hT₁ : T₁ ∈ distTriang C)
    (hT₂ : T₂ ∈ distTriang C) (φ₁ : T₁.obj₁ ⟶ T₂.obj₁) (φ₂ : T₁.obj₂ ⟶ T₂.obj₂)
    (φ₃ : T₁.obj₃ ⟶ T₂.obj₃) (h₁ : T₁.mor₁ ≫ φ₂ = φ₁ ≫ T₂.mor₁)
    (h₂ : T₁.mor₂ ≫ φ₃ = φ₂ ≫ T₂.mor₂) (h : Subsingleton (T₁.obj₁⟦(1 : ℤ)⟧ ⟶ T₂.obj₃))
    [IsIso φ₁] [IsIso φ₃] : IsIso φ₂ := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism _ _ hT₁ hT₂ φ₁ φ₂ h₁
  have hc : c = φ₃ := by
    rw [← sub_eq_zero]
    obtain ⟨d, hd⟩ := Triangle.yoneda_exact₃ _ hT₁ (c - φ₃) (by
      rw [Preadditive.comp_sub, hc₂, h₂, sub_self])
    rw [hd, h.elim d 0, comp_zero]
  subst hc
  exact isIso₂_of_isIso₁₃ (Triangle.homMk _ _ φ₁ φ₂ c h₁ hc₂ hc₃) hT₁ hT₂
    (inferInstanceAs (IsIso φ₁)) (inferInstanceAs (IsIso c))

end CategoryTheory.Pretriangulated

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H)
  [IsIso adj.counit]

/-- The unit of an adjunction with invertible counit is invertible on every object isomorphic to
an object in the image of the right adjoint. -/
lemma isIso_unit_app_of_iso_rightAdjoint_obj {A : C} {N : D} (e : A ≅ H.obj N) :
    IsIso (adj.unit.app A) := by
  have : IsIso (adj.unit.app (H.obj N)) := by
    have h := adj.right_triangle_components N
    have : IsIso (adj.unit.app (H.obj N) ≫ H.map (adj.counit.app N)) := by
      rw [h]; exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (H.map (adj.counit.app N))
  exact (NatTrans.isIso_app_iff_of_iso adj.unit e).2 this

include adj in
/-- **Conservativity on the essential image of a fully faithful right adjoint.** Let `F ⊣ H`
have invertible counit. A morphism between objects isomorphic to objects in the image of `H` is
an isomorphism as soon as its image under `F` is. -/
lemma isIso_of_isIso_map_of_iso_rightAdjoint_obj {A B : C} {N N' : D} (eA : A ≅ H.obj N)
    (eB : B ≅ H.obj N') (φ : A ⟶ B) [IsIso (F.map φ)] : IsIso φ := by
  have := adj.isIso_unit_app_of_iso_rightAdjoint_obj eA
  have := adj.isIso_unit_app_of_iso_rightAdjoint_obj eB
  have h : φ ≫ adj.unit.app B = adj.unit.app A ≫ H.map (F.map φ) := adj.unit.naturality φ
  have : IsIso (φ ≫ adj.unit.app B) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right φ (adj.unit.app B)

end CategoryTheory.Adjunction
