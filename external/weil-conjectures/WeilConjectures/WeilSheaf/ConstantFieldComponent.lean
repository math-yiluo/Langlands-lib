/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric

/-!
# The geometric fibre over a larger constant field

Let `k₀ ⊆ k'` be finite fields, `#k' = #k₀ ^ r`, and let `V` be a scheme over `k'` through
`c : V ⟶ Spec k'`, hence over `k₀` through `c ≫ Spec k' ⟶ Spec k₀`. The geometric fibre of `V`
over `k'` maps to the geometric fibre over `k₀`, through `τ⁻¹ : k̄ ≅ k̄'`
(`AlgebraicGeometry.algebraicClosureAlgEquiv`):
`θ : V ×_{k'} k̄' ⟶ V ×_{k₀} k̄` (`AlgebraicGeometry.Scheme.Hom.geometricFiberComponentMap`).
Its image is one of the `r` components `V ×_{k', τ} k̄` of `V ×_{k₀} k̄`, and it intertwines the
geometric Galois Frobenius of `V` over `k'` with the `r`-th power of that over `k₀`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberComponentMap_comp_geometricGaloisFrobenius_pow`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Algebra k₀ k'] [Algebra.IsAlgebraic k₀ k']
  {V : Scheme.{u}} (c : V ⟶ Spec (.of k')) (f : V ⟶ Spec (.of k₀))
  (hc : c ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) = f)

include hc in
/-- The map `θ : V ×_{k'} k̄' ⟶ V ×_{k₀} k̄` of geometric fibres, through `τ⁻¹ : k̄ ≅ k̄'`. -/
def geometricFiberComponentMap : c.geometricFiber ⟶ f.geometricFiber :=
  pullback.lift c.geometricFiberProj (c.geometricFiberToAlgebraicClosure ≫
    Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').symm.toRingHom)) (by
    rw [← hc, ← Category.assoc, geometricFiber_condition, Category.assoc, Category.assoc]
    refine congrArg (_ ≫ ·) ((spec_map_comp_spec_map_eq _ _ (algebraMap k₀ _) fun x ↦ ?_).trans
      (spec_map_comp_spec_map_eq _ _ _ fun x ↦ ?_).symm)
    · exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
    · simp)

@[reassoc (attr := simp)]
lemma geometricFiberComponentMap_comp_geometricFiberProj :
    geometricFiberComponentMap c f hc ≫ f.geometricFiberProj = c.geometricFiberProj :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma geometricFiberComponentMap_comp_geometricFiberToAlgebraicClosure :
    geometricFiberComponentMap c f hc ≫ f.geometricFiberToAlgebraicClosure =
      c.geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').symm.toRingHom) :=
  pullback.lift_snd _ _ _

variable [Finite k₀] [Finite k']

include hc in
/-- The component map intertwines the geometric Galois Frobenius of `V` over `k'` with the
`r`-th power of that over `k₀`, `#k' = #k₀ ^ r`: `Fr' ≫ θ = θ ≫ Frʳ`. -/
lemma geometricGaloisFrobenius_hom_comp_geometricFiberComponentMap (r : ℕ)
    (hr : Nat.card k' = Nat.card k₀ ^ r) :
    c.geometricGaloisFrobenius.asIso.hom ≫ geometricFiberComponentMap c f hc =
      geometricFiberComponentMap c f hc ≫ (f.geometricGaloisFrobenius ^ r).asIso.hom := by
  have hτ := spec_algebraicClosureAlgEquiv_comp_specGeometricFrobenius (k₀ := k₀) (k₀' := k') r hr
  have h₁ : Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').toRingHom) = 𝟙 _ := by
    rw [spec_map_comp_spec_map_eq _ _ (RingHom.id _) (fun x ↦ by simp), CommRingCat.ofHom_id,
      Spec.map_id]
  have h₂ : Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').symm.toRingHom) = 𝟙 _ := by
    rw [spec_map_comp_spec_map_eq _ _ (RingHom.id _) (fun x ↦ by simp), CommRingCat.ofHom_id,
      Spec.map_id]
  have hσ : (specGeometricFrobenius k').asIso.hom ≫
      Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').symm.toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').symm.toRingHom) ≫
        (specGeometricFrobenius k₀ ^ r).asIso.hom := by
    rw [← Category.id_comp (specGeometricFrobenius k').asIso.hom, ← h₁, Category.assoc,
      Category.assoc, reassoc_of% hτ, h₂, Category.comp_id]
  ext
  · simp
  · simp only [Category.assoc, geometricFiberComponentMap_comp_geometricFiberToAlgebraicClosure,
      geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure,
      geometricFiberComponentMap_comp_geometricFiberToAlgebraicClosure_assoc,
      geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure_assoc, hσ]

end AlgebraicGeometry.Scheme.Hom
