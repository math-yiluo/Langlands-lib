/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom

/-!
# Tensoring with a lisse sheaf is exact

For a lisse sheaf `F` of `ℚ̄_ℓ,X`-modules, the tensor product `- ⊗_{ℚ̄_ℓ,X} F` preserves
monomorphisms (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.mono_tensorLeft_map`): this can be
checked after pullback along the members of a pro-étale cover trivialising `F`, where `F`
becomes `ℚ̄_ℓⁿ` and `- ⊗ ℚ̄_ℓⁿ = (-)ⁿ` (`CategoryTheory.Mod.mono_tensorLeft_map_of_iso_biproduct`).
Being right exact as a left adjoint, it is exact, so that its right adjoint, the internal hom
`𝓗om(F, -)`, preserves K-injective complexes
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesKInjectiveComplexes_ihom`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {A : C}
  [MonObj A] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]

attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

/-- `- ⊗_A ·` as an additive map on morphisms in the second variable. -/
@[simps]
noncomputable def tensorLeftMapAddHom (M M' : Mod C A) :
    (M ⟶ M') →+ (tensorLeft M ⟶ tensorLeft M') where
  toFun := tensorLeftMap
  map_zero' := by
    have h := tensorLeftMap_add (0 : M ⟶ M') 0
    rwa [add_zero, left_eq_add] at h
  map_add' := tensorLeftMap_add

lemma sum_tensorLeftMap_π_comp_tensorLeftMap_ι {n : ℕ} (M : Fin n → Mod C A) :
    ∑ i, tensorLeftMap (biproduct.π M i) ≫ tensorLeftMap (biproduct.ι M i) =
      𝟙 (tensorLeft (⨁ M)) := by
  simp_rw [← tensorLeftMap_comp]
  calc ∑ i, tensorLeftMap (biproduct.π M i ≫ biproduct.ι M i) =
      tensorLeftMapAddHom (⨁ M) (⨁ M) (∑ i, biproduct.π M i ≫ biproduct.ι M i) := by
        rw [map_sum]; rfl
    _ = 𝟙 _ := by rw [biproduct.total]; exact tensorLeftMap_id _

/-- `- ⊗_A (⨁ᵢ Mᵢ)` preserves monomorphisms if each `- ⊗_A Mᵢ` does: it is the direct sum of
the `- ⊗_A Mᵢ`. -/
lemma mono_tensorLeft_biproduct_map {n : ℕ} (M : Fin n → Mod C A) {N N' : Mod C A}
    (f : N ⟶ N') (h : ∀ i, Mono ((tensorLeft (M i)).map f)) :
    Mono ((tensorLeft (⨁ M)).map f) := by
  refine Preadditive.mono_of_cancel_zero _ fun {Z} g hg ↦ ?_
  have hi (i : Fin n) : g ≫ (tensorLeftMap (biproduct.π M i)).app N = 0 := by
    have := h i
    rw [← cancel_mono ((tensorLeft (M i)).map f), Category.assoc,
      ← (tensorLeftMap (biproduct.π M i)).naturality, reassoc_of% hg, zero_comp, zero_comp]
  rw [← Category.comp_id g, ← NatTrans.id_app, ← sum_tensorLeftMap_π_comp_tensorLeftMap_ι M,
    NatTrans.app_sum, Preadditive.comp_sum]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [NatTrans.comp_app, reassoc_of% hi i, zero_comp]

/-- `- ⊗_A M` preserves monomorphisms for `M` free of finite rank. -/
lemma mono_tensorLeft_map_of_iso_biproduct {M : Mod C A} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ regular A) {N N' : Mod C A} (f : N ⟶ N') [Mono f] :
    Mono ((tensorLeft M).map f) := by
  have : Mono ((tensorLeft (⨁ fun _ : Fin n ↦ regular A)).map f) :=
    mono_tensorLeft_biproduct_map _ f fun _ ↦ by
      rw [← NatIso.naturality_2 tensorLeftRegularIso f]
      infer_instance
  rw [← NatIso.naturality_2 (tensorLeftMapIso e) f]
  infer_instance

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- **Tensoring with a lisse sheaf preserves monomorphisms**: after pullback along a member `g`
of a pro-étale cover trivialising `F`, it becomes tensoring with `ℚ̄_ℓⁿ`. -/
theorem IsAdicLisseSheaf.mono_tensorLeft_map {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F)
    {M N : AdicSheaf l X} (f : M ⟶ N) [Mono f] : Mono ((Mod.tensorLeft F).map f) := by
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨κ, V, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : κ) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  refine Preadditive.mono_of_isZero_kernel _
    (AdicSheaf.isZero_of_isZero_upperStar g hR fun i ↦ ?_)
  obtain ⟨n, ⟨e⟩⟩ := hRF (g i) (.mk i)
  have : Mono ((g i)^*ᵃ[l].map ((Mod.tensorLeft F).map f)) := by
    have key := NatIso.naturality_2 (adicUpperStarTensorLeftIso l (g i) F) f
    change Mono ((Mod.tensorLeft F ⋙ (g i)^*ᵃ[l]).map f)
    rw [← key]
    have := Mod.mono_tensorLeft_map_of_iso_biproduct e ((g i)^*ᵃ[l].map f)
    exact mono_comp' inferInstance (mono_comp' this inferInstance)
  exact (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso (g i)^*ᵃ[l] _)

/-- **Tensoring with a lisse sheaf is exact**: it is right exact as a left adjoint, and it
preserves monomorphisms (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.mono_tensorLeft_map`). -/
theorem IsAdicLisseSheaf.preservesHomology_tensorLeft {F : AdicSheaf l X}
    (hF : IsAdicLisseSheaf F) : (Mod.tensorLeft F).PreservesHomology := by
  have := (Mod.ihomAdjunction F).left_adjoint_additive
  have : (Mod.tensorLeft F).PreservesMonomorphisms := ⟨fun f _ ↦ hF.mono_tensorLeft_map f⟩
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- **The internal hom out of a lisse sheaf preserves K-injective complexes**: it is right
adjoint to the exact functor `- ⊗ F`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesHomology_tensorLeft`). -/
theorem IsAdicLisseSheaf.preservesKInjectiveComplexes_ihom {F : AdicSheaf l X}
    (hF : IsAdicLisseSheaf F) : (AdicSheaf.ihom F).PreservesKInjectiveComplexes := by
  have := (Mod.ihomAdjunction F).left_adjoint_additive
  have := hF.preservesHomology_tensorLeft
  exact (Mod.ihomAdjunction F).preservesKInjectiveComplexes

end AlgebraicGeometry.ProEtale
