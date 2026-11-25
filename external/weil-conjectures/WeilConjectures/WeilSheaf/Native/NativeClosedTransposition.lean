/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels

/-! # Formal consequences of the normalized closed comparison

Source: the evaluation and transposition paragraph of
prose-10-20, native comparison steps 7--8
(blueprint: lem-sf-native-closed-transposition).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b
open CategoryTheory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

section Closed
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)

private theorem uncurry_eq (T P Q : D) (g : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm g =
      S.tensor.map (Prod.mkHom g (𝟙 P)) ≫ S.evaluation P Q := by
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
    CoefficientClosedStructure.tensor, Adjunction.homEquiv, Equiv.symm]
  let := S.monoidal
  change S.monoidal.whiskerRight g P ≫ _ = S.monoidal.tensorHom g (𝟙 P) ≫ _
  rw [MonoidalCategory.tensorHom_id]

private theorem uncurry_precomp {T T' P Q : D} (f : T' ⟶ T)
    (g : T ⟶ H.obj (op P, Q)) :
    (S.transpose T' P Q).symm (f ≫ g) =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ (S.transpose T P Q).symm g := by
  rw [uncurry_eq, uncurry_eq, ← S.tensor.map_comp_assoc]
  simp

private theorem uncurry_hom_map {T P P' Q : D} (f : P' ⟶ P)
    (g : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P' Q).symm (g ≫ H.map (Prod.mkHom f.op (𝟙 Q))) =
      S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ (S.transpose T P Q).symm g := by
  rw [uncurry_eq, uncurry_eq]
  let := S.monoidal
  have ht := S.evaluation_naturality P P' Q f
  have ht' : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
    S.evaluation P' Q = S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) f) ≫
      S.evaluation P Q := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using ht
  calc
    _ = S.tensor.map (Prod.mkHom g (𝟙 P')) ≫
        S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
          S.evaluation P' Q := by
      rw [← S.tensor.map_comp_assoc]
      simp
    _ = S.tensor.map (Prod.mkHom g (𝟙 P')) ≫
        S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) f) ≫
          S.evaluation P Q := by rw [ht']
    _ = _ := by
      rw [← S.tensor.map_comp_assoc, ← S.tensor.map_comp_assoc]
      simp

/-- Biduality defined by transposing evaluation is natural, with no reflexivity
hypothesis. Source: native comparison step 8, naturality of evaluation and symmetry
(blueprint: lem-sf-native-closed-transposition).
Proof: uncurry both sides. Move the arrow across the symmetry and use naturality
of evaluation in its contravariant argument. The adjunction is injective. -/
theorem nativeBidual_natural (β : @SymmetricCategory D _ S.monoidal) :
    NativeBidualNaturality S β := by
  intro W K K' f
  apply (S.transpose K (H.obj (op K', W)) W).symm.injective
  rw [uncurry_precomp, uncurry_hom_map]
  simp only [nativeBidual, Equiv.symm_apply_apply]
  let := S.monoidal
  let := β
  have he := S.evaluation_naturality K' K W f
  have he' : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 W))) (𝟙 K)) ≫
      S.evaluation K W = S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K', W))) f) ≫
        S.evaluation K' W := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using he
  have h₁ := BraidedCategory.braiding_naturality f (𝟙 (H.obj (op K', W)))
  have h₂ := BraidedCategory.braiding_naturality (𝟙 K)
    (H.map (Prod.mkHom f.op (𝟙 W)))
  change S.tensor.map (Prod.mkHom f (𝟙 (H.obj (op K', W)))) ≫
      (β.toBraidedCategory.braiding K' (H.obj (op K', W))).hom =
    (β.toBraidedCategory.braiding K (H.obj (op K', W))).hom ≫
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K', W))) f) at h₁
  change S.tensor.map (Prod.mkHom (𝟙 K) (H.map (Prod.mkHom f.op (𝟙 W)))) ≫
      (β.toBraidedCategory.braiding K (H.obj (op K, W))).hom =
    (β.toBraidedCategory.braiding K (H.obj (op K', W))).hom ≫
      S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 W))) (𝟙 K)) at h₂
  simp only [← Category.assoc]
  rw [h₁, h₂]
  simp only [Category.assoc, he']

end Closed

section Comparison
variable {C : Type a} [Category.{b} C] {D : Type a} [Category.{b} D]
  {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
  (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
  (U : C ⥤ D) (τ : SC.tensor ⋙ U ≅ U.prod U ⋙ SD.tensor)
  (η : HC ⋙ U ≅ U.op.prod U ⋙ HD)
  (hη : ∀ K L, (η.app (op K, L)).hom = nativeHomComparison SC SD U τ K L)

include hη in
/-- The canonical Hom comparison preserves evaluation.
Source: native comparison step 7, the counit equation of the adjunction
(blueprint: lem-sf-native-closed-transposition).
Proof: uncurry the defining transpose of mapped evaluation, then cancel the
invertible tensor comparison. -/
theorem nativeComparison_evaluation : NativeEvaluationCompatibility SC SD U τ η := by
  intro K L
  have h := (SD.transpose _ (U.obj K) (U.obj L)).symm_apply_apply
    ((τ.app (HC.obj (op K, L), K)).inv ≫ U.map (SC.evaluation K L))
  rw [← nativeHomComparison, ← hη] at h
  rw [uncurry_eq] at h
  rw [h, Iso.hom_inv_id_assoc]

include hη in
private theorem uncurry_comparison (M K L : C) (f : M ⟶ HC.obj (op K, L)) :
    (SD.transpose (U.obj M) (U.obj K) (U.obj L)).symm
      (U.map f ≫ (η.app (op K, L)).hom) =
    (τ.app (M, K)).inv ≫ U.map ((SC.transpose M K L).symm f) := by
  rw [uncurry_precomp, hη]
  simp only [nativeHomComparison, Equiv.symm_apply_apply]
  have hn := τ.inv.naturality (Prod.mkHom f (𝟙 K))
  simp only [Functor.comp_map, Functor.prod_map, U.map_id] at hn
  change SD.tensor.map (Prod.mkHom (U.map f) (𝟙 (U.obj K))) ≫
      (τ.app (HC.obj (op K, L), K)).inv =
    (τ.app (M, K)).inv ≫ U.map (SC.tensor.map (Prod.mkHom f (𝟙 K))) at hn
  rw [← Category.assoc, hn, Category.assoc, ← U.map_comp, ← uncurry_eq]

include hη in
/-- A symmetric normalized closed comparison preserves the actual bidual arrow.
Source: native comparison step 8, transposition of evaluation after symmetry
(blueprint: lem-sf-native-closed-transposition).
Proof: uncurry the iterated Hom comparison. Its first inverse is in the
contravariant Hom argument. Symmetry compatibility moves the tensor comparison
past the braiding; evaluation compatibility cancels the remaining Hom comparison
with its inverse. Injectivity of the ordinary adjunction concludes. -/
theorem nativeComparison_bidual
    (βC : @SymmetricCategory C _ SC.monoidal)
    (βD : @SymmetricCategory D _ SD.monoidal)
    (hβ : NativeSymmetryCompatibility SC SD βC βD U τ) :
    NativeBidualCompatibility SC SD βC βD U η := by
  intro W K
  apply (SD.transpose (U.obj K) (HD.obj (op (U.obj K), U.obj W)) (U.obj W)).symm.injective
  rw [← Category.assoc (U.map _) (η.app _).hom, uncurry_hom_map,
    uncurry_comparison SC SD U τ η hη]
  simp only [nativeBidual, Equiv.symm_apply_apply, U.map_comp]
  have hs := hβ K (HC.obj (op K, W))
  have he := nativeComparison_evaluation SC SD U τ η hη K W
  have hs' : (τ.app (K, HC.obj (op K, W))).inv ≫
      U.map (βC.toBraidedCategory.braiding K (HC.obj (op K, W))).hom =
    (βD.toBraidedCategory.braiding (U.obj K) (U.obj (HC.obj (op K, W)))).hom ≫
      (τ.app (HC.obj (op K, W), K)).inv := by
    apply (cancel_mono (τ.app (HC.obj (op K, W), K)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hs, Iso.inv_hom_id_assoc]
  have he' : (τ.app (HC.obj (op K, W), K)).inv ≫ U.map (SC.evaluation K W) =
      SD.tensor.map (Prod.mkHom (η.app (op K, W)).hom (𝟙 (U.obj K))) ≫
        SD.evaluation (U.obj K) (U.obj W) := by
    rw [he, Iso.inv_hom_id_assoc]
  rw [← Category.assoc _ (U.map _), hs']
  simp only [Category.assoc, he']
  let := SD.monoidal
  let := βD
  have hn := BraidedCategory.braiding_naturality (𝟙 (U.obj K)) (η.app (op K, W)).inv
  change SD.tensor.map (Prod.mkHom (𝟙 (U.obj K)) (η.app (op K, W)).inv) ≫
      (βD.toBraidedCategory.braiding (U.obj K) (U.obj (HC.obj (op K, W)))).hom =
    (βD.toBraidedCategory.braiding (U.obj K) (HD.obj (op (U.obj K), U.obj W))).hom ≫
      SD.tensor.map (Prod.mkHom (η.app (op K, W)).inv (𝟙 (U.obj K))) at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← SD.tensor.map_comp_assoc]
  simp

end Comparison
end AlgebraicGeometry.ProEtaleWeilSheaf
