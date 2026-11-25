/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.Tactic.CategoryTheory.Reassoc

/-! # Naturality of a tensor-induced internal Hom comparison

Source: blueprint latest, lem-coef-finite-free-extension.proof.md,
the evaluation-transpose construction of the Hom comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
open CategoryTheory Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

namespace StageHomProof

local notation "uncurry₀" => Functor.uncurry.obj

variable {A B : Type*} [Category A] [Category B]

private theorem tensor_map_comp (T : A ⥤ A ⥤ A)
    {U V W X Y Z : A} (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z) :
    (uncurry₀ T).map (Prod.mkHom (f ≫ g) (h ≫ k)) =
      (uncurry₀ T).map (Prod.mkHom f h) ≫ (uncurry₀ T).map (Prod.mkHom g k) :=
  (uncurry₀ T).map_comp (Prod.mkHom f h) (Prod.mkHom g k)

private theorem tensor_right_comp (T : A ⥤ A ⥤ A) {K X Y Z : A}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (uncurry₀ T).map (Prod.mkHom (𝟙 K) (f ≫ g)) =
      (uncurry₀ T).map (Prod.mkHom (𝟙 K) f) ≫ (uncurry₀ T).map (Prod.mkHom (𝟙 K) g) := by
  simpa only [Category.id_comp] using tensor_map_comp T (𝟙 K) (𝟙 K) f g

private theorem evaluation_transport
    (T : A ⥤ A ⥤ A) (H : Aᵒᵖ ⥤ A ⥤ A)
    (adj : ∀ K : A, T.obj K ⊣ H.obj (op K))
    (hn : ∀ (K K' M : A) (f : K' ⟶ K),
      (uncurry₀ T).map (Prod.mkHom (𝟙 K') ((uncurry₀ H).map (Prod.mkHom f.op (𝟙 M)))) ≫
          (adj K').counit.app M =
        (uncurry₀ T).map (Prod.mkHom f (𝟙 _)) ≫ (adj K).counit.app M)
    (K K' M M' : A) (f : K' ⟶ K) (g : M ⟶ M') :
    (uncurry₀ T).map (Prod.mkHom (𝟙 K') ((uncurry₀ H).map (Prod.mkHom f.op g))) ≫
        (adj K').counit.app M' =
      (uncurry₀ T).map (Prod.mkHom f (𝟙 ((H.obj (op K)).obj M))) ≫
        (adj K).counit.app M ≫ g := by
  have hh : (uncurry₀ H).map (Prod.mkHom f.op g) =
      (uncurry₀ H).map (Prod.mkHom (𝟙 (op K)) g) ≫ (uncurry₀ H).map (Prod.mkHom f.op (𝟙 M')) := by
    rw [← (uncurry₀ H).map_comp]
    simp only [prod_comp, Category.id_comp, Category.comp_id]
  rw [hh, tensor_right_comp, Category.assoc, hn]
  have ht : (uncurry₀ T).map (Prod.mkHom (𝟙 K') ((uncurry₀ H).map (Prod.mkHom (𝟙 (op K)) g))) ≫
      (uncurry₀ T).map (Prod.mkHom f (𝟙 _)) =
      (uncurry₀ T).map (Prod.mkHom f (𝟙 _)) ≫
        (uncurry₀ T).map (Prod.mkHom (𝟙 K) ((uncurry₀ H).map (Prod.mkHom (𝟙 (op K)) g))) := by
    simp only [← (uncurry₀ T).map_comp, prod_comp, Category.id_comp, Category.comp_id]
  erw [← Category.assoc, ht, Category.assoc]
  congr 1
  simpa only [Functor.uncurry_obj_map, _root_.CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, Functor.comp_map, Functor.id_map] using (adj K).counit.naturality g

private def homMap
    {TA : A ⥤ A ⥤ A} {TB : B ⥤ B ⥤ B}
    {HA : Aᵒᵖ ⥤ A ⥤ A} {HB : Bᵒᵖ ⥤ B ⥤ B}
    (a : ∀ K : A, TA.obj K ⊣ HA.obj (op K))
    (b : ∀ K : B, TB.obj K ⊣ HB.obj (op K))
    (F : A ⥤ B) (μ : uncurry₀ TA ⋙ F ≅
      F.prod F ⋙ uncurry₀ TB) (K M : A) :
    F.obj ((HA.obj (op K)).obj M) ⟶ (HB.obj (op (F.obj K))).obj (F.obj M) :=
  (b (F.obj K)).homEquiv _ _ (μ.inv.app (K, (HA.obj (op K)).obj M) ≫
    F.map ((a K).counit.app M))

private theorem uncurry
    (T : A ⥤ A ⥤ A) (H : Aᵒᵖ ⥤ A ⥤ A)
    (a : ∀ K : A, T.obj K ⊣ H.obj (op K))
    {K M N : A} (f : N ⟶ (H.obj (op K)).obj M) :
    ((a K).homEquiv N M).symm f =
      (uncurry₀ T).map (Prod.mkHom (𝟙 K) f) ≫ (a K).counit.app M := by
  simpa only [Functor.uncurry_obj_map, _root_.CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] using (a K).homEquiv_counit N M f

private theorem homMap_eval
    {TA : A ⥤ A ⥤ A} {TB : B ⥤ B ⥤ B}
    {HA : Aᵒᵖ ⥤ A ⥤ A} {HB : Bᵒᵖ ⥤ B ⥤ B}
    (a : ∀ K : A, TA.obj K ⊣ HA.obj (op K))
    (b : ∀ K : B, TB.obj K ⊣ HB.obj (op K))
    (F : A ⥤ B) (μ : uncurry₀ TA ⋙ F ≅
      F.prod F ⋙ uncurry₀ TB) (K M : A) :
    (uncurry₀ TB).map (Prod.mkHom (𝟙 (F.obj K)) (homMap a b F μ K M)) ≫
        (b (F.obj K)).counit.app (F.obj M) =
      μ.inv.app (K, (HA.obj (op K)).obj M) ≫ F.map ((a K).counit.app M) := by
  dsimp only [homMap]
  simpa only [Functor.uncurry_obj_map, _root_.CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, Adjunction.homEquiv_counit, Functor.prod_obj,
    Functor.id_obj, Functor.uncurry_obj_obj] using
      ((b (F.obj K)).homEquiv _ _).symm_apply_apply
      (μ.inv.app (K, (HA.obj (op K)).obj M) ≫ F.map ((a K).counit.app M))

private theorem homMap_naturality
    {TA : A ⥤ A ⥤ A} {TB : B ⥤ B ⥤ B}
    {HA : Aᵒᵖ ⥤ A ⥤ A} {HB : Bᵒᵖ ⥤ B ⥤ B}
    (a : ∀ K : A, TA.obj K ⊣ HA.obj (op K))
    (b : ∀ K : B, TB.obj K ⊣ HB.obj (op K))
    (ha : ∀ (K K' M : A) (f : K' ⟶ K),
      (uncurry₀ TA).map (Prod.mkHom (𝟙 K') ((uncurry₀ HA).map (Prod.mkHom f.op (𝟙 M)))) ≫
          (a K').counit.app M = (uncurry₀ TA).map (Prod.mkHom f (𝟙 _)) ≫ (a K).counit.app M)
    (hb : ∀ (K K' M : B) (f : K' ⟶ K),
      (uncurry₀ TB).map (Prod.mkHom (𝟙 K') ((uncurry₀ HB).map (Prod.mkHom f.op (𝟙 M)))) ≫
          (b K').counit.app M = (uncurry₀ TB).map (Prod.mkHom f (𝟙 _)) ≫ (b K).counit.app M)
    (F : A ⥤ B) (μ : uncurry₀ TA ⋙ F ≅
      F.prod F ⋙ uncurry₀ TB)
    (K M K' M' : A) (f : K' ⟶ K) (g : M ⟶ M') :
    F.map ((uncurry₀ HA).map (Prod.mkHom f.op g)) ≫ homMap a b F μ K' M' =
      homMap a b F μ K M ≫ (uncurry₀ HB).map (Prod.mkHom (F.map f).op (F.map g)) := by
  apply ((b (F.obj K')).homEquiv _ (F.obj M')).symm.injective
  simp only [uncurry, tensor_right_comp, Category.assoc]
  rw [homMap_eval, evaluation_transport TB HB b hb]
  have hn := μ.inv.naturality (Prod.mkHom (𝟙 K') ((uncurry₀ HA).map (Prod.mkHom f.op g)))
  have hn' := μ.inv.naturality (Prod.mkHom f (𝟙 ((HA.obj (op K)).obj M)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn hn'
  simp only [F.map_id, Functor.uncurry_obj_obj] at hn hn'
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp,
    evaluation_transport TA HA a ha, F.map_comp, F.map_comp]
  have ht : (uncurry₀ TB).map (Prod.mkHom (𝟙 (F.obj K')) (homMap a b F μ K M)) ≫
      (uncurry₀ TB).map (Prod.mkHom (F.map f) (𝟙 _)) =
      (uncurry₀ TB).map (Prod.mkHom (F.map f) (𝟙 _)) ≫
        (uncurry₀ TB).map (Prod.mkHom (𝟙 (F.obj K)) (homMap a b F μ K M)) := by
    simp only [← (uncurry₀ TB).map_comp, prod_comp, Category.id_comp, Category.comp_id]
  rw [reassoc_of% ht, reassoc_of% homMap_eval a b F μ K M,
    ← reassoc_of% hn']

end StageHomProof

/-- The internal Hom map transposed from an invertible tensor comparison is natural
in both variables.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, Hom comparison
by transposition of the extended evaluation.
(blueprint: lem-sf-normalized-stage-hom-naturality).

Proof: apply the injective inverse tensor-Hom adjunction at the source of the
contravariant map. The transpose of each Hom comparison is its defining extended
evaluation. Evaluation is natural in its output and dinatural in its input by the
parametrized adjunction counit identity. The tensorator inverse is natural in both
arguments. Use those identities and bifunctoriality to identify the transposes,
then use adjunction injectivity. No tensor coherence, constructibility or geometric
assumptions enter this calculation. -/
theorem scalar_tensor_hom_comparison_naturality
    {A B : Type*} [Category A] [Category B]
    (TA : A ⥤ A ⥤ A) (HA : Aᵒᵖ ⥤ A ⥤ A)
    (TB : B ⥤ B ⥤ B) (HB : Bᵒᵖ ⥤ B ⥤ B)
    (a : ∀ K : A, TA.obj K ⊣ HA.obj (op K))
    (b : ∀ K : B, TB.obj K ⊣ HB.obj (op K))
    (ha : ∀ (K K' M : A) (f : K' ⟶ K),
      (Functor.uncurry.obj TA).map
          (Prod.mkHom (𝟙 K') ((Functor.uncurry.obj HA).map (Prod.mkHom f.op (𝟙 M)))) ≫
        (a K').counit.app M =
      (Functor.uncurry.obj TA).map (Prod.mkHom f (𝟙 _)) ≫ (a K).counit.app M)
    (hb : ∀ (K K' M : B) (f : K' ⟶ K),
      (Functor.uncurry.obj TB).map
          (Prod.mkHom (𝟙 K') ((Functor.uncurry.obj HB).map (Prod.mkHom f.op (𝟙 M)))) ≫
        (b K').counit.app M =
      (Functor.uncurry.obj TB).map (Prod.mkHom f (𝟙 _)) ≫ (b K).counit.app M)
    (F : A ⥤ B)
    (μ : Functor.uncurry.obj TA ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TB)
    (K M K' M' : A) (f : K' ⟶ K) (g : M ⟶ M') :
    let c := fun (U V : A) ↦ (b (F.obj U)).homEquiv _ _
      (μ.inv.app (U, (HA.obj (op U)).obj V) ≫ F.map ((a U).counit.app V))
    F.map ((Functor.uncurry.obj HA).map (Prod.mkHom f.op g)) ≫ c K' M' =
      c K M ≫ (Functor.uncurry.obj HB).map (Prod.mkHom (F.map f).op (F.map g)) := by
  exact StageHomProof.homMap_naturality a b ha hb F μ K M K' M' f g

end WeilConjectures.FiniteFreeCoefficients
