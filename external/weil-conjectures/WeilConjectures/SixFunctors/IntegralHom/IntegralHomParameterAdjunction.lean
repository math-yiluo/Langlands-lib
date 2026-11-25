/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Parameter coherence for tensor-Hom adjunctions

Source: Stacks Project, Tag 08J9, naturality of tensor-Hom currying.
(blueprint: lem-sf-integral-hom-parameter-adjunction).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory Opposite CategoryTheory.MonoidalCategory
namespace WeilConjectures.IntegralHom

/-- Build a parameter adjunction from the counit compatibility equation.
Source: the tensor-Hom adjunction and its first-variable naturality (Stacks 08J9).
(blueprint: lem-sf-integral-hom-parameter-adjunction). -/
def parameterAdjunctionOfCounit {D : Type*} [Category D]
    {F : D ⥤ D ⥤ D} {G : Dᵒᵖ ⥤ D ⥤ D}
    (a : ∀ K, F.obj K ⊣ G.obj (op K))
    (h : ∀ (K K' W : D) (f : K ⟶ K'),
      (F.obj K).map ((G.map f.op).app W) ≫ (a K).counit.app W =
        (F.map f).app ((G.obj (op K')).obj W) ≫ (a K').counit.app W) : F ⊣₂ G :=
  ParametrizedAdjunction.mk' a (by
    intro K K' f L W g
    apply ((a K).homEquiv L W).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    rw [Functor.map_comp, Category.assoc, h K K' W f]
    rw [← Category.assoc, (F.map f).naturality, Category.assoc]
    rw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply])

/-- The left-tensor adjunction, transported through the given braiding, with its
parameter coherence retained. Source: Stacks 08J9, natural tensor-Hom currying.
(blueprint: lem-sf-integral-hom-parameter-adjunction). -/
noncomputable def leftTensorParameterAdjunction {D : Type*} [Category D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    (β : @SymmetricCategory D _ S.monoidal) :
    Functor.curry.obj S.tensor ⊣₂ Functor.curry.obj H := by
  let := S.monoidal
  let := β
  let e (K : D) : MonoidalCategory.tensorRight K ≅
      (Functor.curry.obj S.tensor).obj K :=
    NatIso.ofComponents (fun L ↦ (β_ K L).symm) (by
      intro L L' f
      simp [CoefficientClosedStructure.tensor])
  let a : ∀ K : D, (Functor.curry.obj S.tensor).obj K ⊣
      (Functor.curry.obj H).obj (op K) := fun K ↦
    (S.adjunction K).ofNatIsoLeft (e K)
  have he (K W : D) : (a K).counit.app W =
      (β_ K (H.obj (op K, W))).hom ≫ (S.adjunction K).counit.app W := by
    rfl
  refine parameterAdjunctionOfCounit a ?_
  intro K K' W f
  change S.tensor.map (Prod.mkHom (𝟙 K) (H.map (Prod.mkHom f.op (𝟙 W)))) ≫
      (a K).counit.app W =
    S.tensor.map (Prod.mkHom f (𝟙 (H.obj (op K', W)))) ≫ (a K').counit.app W
  rw [he, he]
  change ((𝟙 K) ⊗ₘ H.map (Prod.mkHom f.op (𝟙 W))) ≫ _ ≫ _ =
    (f ⊗ₘ 𝟙 _) ≫ _ ≫ _
  rw [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id,
    BraidedCategory.braiding_naturality_right_assoc]
  have hn := S.evaluation_naturality K' K W f
  change (H.map (Prod.mkHom f.op (𝟙 W)) ▷ K) ≫ _ =
    (_ ◁ f) ≫ _ at hn
  rw [hn, BraidedCategory.braiding_naturality_left_assoc]

end WeilConjectures.IntegralHom
