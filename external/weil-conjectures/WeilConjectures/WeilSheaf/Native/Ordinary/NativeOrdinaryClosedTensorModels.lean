/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryCanonicalTensorRepresentatives
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRepresentativeCurrying

/-! # Ordinary tensor on prescribed product-Hom representatives

Source: Stacks 06YS, 08J9 and 0A97; native tensor transport, ordinary part of step 1
(blueprint: lem-sf-native-ordinary-closed-tensor-models).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem closed_of_natural_currying
    {D : Type*} [Category D] [MonoidalCategory D]
    (H : Dᵒᵖ × D ⥤ D)
    (e : ∀ T P I : D, (T ⊗ P ⟶ I) ≃ (T ⟶ H.obj (op P, I)))
    (hn : ∀ (T T' P P' I I' : D)
      (f : T' ⟶ T) (g : P' ⟶ P) (h : I ⟶ I') (φ : T ⟶ H.obj (op P, I)),
      (e T' P' I').symm (f ≫ φ ≫ H.map (Prod.mkHom g.op h)) =
        (f ⊗ₘ g) ≫ (e T P I).symm φ ≫ h) :
    ∃ S : CoefficientClosedStructure H,
      S.monoidal = (inferInstance : MonoidalCategory D) ∧
        ∀ T P I, HEq (S.transpose T P I) (e T P I) := by
  have hId (P I : D) : H.map (Prod.mkHom (𝟙 P).op (𝟙 I)) = 𝟙 _ := by
    change H.map (𝟙 _) = 𝟙 _
    exact H.map_id _
  let adj : ∀ P : D, tensorRight P ⊣ Prod.sectR (op P) D ⋙ H := fun P ↦
    Adjunction.mkOfHomEquiv
      { homEquiv := fun T I ↦ e T P I
        homEquiv_naturality_left_symm := fun {T' T I} f φ ↦ by
          change (e T' P I).symm (f ≫ φ) = (f ▷ P) ≫ (e T P I).symm φ
          simpa only [hId, Category.comp_id, tensorHom_id] using
              hn T T' P P I I f (𝟙 P) (𝟙 I) φ
        homEquiv_naturality_right := fun {T} {I I'} ψ h ↦ by
          apply (e T P I').symm.injective
          have he := hn T T P P I I' (𝟙 T) (𝟙 P) h (e T P I ψ)
          change (e T P I').symm (e T P I' (ψ ≫ h)) =
            (e T P I').symm (e T P I ψ ≫ H.map (𝟙 (op P), h))
          rw [Equiv.symm_apply_apply]
          simpa only [op_id, id_tensorHom_id, Category.id_comp,
            Equiv.symm_apply_apply] using he.symm }
  let S : CoefficientClosedStructure H :=
    { monoidal := inferInstance
      adjunction := adj
      evaluation_naturality := by
        intro P P' I g
        have h₁ := hn (H.obj (op P', I)) (H.obj (op P, I)) P' P' I I
          (H.map (Prod.mkHom g.op (𝟙 I))) (𝟙 P') (𝟙 I) (𝟙 _)
        have h₂ := hn (H.obj (op P, I)) (H.obj (op P, I)) P P' I I
          (𝟙 _) g (𝟙 I) (𝟙 _)
        change (H.map (Prod.mkHom g.op (𝟙 I)) ▷ P') ≫
            (e (H.obj (op P', I)) P' I).symm (𝟙 _) =
          (H.obj (op P, I) ◁ g) ≫ (e (H.obj (op P, I)) P I).symm (𝟙 _)
        simp only [hId, Category.id_comp, Category.comp_id, tensorHom_id, id_tensorHom]
          at h₁ h₂
        exact h₁.symm.trans h₂ }
  refine ⟨S, rfl, ?_⟩
  intro T P I
  apply heq_of_eq
  change (adj P).homEquiv T I = e T P I
  dsimp only [adj]
  rw [Adjunction.mkOfHomEquiv_homEquiv]

/-- The ordinary closed tensor can be normalized against any specified natural
product-total Hom representatives. This construction involves no Weil structure
or forgetful comparison.

Source: Stacks 06YS, 08J9 and 0A97; ordinary part of step 1 of
lem-sf-weil-native-tensor-transport
(blueprint: lem-sf-native-ordinary-closed-tensor-models).

Proof: construct the one-K-flat models and signed symmetry directly from the
balanced native tensor comparison and the canonical localization tensorator.
For the Hom part, transport the normalized ringed tensor-Hom calculation to the
specified product-total representatives R. The row-sign change (-1)^(np) and
the reversed tensor order give unsigned degree-zero uncurrying.
The tensor part is isolated as native_ordinary_tensor_representatives and the
Hom-set calculation as native_ordinary_representative_currying. From its natural
bijections, Adjunction.mkOfHomEquiv constructs the adjunctions. Applying inverse
currying naturality twice to identity maps proves evaluation_naturality in the
Hom source. Its transpose is the supplied bijection, so the representative
uncurrying equation and the tensor braiding square give NativeOrdinaryTensorModels.
These constructions apply also to zero complexes and to the empty scheme;
no boundedness, constructibility or finite-type assumption is used. -/
theorem native_ordinary_closed_tensor_models
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
        DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H) :
    ∃ S : CoefficientClosedStructure H,
    ∃ β : @SymmetricCategory _ _ S.monoidal,
      S.monoidal =
        (inferInstance : MonoidalCategory (DerivedCategory (ProEtale.AdicSheaf l Y))) ∧
      NativeOrdinaryTensorModels l Y H R S β := by
  obtain ⟨β, model, swap, hn, hswap, hβ, hcanonical⟩ :=
    native_ordinary_canonical_tensor_representatives l Y
  obtain ⟨e, he, hmodel⟩ := native_ordinary_representative_currying l Y H R model hn
  obtain ⟨⟨m, adj, ev⟩, hm, ht⟩ := closed_of_natural_currying H e he
  dsimp only [CoefficientClosedStructure.monoidal] at hm
  subst m
  let S : CoefficientClosedStructure H := ⟨inferInstance, adj, ev⟩
  refine ⟨S, β, rfl, model, swap, ?_, hswap, hβ, hcanonical⟩
  intro P Q I hP hQ hI φ
  obtain ⟨ψ, hψ, hloc⟩ := hmodel P Q I hP hQ hI φ
  refine ⟨ψ, hψ, ?_⟩
  rw [eq_of_heq (ht (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj I))]
  exact hloc

end AlgebraicGeometry.ProEtaleWeilSheaf
