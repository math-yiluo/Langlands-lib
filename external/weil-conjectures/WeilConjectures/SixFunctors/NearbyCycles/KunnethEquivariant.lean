/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutAction
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeId
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived

/-!

# Equivariance of the Künneth map of nearby cycles

Let `φ₁ : P ⟶ M` and `φ₂ : P ⟶ N` be morphisms of models, and let `σ_M`, `σ_N`, `σ_P` be
morphisms of models over the identities (for instance automorphisms of the geometric generic
fibres over the generic point of the trait) compatible with `φ₁` and `φ₂`. Then the Künneth map
`Π_{A,B} : Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B ⟶ Ψ_P (Lf₁^* A ⊗ Lf₂^* B)` is equivariant for the actions
`NearbyCyclesModel.Hom.autAction` of `σ_M`, `σ_N` on the source and of `σ_P` on the target
(`NearbyCyclesModel.kunnethMap_autAction`).

This is the compatibility of the Künneth map with pullbacks
(`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`) for the identities, transported along
the identity isomorphisms `L(𝟙)^* ≅ 𝟭`, which are monoidal
(`ProEtale.CondensedRing.leftDerivedUpperStarTensor_id`) and compatible with the pullback
comparisons of the squares with identity sides
(`ProEtale.CondensedRing.pullbackSquareComparison_hom_app_id_right`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The comultiplication of `L(𝟙 W)^*` is compatible with the identity isomorphism
`L(𝟙 W)^* ≅ 𝟭`. -/
lemma δ_leftDerivedUpperStarId (W : Scheme.{u})
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))) :
    Functor.OplaxMonoidal.δ L((𝟙 W)^*⟦Λ⟧) K M ≫
        ((leftDerivedUpperStarId Λ W).hom.app K ⊗ₘ (leftDerivedUpperStarId Λ W).hom.app M) =
      (leftDerivedUpperStarId Λ W).hom.app (K ⊗ M) :=
  leftDerivedUpperStarTensor_id Λ W K M

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- `ProEtale.CondensedRing.pullbackSquareComparison_hom_app_id_right`, in the form used below. -/
private lemma pullbackSquareComparison_id_hom_app_comp_map {Z X : Scheme.{u}} (f : Z ⟶ X)
    (h : f ≫ 𝟙 X = 𝟙 Z ≫ f)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (pullbackSquareComparison Λ (⟨h⟩ : CommSq f (𝟙 Z) (𝟙 X) f)).hom.app K ≫
        L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ X).hom.app K) =
      (leftDerivedUpperStarId Λ Z).hom.app (L((f)^*⟦Λ⟧).obj K) := by
  rw [pullbackSquareComparison_hom_app_id_right, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  simp

/-- `Lf^*` of the identity isomorphism `L(𝟙)^* ≅ 𝟭` followed by `Lf^*` of its inverse. -/
lemma map_leftDerivedUpperStarId_hom_comp_map_inv {Z X : Scheme.{u}} (f : Z ⟶ X)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ X).hom.app K) ≫
        L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ X).inv.app K) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]

namespace NearbyCyclesModel

/-! ### Abstract computation -/

section Abstract

variable {S D : Type*} [Category S] [MonoidalCategory S] [Category D]

-- Perform the tensor-composition calculation before specializing to derived categories.
private lemma δ_comp_tensorHom_of_comp {T U₁ U₂ V₁ V₂ W₁ W₂ : S}
    (δ : T ⟶ U₁ ⊗ U₂) (p₁ : U₁ ⟶ V₁) (p₂ : U₂ ⟶ V₂)
    (q₁ : V₁ ⟶ W₁) (q₂ : V₂ ⟶ W₂) (r₁ : U₁ ⟶ W₁) (r₂ : U₂ ⟶ W₂)
    (t : T ⟶ W₁ ⊗ W₂) (h₁ : p₁ ≫ q₁ = r₁) (h₂ : p₂ ≫ q₂ = r₂)
    (hδ : δ ≫ (r₁ ⊗ₘ r₂) = t) :
    (δ ≫ (p₁ ⊗ₘ p₂)) ≫ (q₁ ⊗ₘ q₂) = t := by
  rw [Category.assoc, tensorHom_comp_tensorHom, h₁, h₂, hδ]

/-- The equivariance of the Künneth maps, in an abstract monoidal category: the transport of the
compatibility of the Künneth maps with pullbacks along an isomorphism `I ≅ 𝟭`. -/
private lemma kunnethMap_autAction_aux {I : S ⥤ S} (ι : I ≅ 𝟭 S) (Ψ : D ⥤ S)
    {U₁ U₂ U₁' U₂' V₁ V₂ : S} {C₀ C' C : D} (K : U₁ ⊗ U₂ ⟶ Ψ.obj C)
    (K' : U₁' ⊗ U₂' ⟶ Ψ.obj C') (n : C' ⟶ C)
    (v₁ : U₁' ⟶ U₁) (v₂ : U₂' ⟶ U₂) (hnat : K' ≫ Ψ.map n = (v₁ ⊗ₘ v₂) ≫ K)
    (αP : I.obj (Ψ.obj C) ⟶ Ψ.obj C₀) (s : C₀ ⟶ C') (t : C₀ ⟶ C) (hs : s ≫ n = t)
    (δ : I.obj (U₁ ⊗ U₂) ⟶ I.obj U₁ ⊗ I.obj U₂)
    (hδ : δ ≫ (ι.hom.app U₁ ⊗ₘ ι.hom.app U₂) = ι.hom.app (U₁ ⊗ U₂))
    (p₁ : I.obj U₁ ⟶ V₁) (q₁ : V₁ ⟶ U₁) (q₁' : U₁ ⟶ V₁) (hp₁ : p₁ ≫ q₁ = ι.hom.app U₁)
    (hq₁ : q₁ ≫ q₁' = 𝟙 _) (m₁ : V₁ ⟶ U₁')
    (p₂ : I.obj U₂ ⟶ V₂) (q₂ : V₂ ⟶ U₂) (q₂' : U₂ ⟶ V₂) (hp₂ : p₂ ≫ q₂ = ι.hom.app U₂)
    (hq₂ : q₂ ≫ q₂' = 𝟙 _) (m₂ : V₂ ⟶ U₂')
    (h : I.map K ≫ αP ≫ Ψ.map s = δ ≫ ((p₁ ≫ m₁) ⊗ₘ (p₂ ≫ m₂)) ≫ K') :
    ((q₁' ≫ m₁ ≫ v₁) ⊗ₘ (q₂' ≫ m₂ ≫ v₂)) ≫ K = K ≫ ι.inv.app _ ≫ αP ≫ Ψ.map t := by
  have hK := ι.hom.naturality K
  simp only [Functor.id_map] at hK
  rw [← cancel_epi (ι.hom.app (U₁ ⊗ U₂)), ← reassoc_of% hK, Iso.hom_inv_id_app_assoc, ← hs,
    Ψ.map_comp, reassoc_of% h, hnat, ← hδ, ← hp₁, ← hp₂]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, reassoc_of% hq₁,
    reassoc_of% hq₂]

variable {CM CN CP SM SN SP : Type*} [Category CM] [Category CN] [Category CP] [Category SM]
  [Category SN] [Category SP] [MonoidalCategory CP] [MonoidalCategory SP]
  {ΨM : CM ⥤ SM} {ΨN : CN ⥤ SN} {ΨP : CP ⥤ SP} {g₁ : CM ⥤ CP} {g₂ : CN ⥤ CP}
  {s₁ : SM ⥤ SP} {s₂ : SN ⥤ SP}

/-- The naturality of the Künneth maps, in abstract categories. -/
private lemma kunnethMap_comp_map_tensorHom_aux (α₁ : ΨM ⋙ s₁ ⟶ g₁ ⋙ ΨP) (α₂ : ΨN ⋙ s₂ ⟶ g₂ ⋙ ΨP)
    (μ : ∀ U V, ΨP.obj U ⊗ ΨP.obj V ⟶ ΨP.obj (U ⊗ V))
    (hμ : ∀ {U U' V V' : CP} (x : U ⟶ U') (y : V ⟶ V'),
      (ΨP.map x ⊗ₘ ΨP.map y) ≫ μ U' V' = μ U V ≫ ΨP.map (x ⊗ₘ y))
    {A A' : CM} {B B' : CN} (a : A ⟶ A') (b : B ⟶ B') :
    ((α₁.app A ⊗ₘ α₂.app B) ≫ μ _ _) ≫ ΨP.map (g₁.map a ⊗ₘ g₂.map b) =
      (s₁.map (ΨM.map a) ⊗ₘ s₂.map (ΨN.map b)) ≫ (α₁.app A' ⊗ₘ α₂.app B') ≫ μ _ _ := by
  have h₁ := α₁.naturality a
  have h₂ := α₂.naturality b
  simp only [Functor.comp_map] at h₁ h₂
  rw [Category.assoc, ← hμ, tensorHom_comp_tensorHom_assoc, ← h₁, ← h₂,
    tensorHom_comp_tensorHom_assoc]

end Abstract

variable {X X' Y Y' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

/-- The Künneth map `Π_{A,B}` is natural in `A` and `B`. -/
lemma kunnethMap_comp_map_tensorHom (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (a : A ⟶ A') (b : B ⟶ B') :
    kunnethMap Λ φ₁ φ₂ A B ≫
        (P.nearbyCycles Λ).map (L((f₁)^*⟦Λ⟧).map a ⊗ₘ L((f₂)^*⟦Λ⟧).map b) =
      (L((f₁')^*⟦Λ⟧).map ((M.nearbyCycles Λ).map a) ⊗ₘ
          L((f₂')^*⟦Λ⟧).map ((N.nearbyCycles Λ).map b)) ≫ kunnethMap Λ φ₁ φ₂ A' B' := by
  exact kunnethMap_comp_map_tensorHom_aux (φ₁.pullbackExchange Λ) (φ₂.pullbackExchange Λ)
    (P.tensorMap Λ) (fun x y ↦ P.tensorMap_natural Λ x y) a b

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- The comultiplication of `L(𝟙)^*` followed by the pullback comparisons of the squares with
identity sides and the identity isomorphisms `L(𝟙)^* ≅ 𝟭` is the identity isomorphism. -/
lemma δ_comp_pullbackSquareComparison_id (h₁ : f₁ ≫ 𝟙 X = 𝟙 Z ≫ f₁)
    (h₂ : f₂ ≫ 𝟙 Y = 𝟙 Z ≫ f₂)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (Functor.OplaxMonoidal.δ L((𝟙 Z)^*⟦Λ⟧) (L((f₁)^*⟦Λ⟧).obj A) (L((f₂)^*⟦Λ⟧).obj B) ≫
        ((pullbackSquareComparison Λ (⟨h₁⟩ : CommSq f₁ (𝟙 Z) (𝟙 X) f₁)).hom.app A ⊗ₘ
          (pullbackSquareComparison Λ (⟨h₂⟩ : CommSq f₂ (𝟙 Z) (𝟙 Y) f₂)).hom.app B)) ≫
        (L((f₁)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ X).hom.app A) ⊗ₘ
          L((f₂)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app B)) =
      (leftDerivedUpperStarId Λ Z).hom.app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) := by
  exact δ_comp_tensorHom_of_comp _ _ _ _ _ _ _ _
    (pullbackSquareComparison_id_hom_app_comp_map Λ f₁ h₁ A)
    (pullbackSquareComparison_id_hom_app_comp_map Λ f₂ h₂ B)
    (δ_leftDerivedUpperStarId Λ Z _ _)

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- **Equivariance of the Künneth map of nearby cycles**: for morphisms of models `σ_M`, `σ_N`,
`σ_P` over the identities compatible with `φ₁ : P ⟶ M` and `φ₂ : P ⟶ N`, the Künneth map
`Π_{A,B}` intertwines `Lf₁'^* σ_M ⊗ Lf₂'^* σ_N` with `σ_P` acting on `Ψ_P (Lf₁^* A ⊗ Lf₂^* B)`. -/
lemma kunnethMap_autAction (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (σM : M.Hom M (𝟙 X) (𝟙 X')) (σN : N.Hom N (𝟙 Y) (𝟙 Y')) (σP : P.Hom P (𝟙 Z) (𝟙 Z'))
    (htot₁ : σP.total ≫ φ₁.total = φ₁.total ≫ σM.total)
    (hgen₁ : σP.generic ≫ φ₁.generic = φ₁.generic ≫ σM.generic)
    (htot₂ : σP.total ≫ φ₂.total = φ₂.total ≫ σN.total)
    (hgen₂ : σP.generic ≫ φ₂.generic = φ₂.generic ≫ σN.generic)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (L((f₁')^*⟦Λ⟧).map (σM.autAction Λ A) ⊗ₘ L((f₂')^*⟦Λ⟧).map (σN.autAction Λ B)) ≫
        kunnethMap Λ φ₁ φ₂ A B =
      kunnethMap Λ φ₁ φ₂ A B ≫
        σP.autAction Λ (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) := by
  have hb₁ : f₁ ≫ 𝟙 X = 𝟙 Z ≫ f₁ := by simp
  have hb₂ : f₂ ≫ 𝟙 Y = 𝟙 Z ≫ f₂ := by simp
  have hs₁ : f₁' ≫ 𝟙 X' = 𝟙 Z' ≫ f₁' := by simp
  have hs₂ : f₂' ≫ 𝟙 Y' = 𝟙 Z' ≫ f₂' := by simp
  have h := map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁ φ₂ σM σN σP htot₁.symm hgen₁.symm
    htot₂.symm hgen₂.symm hb₁ hs₁ hb₂ hs₂ A B
  -- Infer the intermediate morphisms from the compatibilities below, reusing their derived
  -- pullbacks instead of synthesizing the graded tensor instances for each occurrence.
  have key := kunnethMap_autAction_aux (leftDerivedUpperStarId Λ Z') (P.nearbyCycles Λ)
    _ _ _ _ _
    (kunnethMap_comp_map_tensorHom Λ φ₁ φ₂
      ((leftDerivedUpperStarId Λ X).hom.app A) ((leftDerivedUpperStarId Λ Y).hom.app B))
    _ _ _ (δ_comp_pullbackSquareComparison_id Λ hb₁ hb₂ A B)
    _ (δ_leftDerivedUpperStarId Λ Z' _ _)
    _ _ _ (pullbackSquareComparison_id_hom_app_comp_map Λ f₁' hs₁ _)
    (map_leftDerivedUpperStarId_hom_comp_map_inv Λ f₁' _) _
    _ _ _ (pullbackSquareComparison_id_hom_app_comp_map Λ f₂' hs₂ _)
    (map_leftDerivedUpperStarId_hom_comp_map_inv Λ f₂' _) _ h
  simp only [Hom.autAction, CategoryTheory.Functor.map_comp]
  exact key

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
