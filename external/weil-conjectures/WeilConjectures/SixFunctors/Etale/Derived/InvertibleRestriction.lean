/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-!
# Automorphisms of invertible complexes are determined along a closed subscheme

Let `i : Z ⟶ X` be a closed immersion such that every point of `X` lies in a preconnected set
meeting the range of `i`, and let `Λ` be a finite commutative ring. An endomorphism `γ` of an
invertible object `F` of `D(X_ét, Λ)` with `Li^* γ = 𝟙` is the identity. Tensoring with an
inverse of `F` turns `γ` into an endomorphism of the unit `Λ_X`, a morphism between finite
locally constant sheaves, and such morphisms are determined along `i`
(`AlgebraicGeometry.Etale.upperStar_map_injective_of_isPreconnected`).

## Main statements

- `AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_constantSheaf`: a constant sheaf with
  finitely generated value is finite locally constant.
- `AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_map_eq_of_isInvertible`: two
  isomorphisms out of an invertible complex agreeing after `Li^*` are equal.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalCategory

/-- Let `L : C ⥤ D` be a functor between monoidal categories with `L(K ⊗ M) ≅ L K ⊗ L M`
naturally, and detecting identities of the unit. An endomorphism `γ` of an invertible object `F`
with `L γ = 𝟙` is the identity: with `M` an inverse of `F`, `γ ▷ M` is conjugate to an
endomorphism of the unit mapped to `𝟙` by `L`, hence is `𝟙`, and `γ` is recovered from `γ ▷ M`
by tensoring with `F` on the right. -/
lemma eq_id_of_map_eq_id_of_tensorInverse {C D : Type*} [Category C] [MonoidalCategory C]
    [Category D] [MonoidalCategory D] (L : C ⥤ D)
    (τ : (Functor.postcompose₂.obj L).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj (curriedTensor D))
    (hunit : ∀ δ : 𝟙_ C ⟶ 𝟙_ C, L.map δ = 𝟙 _ → δ = 𝟙 _)
    {F M : C} (e₁ : F ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ F ≅ 𝟙_ C) (γ : F ⟶ F) (hγ : L.map γ = 𝟙 _) :
    γ = 𝟙 F := by
  have hL : L.map (γ ▷ M) = 𝟙 _ := by
    have h : L.map (γ ▷ M) ≫ ((τ.app F).app M).hom =
        ((τ.app F).app M).hom ≫ (L.map γ ▷ L.obj M) :=
      NatTrans.congr_app (τ.hom.naturality γ) M
    rw [hγ] at h
    exact (cancel_mono ((τ.app F).app M).hom).1 (by simpa using h)
  have hM : γ ▷ M = 𝟙 _ := by
    have h := hunit (e₁.inv ≫ γ ▷ M ≫ e₁.hom) (by
      rw [L.map_comp, L.map_comp, hL, Category.id_comp, ← L.map_comp, e₁.inv_hom_id, L.map_id])
    simpa using congrArg (fun f ↦ e₁.hom ≫ f ≫ e₁.inv) h
  have h₁ : γ ▷ (M ⊗ F) = 𝟙 _ := by
    have h := associator_naturality_left γ M F
    rw [hM] at h
    exact (cancel_epi (α_ F M F).hom).1 (by simpa using h.symm)
  have h₂ : γ ▷ 𝟙_ C = 𝟙 _ := by
    have h := whisker_exchange γ e₂.hom
    rw [h₁] at h
    exact (cancel_epi (F ◁ e₂.hom)).1 (by simpa using h)
  have h := rightUnitor_naturality γ
  rw [h₂] at h
  exact (cancel_epi (ρ_ F).hom).1 (by simpa using h.symm)

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- A constant sheaf of `Λ`-modules with finitely generated value is finite locally constant:
it is trivialised by the identity cover, and its stalks are its value. -/
instance isFiniteLocallyConstantSheaf_constantSheaf (N : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ N] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N).IsConstant
      X.smallEtaleTopology := Sheaf.isConstant_of_iso _ (Iso.refl _)
  have : IsLocallyConstantSheaf
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) :=
    ⟨⟨⟨Cover.mkOfCovers PUnit (fun _ ↦ X) (fun _ ↦ 𝟙 X) (fun x ↦ ⟨⟨⟩, x, rfl⟩)
      (fun _ ↦ inferInstance), fun _ ↦
      (isConstant_over_iff_upperStar _ _ _).2 (Sheaf.IsConstant.upperStar (X := X) _ _ _)⟩⟩⟩
  have : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) :=
    ⟨fun Ω _ _ s ↦ ((ModuleCat.isFinitelyGenerated_iff N).2 inferInstance).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso N).symm⟩
  exact {}
variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : ∀ x : X, ∃ S : Set X, _root_.IsPreconnected S ∧ x ∈ S ∧ (S ∩ Set.range i.base).Nonempty)

include hi in
/-- An endomorphism of the unit `Λ_X` of `D(X_ét, Λ)` which becomes the identity after `Li^*` is
the identity: it is a morphism of finite locally constant sheaves placed in degree zero. -/
lemma eq_id_of_leftDerivedUpperStar_map_eq_id
    (δ : 𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) ⟶ 𝟙_ _)
    (hδ : (L((i)^*[ModuleCat.{u + 1} Λ])).map δ = 𝟙 _) : δ = 𝟙 _ := by
  let A := ModuleCat.{u + 1} Λ
  let U := 𝟙_ (Sheaf X.smallEtaleTopology A)
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) U :=
    isFiniteLocallyConstantSheaf_constantSheaf (𝟙_ A)
  let u := singleFunctorObjUnitIso A X
  let S := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0
  obtain ⟨δ₀, hδ₀⟩ := S.map_surjective (u.hom ≫ δ ≫ u.inv)
  let c : S ⋙ L((i)^*[A]) ≅ (i)^*[A] ⋙ DerivedCategory.singleFunctor _ 0 :=
    Functor.isoWhiskerLeft S (leftDerivedUpperStarIsoMapDerivedCategory A i) ≪≫
      ((i)^*[A]).mapDerivedCategorySingleFunctor 0
  have h₁ : (L((i)^*[A])).map (S.map δ₀) = 𝟙 _ := by
    rw [hδ₀, Functor.map_comp, Functor.map_comp, hδ, Category.id_comp, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  have h₂ : (DerivedCategory.singleFunctor _ 0).map (((i)^*[A]).map δ₀) =
      (DerivedCategory.singleFunctor _ 0).map (((i)^*[A]).map (𝟙 U)) := by
    have := c.hom.naturality δ₀
    rw [Functor.comp_map, h₁] at this
    erw [Category.id_comp] at this
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, ← cancel_epi (c.hom.app U)]
    exact this.symm.trans (Category.comp_id _).symm
  have h₄ : δ₀ = 𝟙 U := upperStar_map_injective_of_isPreconnected i hi
    ((DerivedCategory.singleFunctor _ 0).map_injective h₂)
  rw [h₄, CategoryTheory.Functor.map_id] at hδ₀
  calc δ = u.inv ≫ (u.hom ≫ δ ≫ u.inv) ≫ u.hom := by simp
    _ = 𝟙 _ := by rw [← hδ₀, Category.id_comp, Iso.inv_hom_id]

include hi in
/-- An endomorphism `γ` of an invertible object `F` of `D(X_ét, Λ)` with `Li^* γ = 𝟙` is the
identity: with `M` an inverse of `F`, `γ ▷ M` is conjugate to an endomorphism of the unit which
becomes the identity after `Li^*`, by monoidality of `Li^*`, and `γ` is recovered from `γ ▷ M`
by tensoring with `F` (`CategoryTheory.MonoidalCategory.eq_id_of_map_eq_id_of_tensorInverse`).
-/
lemma eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible
    {F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hF : DerivedCategory.isInvertible Λ X F) (γ : F ⟶ F)
    (hγ : (L((i)^*[ModuleCat.{u + 1} Λ])).map γ = 𝟙 _) : γ = 𝟙 _ := by
  obtain ⟨M, ⟨e⟩, ⟨e'⟩⟩ := hF
  exact MonoidalCategory.eq_id_of_map_eq_id_of_tensorInverse L((i)^*[ModuleCat.{u + 1} Λ])
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} Λ) i)
    (eq_id_of_leftDerivedUpperStar_map_eq_id i hi) e e' γ hγ


section Surjective

variable {Z : Scheme.{u}} (π : Z ⟶ X) [Surjective π]

/-- An endomorphism of the unit `Λ_X` of `D(X_ét, Λ)` which becomes the identity after `Lπ^*`
for a surjective `π` is the identity: it is a morphism of sheaves placed in degree zero, and the
pullback of sheaves along `π` is faithful. -/
lemma eq_id_of_leftDerivedUpperStar_map_eq_id_of_surjective
    (δ : 𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) ⟶ 𝟙_ _)
    (hδ : (L((π)^*[ModuleCat.{u + 1} Λ])).map δ = 𝟙 _) : δ = 𝟙 _ := by
  let A := ModuleCat.{u + 1} Λ
  let U := 𝟙_ (Sheaf X.smallEtaleTopology A)
  let u := singleFunctorObjUnitIso A X
  let S := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0
  obtain ⟨δ₀, hδ₀⟩ := S.map_surjective (u.hom ≫ δ ≫ u.inv)
  let c : S ⋙ L((π)^*[A]) ≅ (π)^*[A] ⋙ DerivedCategory.singleFunctor _ 0 :=
    Functor.isoWhiskerLeft S (leftDerivedUpperStarIsoMapDerivedCategory A π) ≪≫
      ((π)^*[A]).mapDerivedCategorySingleFunctor 0
  have h₁ : (L((π)^*[A])).map (S.map δ₀) = 𝟙 _ := by
    rw [hδ₀, Functor.map_comp, Functor.map_comp, hδ, Category.id_comp, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  have h₂ : (DerivedCategory.singleFunctor _ 0).map (((π)^*[A]).map δ₀) =
      (DerivedCategory.singleFunctor _ 0).map (((π)^*[A]).map (𝟙 U)) := by
    have := c.hom.naturality δ₀
    rw [Functor.comp_map, h₁] at this
    erw [Category.id_comp] at this
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, ← cancel_epi (c.hom.app U)]
    exact this.symm.trans (Category.comp_id _).symm
  have := Etale.faithful_upperStar_of_surjective Λ π π.surjective
  have h₄ : δ₀ = 𝟙 U := ((π)^*[A]).map_injective
    ((DerivedCategory.singleFunctor _ 0).map_injective h₂)
  rw [h₄, CategoryTheory.Functor.map_id] at hδ₀
  calc δ = u.inv ≫ (u.hom ≫ δ ≫ u.inv) ≫ u.hom := by simp
    _ = 𝟙 _ := by rw [← hδ₀, Category.id_comp, Iso.inv_hom_id]

/-- An endomorphism `γ` of an invertible object `F` of `D(X_ét, Λ)` with `Lπ^* γ = 𝟙` for a
surjective `π` is the identity, as in
`AlgebraicGeometry.Etale.eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible`. -/
lemma eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible_of_surjective
    {F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hF : DerivedCategory.isInvertible Λ X F) (γ : F ⟶ F)
    (hγ : (L((π)^*[ModuleCat.{u + 1} Λ])).map γ = 𝟙 _) : γ = 𝟙 _ := by
  obtain ⟨M, ⟨e⟩, ⟨e'⟩⟩ := hF
  exact MonoidalCategory.eq_id_of_map_eq_id_of_tensorInverse L((π)^*[ModuleCat.{u + 1} Λ])
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} Λ) π)
    (eq_id_of_leftDerivedUpperStar_map_eq_id_of_surjective π) e e' γ hγ

end Surjective
end Etale

end AlgebraicGeometry
