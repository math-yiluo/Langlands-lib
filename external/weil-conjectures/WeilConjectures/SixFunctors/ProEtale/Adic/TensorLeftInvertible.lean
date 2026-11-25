/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.WeilSheaf.CurryIsoCriterion

/-!
# Tensoring with a locally trivial sheaf of rank one is invertible

Let `π : W ⟶ Y` be a quasi-compact surjective weakly étale morphism and let `M` be a sheaf of
`ℚ̄_ℓ,Y`-modules with `π^* M ≅ ℚ̄_ℓ,W`. Then for every `N` the counit
`𝓗om(M, N) ⊗_{ℚ̄_ℓ} M ⟶ N` of the adjunction `- ⊗ M ⊣ 𝓗om(M, -)`
(`CategoryTheory.Mod.ihomAdjunction`)
is an isomorphism (`AlgebraicGeometry.ProEtale.AdicSheaf.isIso_ihomAdjunction_counit_app`), and so
is the unit `N ⟶ 𝓗om(M, N ⊗ M)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.isIso_ihomAdjunction_unit_app`).

Pullback along `π` reflects isomorphisms
(`AlgebraicGeometry.ProEtale.AdicSheaf.reflectsIsomorphisms_upperStar`) and is compatible with the
tensor product and the internal hom, hence with the counit
(`AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso_inv_app_comp_map_counit_app`); after
pullback, `M` becomes `ℚ̄_ℓ,W`, for which `- ⊗ ℚ̄_ℓ,W ≅ 𝟭`
(`CategoryTheory.Mod.tensorLeftRegularIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace CategoryTheory

/-- The counit of an adjunction whose left adjoint is isomorphic to the identity is an
isomorphism. -/
lemma Adjunction.isIso_counit_app_of_iso_id {C : Type*} [Category C] {L R : C ⥤ C} (adj : L ⊣ R)
    (e : L ≅ 𝟭 C) (X : C) : IsIso (adj.counit.app X) :=
  have : L.Full := Functor.Full.of_iso e.symm
  have : L.Faithful := Functor.Faithful.of_iso e.symm
  adj.isIso_counit_app_of_iso (e.app X).symm

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Sheaf.symmetricCategory

section Counit

variable {V X : Scheme.{u}} (g : V ⟶ X) [WeaklyEtale g]

/-- The identification `g^*(P ⊗_A M) ≅ g^* P ⊗_A g^* M` is compatible with the quotient maps
`P ⊗ M ⟶ P ⊗_A M`. -/
lemma tensorπ_adicUpperStarTensorLeftIso_inv_app (P M : AdicSheaf l X) :
    Mod.tensorπ ((g)^*ᵃ[l].obj P) ((g)^*ᵃ[l].obj M) ≫
        ((adicUpperStarTensorLeftIso l g M).inv.app P).hom =
      μ (g)^*[WeilCoefficients.{u} l] P.X M.X ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.tensorπ P M) := by
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (g)^*ᵃ[l])
  have h := Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicUpperStarRingHom l g)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _) P M
  have h₃ : Mod.tensorπ ((g)^*ᵃ[l].obj P) ((g)^*ᵃ[l].obj M) =
      μ (g)^*[WeilCoefficients.{u} l] P.X M.X ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.tensorπ P M) ≫
          ((adicUpperStarTensorLeftIso l g M).hom.app P).hom := by
    erw [h, IsIso.hom_inv_id_assoc]
    rfl
  erw [h₃, Category.assoc, Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id_app]
  rw [Mod.id_hom']
  erw [Category.comp_id]

/-- **Pullback along a weakly étale morphism is compatible with the counit of
`- ⊗ M ⊣ 𝓗om(M, -)`**: through `g^*(𝓗om(M, N) ⊗_A M) ≅ g^* 𝓗om(M, N) ⊗_A g^* M` and
`g^* 𝓗om(M, N) ≅ 𝓗om(g^* M, g^* N)`, the pullback of the counit is the counit for `g^* M`. -/
lemma adicUpperStarTensorLeftIso_inv_app_comp_map_counit_app (M N : AdicSheaf l X) :
    (adicUpperStarTensorLeftIso l g M).inv.app ((AdicSheaf.ihom M).obj N) ≫
        (g)^*ᵃ[l].map ((Mod.ihomAdjunction M).counit.app N) =
      (Mod.tensorLeft ((g)^*ᵃ[l].obj M)).map ((adicUpperStarIhomIso l g M).hom.app N) ≫
        (Mod.ihomAdjunction ((g)^*ᵃ[l].obj M)).counit.app ((g)^*ᵃ[l].obj N) := by
  refine Mod.tensorLeft_obj_hom_ext ?_
  rw [Mod.comp_hom', ← Category.assoc, tensorπ_adicUpperStarTensorLeftIso_inv_app,
    Mod.comp_hom', Mod.tensorπ_map_assoc, adicUpperStar_map_hom, Category.assoc,
    ← Functor.map_comp]
  have h₁ := adicUpperStarIhomIso_evaluation g M N
  rw [Mod.evaluation, Mod.evaluation] at h₁
  exact h₁.symm

end Counit

namespace AdicSheaf

variable {W Y : Scheme.{u}} (π : W ⟶ Y) [WeaklyEtale π] [QuasiCompact π] [Surjective π]
  {M : AdicSheaf l Y} (e : (π)^*ᵃ[l].obj M ≅ AdicSheaf.unit l W)

include e

/-- **Tensoring with a sheaf of rank one which is trivial locally for the weakly étale topology
is invertible**: if `π^* M ≅ ℚ̄_ℓ` for a quasi-compact surjective weakly étale `π`, the counit
`𝓗om(M, N) ⊗_{ℚ̄_ℓ} M ⟶ N` is an isomorphism. -/
theorem isIso_ihomAdjunction_counit_app (N : AdicSheaf l Y) :
    IsIso ((Mod.ihomAdjunction M).counit.app N) := by
  have := AdicSheaf.reflectsIsomorphisms_upperStar (l := l) π
  have : IsIso ((Mod.ihomAdjunction ((π)^*ᵃ[l].obj M)).counit.app ((π)^*ᵃ[l].obj N)) :=
    (Mod.ihomAdjunction _).isIso_counit_app_of_iso_id
      (Mod.tensorLeftMapIso e ≪≫ Mod.tensorLeftRegularIso) _
  have h := adicUpperStarTensorLeftIso_inv_app_comp_map_counit_app π M N
  have : IsIso ((adicUpperStarTensorLeftIso l π M).inv.app ((AdicSheaf.ihom M).obj N) ≫
      (π)^*ᵃ[l].map ((Mod.ihomAdjunction M).counit.app N)) := by
    rw [h]
    infer_instance
  have : IsIso ((π)^*ᵃ[l].map ((Mod.ihomAdjunction M).counit.app N)) :=
    IsIso.of_isIso_comp_left ((adicUpperStarTensorLeftIso l π M).inv.app _) _
  exact isIso_of_reflects_iso _ (π)^*ᵃ[l]

/-- If `π^* M ≅ ℚ̄_ℓ` for a quasi-compact surjective weakly étale `π`, then
`𝓗om(M, N) ⊗_{ℚ̄_ℓ} M ≅ N` through the counit. -/
noncomputable def tensorLeftIhomIso (N : AdicSheaf l Y) :
    (Mod.tensorLeft M).obj ((AdicSheaf.ihom M).obj N) ≅ N :=
  have := isIso_ihomAdjunction_counit_app π e N
  asIso ((Mod.ihomAdjunction M).counit.app N)

@[simp]
lemma tensorLeftIhomIso_hom (N : AdicSheaf l Y) :
    (tensorLeftIhomIso π e N).hom = (Mod.ihomAdjunction M).counit.app N :=
  rfl

/-- If `π^* M ≅ ℚ̄_ℓ` for a quasi-compact surjective weakly étale `π`, then `- ⊗_{ℚ̄_ℓ} M`
reflects isomorphisms: after pullback along `π` it becomes `- ⊗_{ℚ̄_ℓ} ℚ̄_ℓ ≅ 𝟭`. -/
lemma reflectsIsomorphisms_tensorLeft : (Mod.tensorLeft M).ReflectsIsomorphisms := by
  have := AdicSheaf.reflectsIsomorphisms_upperStar (l := l) π
  have : (Mod.tensorLeft ((π)^*ᵃ[l].obj M)).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso (Mod.tensorLeftMapIso e ≪≫ Mod.tensorLeftRegularIso).symm
  have : (Mod.tensorLeft M ⋙ (π)^*ᵃ[l]).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso (adicUpperStarTensorLeftIso l π M).symm
  exact reflectsIsomorphisms_of_comp _ (π)^*ᵃ[l]

/-- If `π^* M ≅ ℚ̄_ℓ` for a quasi-compact surjective weakly étale `π`, the unit
`N ⟶ 𝓗om(M, N ⊗_{ℚ̄_ℓ} M)` is an isomorphism: by the triangle identity its image under
`- ⊗ M` is inverse to a counit, and `- ⊗ M` reflects isomorphisms. -/
theorem isIso_ihomAdjunction_unit_app (N : AdicSheaf l Y) :
    IsIso ((Mod.ihomAdjunction M).unit.app N) := by
  have := reflectsIsomorphisms_tensorLeft π e
  have := isIso_ihomAdjunction_counit_app π e ((Mod.tensorLeft M).obj N)
  have : IsIso ((Mod.tensorLeft M).map ((Mod.ihomAdjunction M).unit.app N) ≫
      (Mod.ihomAdjunction M).counit.app ((Mod.tensorLeft M).obj N)) := by
    erw [(Mod.ihomAdjunction M).left_triangle_components N]
    exact IsIso.id _
  have : IsIso ((Mod.tensorLeft M).map ((Mod.ihomAdjunction M).unit.app N)) :=
    IsIso.of_isIso_comp_right _ ((Mod.ihomAdjunction M).counit.app ((Mod.tensorLeft M).obj N))
  exact isIso_of_reflects_iso _ (Mod.tensorLeft M)

/-- If `π^* M ≅ ℚ̄_ℓ` for a quasi-compact surjective weakly étale `π`, then
`N ≅ 𝓗om(M, N ⊗_{ℚ̄_ℓ} M)` through the unit. -/
noncomputable def ihomTensorLeftIso (N : AdicSheaf l Y) :
    N ≅ (AdicSheaf.ihom M).obj ((Mod.tensorLeft M).obj N) :=
  have := isIso_ihomAdjunction_unit_app π e N
  asIso ((Mod.ihomAdjunction M).unit.app N)

@[simp]
lemma ihomTensorLeftIso_hom (N : AdicSheaf l Y) :
    (ihomTensorLeftIso π e N).hom = (Mod.ihomAdjunction M).unit.app N :=
  rfl

end AdicSheaf

end AlgebraicGeometry.ProEtale
