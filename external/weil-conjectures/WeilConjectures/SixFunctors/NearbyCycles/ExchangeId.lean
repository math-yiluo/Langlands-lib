/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp

/-!

# The pullback exchange of the identity morphism of models

The pullback exchange `α : L(𝟙)^* Ψ_M ⟶ Ψ_M L(𝟙)^*` of the identity morphism of a model
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.id`) is the composite of the
identity isomorphisms `L(𝟙)^* ≅ 𝟭`
(`NearbyCyclesModel.Hom.id_pullbackExchange_app`). It follows from the unit laws of the
composition isomorphisms of the derived pullbacks (`leftDerivedUpperStarComp_id_left_app`,
`leftDerivedUpperStarComp_id_right_app`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- The mate of a transformation `θ : G ⋙ L ⟶ L ⋙ H` of the form `L(I₁) ≫ I₂⁻¹`, for isomorphisms
`I₁ : G ≅ 𝟭` and `I₂ : H ≅ 𝟭`, is `I₁(R) ≫ R(I₂⁻¹)`. -/
lemma mateEquiv_app_of_isoId {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {G : C ⥤ C} {H : D ⥤ D} (I₁ : G ≅ 𝟭 C) (I₂ : H ≅ 𝟭 D) (θ : G ⋙ L ⟶ L ⋙ H)
    (hθ : ∀ B, θ.app B = L.map (I₁.hom.app B) ≫ I₂.inv.app (L.obj B)) (Y : D) :
    (mateEquiv a a θ).app Y = I₁.hom.app (R.obj Y) ≫ R.map (I₂.inv.app Y) := by
  apply (a.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, mateEquiv_counit, hθ,
    Functor.map_comp, Category.assoc, Category.assoc, a.counit_naturality]
  have h := I₂.inv.naturality (a.counit.app Y)
  simp only [Functor.id_map, Functor.id_obj] at h
  rw [h]
  simp

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Squares

variable {X Y : Scheme.{u}}

/-- The pullback comparison `Lp^* L(𝟙)^* ≅ L(𝟙)^* Lp^*` of the square `p ≫ 𝟙 = 𝟙 ≫ p` is
`I ≫ Lp^*(I⁻¹)`, for the identity isomorphisms `I : L(𝟙)^* ≅ 𝟭`. -/
lemma pullbackSquareComparison_hom_app_id_right (p : X ⟶ Y)
    (sq : CommSq p (𝟙 X) (𝟙 Y) p)
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app B =
      (leftDerivedUpperStarId Λ X).hom.app (L((p)^*⟦Λ⟧).obj B) ≫
        L((p)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).inv.app B) := by
  have h₁ := leftDerivedUpperStarComp_id_left_app Λ p B
  have h₂ := leftDerivedUpperStarComp_id_right_app Λ p B
  simp only [pullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ (𝟙 X) p).hom.app B), Iso.hom_inv_id_app_assoc,
    reassoc_of% h₁]
  rw [← cancel_mono (L((p)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app B))]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, h₂, eqToHom_trans]
  simp

/-- The pullback comparison `L(𝟙)^* Lp^* ≅ Lp^* L(𝟙)^*` of the square `𝟙 ≫ p = p ≫ 𝟙` is
`Lp^*(I) ≫ I⁻¹`, for the identity isomorphisms `I : L(𝟙)^* ≅ 𝟭`. -/
lemma pullbackSquareComparison_hom_app_id_left (p : X ⟶ Y)
    (sq : CommSq (𝟙 X) p p (𝟙 Y))
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app B =
      L((p)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app B) ≫
        (leftDerivedUpperStarId Λ X).inv.app (L((p)^*⟦Λ⟧).obj B) := by
  have h₁ := leftDerivedUpperStarComp_id_left_app Λ p B
  have h₂ := leftDerivedUpperStarComp_id_right_app Λ p B
  simp only [pullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ p (𝟙 Y)).hom.app B), Iso.hom_inv_id_app_assoc,
    reassoc_of% h₂]
  rw [← cancel_mono ((leftDerivedUpperStarId Λ X).hom.app (L((p)^*⟦Λ⟧).obj B))]
  simp only [Category.assoc, Iso.inv_hom_id_app, h₁, eqToHom_trans]
  simp

end Squares

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

/-- **The pullback exchange of a morphism of models with identity components** is the composite of
the identity isomorphisms `I : L(𝟙)^* ≅ 𝟭`: `α_φ(A) = I(Ψ A) ≫ Ψ(I⁻¹(A))`. -/
lemma Hom.pullbackExchange_app_of_eq_id (φ : M.Hom M (𝟙 X) (𝟙 X')) (ht : φ.total = 𝟙 _)
    (hg : φ.generic = 𝟙 _)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (φ.pullbackExchange Λ).app A =
      (leftDerivedUpperStarId Λ X').hom.app ((M.nearbyCycles Λ).obj A) ≫
        (M.nearbyCycles Λ).map ((leftDerivedUpperStarId Λ X).inv.app A) := by
  obtain ⟨total, generic, _, _, _⟩ := φ
  dsimp only at ht hg
  subst ht hg
  have hj := mateEquiv_app_of_isoId (derivedUpperStarLowerStarAdjunction Λ M.j)
    (leftDerivedUpperStarId Λ M.total) (leftDerivedUpperStarId Λ M.generic)
    (pullbackSquareComparison Λ (⟨by simp⟩ : CommSq (𝟙 M.generic) M.j M.j (𝟙 M.total))).hom
    (fun B ↦ pullbackSquareComparison_hom_app_id_left Λ M.j _ B)
  simp only [Hom.pullbackExchange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, hj,
    pullbackSquareComparison_hom_app_id_right Λ M.i,
    pullbackSquareComparison_hom_app_id_right Λ M.ε]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  rfl

/-- **The pullback exchange of the identity morphism of models** is the composite of the identity
isomorphisms `I : L(𝟙)^* ≅ 𝟭`: `α_𝟙(A) = I(Ψ A) ≫ Ψ(I⁻¹(A))`. -/
lemma Hom.id_pullbackExchange_app
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    ((Hom.id M).pullbackExchange Λ).app A =
      (leftDerivedUpperStarId Λ X').hom.app ((M.nearbyCycles Λ).obj A) ≫
        (M.nearbyCycles Λ).map ((leftDerivedUpperStarId Λ X).inv.app A) :=
  Hom.pullbackExchange_app_of_eq_id Λ M _ (Hom.id_total M) (Hom.id_generic M) A

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
