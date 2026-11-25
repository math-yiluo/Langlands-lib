/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift

/-!
# The exceptional projection morphism commutes with the shifts

For a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, the exceptional projection morphism
`PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` of module objects over `Λ` commutes with the
shifts in `B` (`ProEtale.CondensedRing.commShift_exceptionalProjectionMorphismOfCompactification`):
it is built from the projection morphism of `Lg^* ⊣ Rg_*`, the inverse of the projection
comparison of `Di_! ⊣ Li^*` and the identification `Lf^* ≅ Lg^* ⋙ Li^*`, which all do.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

-- Reuse the tensor and colimit instances when elaborating composite derived functors.
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The projection comparison `q_{j,M,N} : Dj_! (M ⊗ᴸ Lj^* N) ⟶ Dj_! M ⊗ᴸ N` of an open
immersion is the projection map of the adjunction `Dj_! ⊣ Lj^*` for the lax monoidal
structure of `Lj^*`. -/
lemma openImmersionProjectionComparison_eq
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    openImmersionProjectionComparison Λ j M N =
      (((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).projectionMap
        L((j)^*⟦Λ⟧) (curriedTensor _) (curriedTensor _)
        (Functor.LaxMonoidal.μNatTrans L((j)^*⟦Λ⟧))).app M).app N := by
  rw [Adjunction.projectionMap_app_app]
  rfl

/-- The lax monoidal structure of `Lj^*` commutes with the shifts in the second variable: it is
the inverse of the tensor comparison, which does. -/
instance commShift_μNatTrans_leftDerivedUpperStar_app
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    NatTrans.CommShift (F₁ := L((j)^*⟦Λ⟧) ⋙ (curriedTensor _).obj (L((j)^*⟦Λ⟧).obj K))
      (F₂ := (curriedTensor _).obj K ⋙ L((j)^*⟦Λ⟧))
      ((Functor.LaxMonoidal.μNatTrans L((j)^*⟦Λ⟧)).app K) ℤ := by
  have e : (Functor.LaxMonoidal.μNatTrans L((j)^*⟦Λ⟧)).app K =
      (asIso ((leftDerivedUpperStarTensor Λ j).app K)).inv := by
    ext N
    rw [← cancel_epi (((leftDerivedUpperStarTensor Λ j).app K).app N)]
    exact (Functor.Monoidal.δ_μ L((j)^*⟦Λ⟧) K N).trans
      ((asIso ((leftDerivedUpperStarTensor Λ j).app K)).hom_inv_id_app N).symm
  rw [e]
  exact NatTrans.CommShift.of_iso_inv _ ℤ

/-- The projection comparison `q_j` of an open immersion commutes with the shifts in its second
variable. -/
instance commShift_openImmersionProjectionComparison
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    NatTrans.CommShift (F₁ := (L((j)^*⟦Λ⟧) ⋙ (curriedTensor _).obj M) ⋙ D((j)_!open⟦Λ⟧))
      (F₂ := (curriedTensor _).obj (D((j)_!open⟦Λ⟧).obj M))
      (((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).projectionMap
        L((j)^*⟦Λ⟧) (curriedTensor _) (curriedTensor _)
        (Functor.LaxMonoidal.μNatTrans L((j)^*⟦Λ⟧))).app M) ℤ :=
  have : (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).CommShift ℤ :=
    commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction_ofNatIsoRight Λ j
  Adjunction.commShift_projectionMap_app _ _ _ _ _ M

end OpenImmersion

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The identification `Lf^* ≅ Lg^* ⋙ Li^*` for a compactification `(i, g)` of `f` commutes with
the shifts. -/
instance commShift_leftDerivedUpperStarCompactificationIso_inv :
    NatTrans.CommShift (leftDerivedUpperStarCompactificationIso Λ c).inv ℤ := by
  have h : ∀ (h₁ h₂ : X ⟶ Y) (e : h₁ = h₂),
      NatTrans.CommShift (eqToIso (congrArg (fun h : X ⟶ Y ↦ L((h)^*⟦Λ⟧)) e)).hom ℤ := by
    rintro h₁ _ rfl
    exact inferInstanceAs (NatTrans.CommShift (𝟙 L((h₁)^*⟦Λ⟧)) ℤ)
  have := h _ _ c.comm
  have : NatTrans.CommShift (leftDerivedUpperStarCompactificationIso Λ c).hom ℤ := by
    dsimp only [leftDerivedUpperStarCompactificationIso, Iso.trans_hom]
    infer_instance
  exact NatTrans.CommShift.of_iso_inv _ ℤ

/-- The exceptional projection morphism `PF^!_{f,K,-}` of a compactification, as a natural
transformation `Rf_! K ⊗ᴸ - ⟶ Rf_! (K ⊗ᴸ Lf^* -)`. -/
@[simps]
noncomputable def exceptionalProjectionMorphismOfCompactificationNatTrans
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (curriedTensor _).obj ((Rf_!(c)⟦Λ⟧).obj K) ⟶
      (L((f)^*⟦Λ⟧) ⋙ (curriedTensor _).obj K) ⋙ Rf_!(c)⟦Λ⟧ where
  app B := exceptionalProjectionMorphismOfCompactification Λ c K B
  naturality _ _ h := exceptionalProjectionMorphismOfCompactification_natural_right Λ c K h

set_option synthInstance.maxSize 4096 in
/-- **The exceptional projection morphism commutes with the shifts** in its second variable. -/
instance commShift_exceptionalProjectionMorphismOfCompactificationNatTrans
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    NatTrans.CommShift (exceptionalProjectionMorphismOfCompactificationNatTrans Λ c K) ℤ := by
  let τ₁ : (curriedTensor _).obj (R((c.g)_*⟦Λ⟧).obj (D((c.i)_!open⟦Λ⟧).obj K)) ⟶
      (L((c.g)^*⟦Λ⟧) ⋙ (curriedTensor _).obj (D((c.i)_!open⟦Λ⟧).obj K)) ⋙ R((c.g)_*⟦Λ⟧) :=
    (projectionMap Λ c.g).app (D((c.i)_!open⟦Λ⟧).obj K)
  have : NatTrans.CommShift τ₁ ℤ := commShift_projectionMap_app Λ c.g _
  let τ₂ : (L((c.i)^*⟦Λ⟧) ⋙ (curriedTensor _).obj K) ⋙ D((c.i)_!open⟦Λ⟧) ⟶
      (curriedTensor _).obj (D((c.i)_!open⟦Λ⟧).obj K) :=
    ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i).projectionMap
      L((c.i)^*⟦Λ⟧) (curriedTensor _) (curriedTensor _)
      (Functor.LaxMonoidal.μNatTrans L((c.i)^*⟦Λ⟧))).app K
  have : NatTrans.CommShift τ₂ ℤ := commShift_openImmersionProjectionComparison Λ c.i K
  have : IsIso τ₂ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    rw [← openImmersionProjectionComparison_eq]
    infer_instance
  have : NatTrans.CommShift (inv τ₂) ℤ := NatTrans.CommShift.of_iso_inv (asIso τ₂) ℤ
  let τ₃ := (leftDerivedUpperStarCompactificationIso Λ c).inv
  have e : exceptionalProjectionMorphismOfCompactificationNatTrans Λ c K =
      τ₁ ≫ Functor.whiskerRight (Functor.whiskerLeft L((c.g)^*⟦Λ⟧) (inv τ₂)) R((c.g)_*⟦Λ⟧) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L((c.g)^*⟦Λ⟧) (Functor.associator _ _ _).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv
        (D((c.i)_!open⟦Λ⟧) ⋙ R((c.g)_*⟦Λ⟧)) ≫
      Functor.whiskerRight (Functor.whiskerRight τ₃ ((curriedTensor _).obj K))
        (D((c.i)_!open⟦Λ⟧) ⋙ R((c.g)_*⟦Λ⟧)) := by
    ext B
    simp only [exceptionalProjectionMorphismOfCompactificationNatTrans_app,
      exceptionalProjectionMorphismOfCompactification, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, NatIso.isIso_inv_app, Functor.comp_map, Category.id_comp,
      CategoryTheory.Functor.map_id, Functor.map_comp]
    erw [Category.id_comp, Category.id_comp]
    rfl
  have : NatTrans.CommShift τ₃ ℤ := inferInstance
  have h1 : NatTrans.CommShift
    (Functor.whiskerRight (Functor.whiskerLeft L((c.g)^*⟦Λ⟧) (inv τ₂)) R((c.g)_*⟦Λ⟧)) ℤ :=
    inferInstance
  have h3 : NatTrans.CommShift (Functor.whiskerRight (Functor.whiskerRight τ₃
    ((curriedTensor _).obj K)) (D((c.i)_!open⟦Λ⟧) ⋙ R((c.g)_*⟦Λ⟧))) ℤ := inferInstance
  have a1 : NatTrans.CommShift (Functor.associator L((c.g)^*⟦Λ⟧)
    ((L((c.i)^*⟦Λ⟧) ⋙ (curriedTensor _).obj K) ⋙ D((c.i)_!open⟦Λ⟧)) R((c.g)_*⟦Λ⟧)).hom ℤ :=
    inferInstance
  have a2 : NatTrans.CommShift (Functor.whiskerLeft L((c.g)^*⟦Λ⟧) (Functor.associator
    (L((c.i)^*⟦Λ⟧) ⋙ (curriedTensor _).obj K) D((c.i)_!open⟦Λ⟧) R((c.g)_*⟦Λ⟧)).hom) ℤ :=
    inferInstance
  have a3 : NatTrans.CommShift (Functor.associator L((c.g)^*⟦Λ⟧)
    (L((c.i)^*⟦Λ⟧) ⋙ (curriedTensor _).obj K) (D((c.i)_!open⟦Λ⟧) ⋙ R((c.g)_*⟦Λ⟧))).inv ℤ :=
    inferInstance
  have a4 : NatTrans.CommShift (Functor.whiskerRight (Functor.associator L((c.g)^*⟦Λ⟧)
    L((c.i)^*⟦Λ⟧) ((curriedTensor _).obj K)).inv (D((c.i)_!open⟦Λ⟧) ⋙ R((c.g)_*⟦Λ⟧))) ℤ :=
    inferInstance
  rw [e]
  infer_instance

end OfCompactification

end AlgebraicGeometry.ProEtale.CondensedRing
