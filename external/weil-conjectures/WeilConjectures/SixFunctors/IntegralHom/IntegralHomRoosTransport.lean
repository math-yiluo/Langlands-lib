/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomAugmentedTowerComparison
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit

/-! # Canonical augmented reduction products under integral Hom

Source: blueprint order 2478, proof step 8; Stacks Tags 08TC, 0038 and 08JC
(blueprint: lem-sf-integral-hom-roos-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

private theorem homotopyLimit_of_roos
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F : ℕᵒᵖ ⥤ C) (c : Cone F) [HasProduct (fun n : ℕ ↦ F.obj (op n))]
    (δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ c.pt⟦(1 : ℤ)⟧)
    (hδ : IsDerivedLimitTriangle (fun n : ℕ ↦ F.map (homOfLE n.le_succ).op) c.pt
      (Pi.lift (fun n : ℕ ↦ c.π.app (op n))) δ) :
    Pretriangulated.IsHomotopyLimit c := by
  let hP := productIsProduct (fun n : ℕ ↦ F.obj (op n))
  have hfirst : Fan.IsLimit.lift hP (fun n : ℕ ↦ c.π.app (op n)) =
      Pi.lift (fun n : ℕ ↦ c.π.app (op n)) := by
    apply Pi.hom_ext
    intro n
    exact (Fan.IsLimit.fac hP _ n).trans (Pi.lift_comp_π (fun n : ℕ ↦ c.π.app (op n)) n).symm
  have hshift : Pretriangulated.towerShift hP =
      towerProductShift (fun n : ℕ ↦ F.map (homOfLE n.le_succ).op) := by
    apply Pi.hom_ext
    intro n
    change Fan.IsLimit.lift hP _ ≫ (Fan.mk _ (Pi.π _)).proj n = _
    rw [Fan.IsLimit.fac]
    exact (Pi.lift_comp_π (fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1) ≫
      F.map (homOfLE n.le_succ).op) n).symm
  refine ⟨Fan.mk _ (Pi.π _), hP, δ, ?_⟩
  rw [hfirst, hshift]
  exact hδ

private theorem roos_of_homotopyLimit
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F : ℕᵒᵖ ⥤ C) (c : Cone F)
    (hc : Pretriangulated.IsHomotopyLimit c) [HasProduct (fun n : ℕ ↦ F.obj (op n))] :
    ∃ δ, IsDerivedLimitTriangle (fun n : ℕ ↦ F.map (homOfLE n.le_succ).op) c.pt
      (Pi.lift (fun n : ℕ ↦ c.π.app (op n))) δ := by
  obtain ⟨P, hP, δ, hδ⟩ := hc
  let ψ := hP.conePointUniqueUpToIso (productIsProduct (fun n : ℕ ↦ F.obj (op n)))
  have hψ (n : ℕ) : ψ.hom ≫ Pi.π _ n = P.proj n :=
    hP.conePointUniqueUpToIso_hom_comp _ ⟨n⟩
  have hfirst : (Fan.IsLimit.lift hP (fun n : ℕ ↦ c.π.app (op n))) ≫ ψ.hom =
      Pi.lift (fun n : ℕ ↦ c.π.app (op n)) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hψ, Fan.IsLimit.fac, Pi.lift_comp_π]
  have ht : Pretriangulated.towerShift hP ≫ ψ.hom =
      ψ.hom ≫ towerProductShift (fun n : ℕ ↦ F.map (homOfLE n.le_succ).op) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hψ, Pretriangulated.towerShift, Fan.IsLimit.fac]
    simp only [Category.assoc, towerProductShift, Pi.lift_comp_π]
    rw [← Category.assoc, hψ]
  have htransition : (𝟙 P.pt - Pretriangulated.towerShift hP) ≫ ψ.hom =
      ψ.hom ≫ towerTransitionEndomorphism (fun n : ℕ ↦ F.map (homOfLE n.le_succ).op) := by
    change _ = ψ.hom ≫ (𝟙 _ - towerProductShift _)
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, ht, Category.id_comp]
    congr 1
    exact (Category.comp_id ψ.hom).symm
  refine ⟨ψ.inv ≫ δ, Pretriangulated.isomorphic_distinguished _ hδ _
    (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) ψ.symm ψ.symm ?_ ?_ ?_)⟩
  · change _ ≫ ψ.inv = 𝟙 _ ≫ _
    rw [← hfirst]
    simp
  · change towerTransitionEndomorphism _ ≫ ψ.inv =
      ψ.inv ≫ (𝟙 P.pt - Pretriangulated.towerShift hP)
    apply (cancel_mono ψ.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun t ↦ ψ.inv ≫ t) htransition.symm
  · simp

namespace WeilConjectures.IntegralHom

attribute [local implicit_reducible] completedIntegralCoefficientSheaf
  completedIntegralCommRingSheafUnrestricted
  completedIntegralCommRingSheaf CategoryTheory.sheafCompose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The Hom functor carries a complete reduction tower to a complete reduction tower.
The given tensor presentation supplies the right adjunction.
This is the final Roos-triangle transport step of the blueprint. The proof applies the
right-adjoint product comparison to the augmented reduction tower and uses the normalized
finite comparison maps to identify the transition endomorphism componentwise.
Source: blueprint order 2478, proof step 8; Stacks Tags 08TC and 0038
(blueprint: lem-sf-integral-hom-roos-transport).
-/
theorem hom_roosTransport
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (K L : completedIntegralDerivedCategory l E Y D hl)
    (hL : IsDerivedComplete l E Y D hl L) :
    IsDerivedComplete l E Y D hl
      ((hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)) := by
  classical
  let H : completedIntegralDerivedCategory l E Y D hl ⥤
      completedIntegralDerivedCategory l E Y D hl := (Functor.curry.obj
    (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))).obj (op K)
  let : H.CommShift ℤ := RingedHomUniverses.homCommShift.{t + 1, t, u, max u (t + 1) + 1}
    (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (completedIntegralCommRingSheaf l E Y D hl) K
  have : H.IsTriangulated :=
    RingedHomUniverses.hom_isTriangulated.{t + 1, t, u, max u (t + 1) + 1}
    (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (completedIntegralCommRingSheaf l E Y D hl) K
  have : PreservesLimitsOfSize.{0, 0} H := (a.adjunction K).rightAdjoint_preservesLimits
  rcases hL with ⟨P, G, q, hq, e, hprod, δ, hδ⟩
  obtain ⟨P', G', q', hq', e', τ, hτ⟩ :=
    augmentedTower_comparison l E Y D hl K P G q hq
  let F := integralReductionTower l E Y D hl P
  let F' := integralReductionTower l E Y D hl P'
  let : HasProduct (fun n : ℕ ↦ F.obj (op n)) := hprod
  let c := (integralReductionTowerCone l E Y D hl q hq).extend e.inv
  have hc : Pretriangulated.IsHomotopyLimit c := homotopyLimit_of_roos F c δ hδ
  let eH := e' ≪≫ H.mapIso e
  let c' := (integralReductionTowerCone l E Y D hl q' hq').extend eH.inv
  have hc' : Pretriangulated.IsHomotopyLimit c' := by
    apply Pretriangulated.IsHomotopyLimit.of_iso τ (hc.map H) c' (Iso.refl _)
    intro n
    dsimp only [Functor.mapCone, Cone.functoriality, Cone.extend, c, c', eH, Iso.trans_inv,
      Functor.mapIso_inv, NatTrans.comp_app, Functor.const_obj_map, Functor.const_obj_obj,
      Iso.refl_hom]
    change H.map (e.inv ≫ _) ≫ _ = 𝟙 _ ≫ ((H.map e.inv ≫ e'.inv) ≫ _)
    erw [Functor.map_comp, Category.id_comp, Category.assoc, Category.assoc]
    exact congrArg (fun f ↦ H.map e.inv ≫ f) (hτ n).symm
  obtain ⟨Pprod, hPprod, _, _⟩ := (show Pretriangulated.IsHomotopyLimit c' from hc')
  let : HasProduct (fun n : ℕ ↦ F'.obj (op n)) := ⟨⟨Pprod, hPprod⟩⟩
  obtain ⟨δ', hδ'⟩ := roos_of_homotopyLimit F' c' hc'
  exact ⟨P', G', q', hq', eH, inferInstance, δ', hδ'⟩

end WeilConjectures.IntegralHom
