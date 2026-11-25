/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.CompUnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!

# Restriction of a pushforward along a section

Let `p : Z ⟶ U` be a morphism of schemes with a section `ι : U ⟶ Z`, `ι ≫ p = 𝟙 U`. For a
module object `N` on `Z`, the map `p_* N ⟶ ι^* N` obtained from the counit of `p^* ⊣ p_*`,
```
p_* N ≅ (𝟙 U)^* p_* N = (ι ≫ p)^* p_* N ≅ ι^* p^* p_* N ⟶ ι^* N,
```
is `p_*` of the unit `N ⟶ ι_* ι^* N` followed by `p_* ι_* ≅ (ι ≫ p)_* = (𝟙 U)_* ≅ 𝟭`
(`ProEtale.CondensedRing.upperStarComp_hom_app_map_counit_eq_lowerStar_map_unit`). This is the
general statement `CategoryTheory.Adjunction.counit_eq_unit_of_comp_eq_id`, the composition and
identity isomorphisms of the pullbacks being conjugate to those of the pushforwards.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The unit of `(f ≫ g)^* ⊣ (f ≫ g)_*` followed by the composition isomorphism of the pullbacks is
the composite of the units, followed by the composition isomorphism of the pushforwards. -/
lemma upperStarLowerStarAdjunction_unit_app_upperStarComp {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (upperStarLowerStarAdjunction Λ g).unit.app M ≫
        (g)_*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ f).unit.app ((g)^*⟦Λ⟧.obj M)) ≫
        (lowerStarComp Λ f g).hom.app ((f)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) =
      (upperStarLowerStarAdjunction Λ (f ≫ g)).unit.app M ≫
        (f ≫ g)_*⟦Λ⟧.map ((upperStarComp Λ f g).hom.app M) := by
  have h := unit_conjugateEquiv ((upperStarLowerStarAdjunction Λ g).comp
    (upperStarLowerStarAdjunction Λ f)) (upperStarLowerStarAdjunction Λ (f ≫ g))
    (upperStarComp Λ f g).hom M
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarComp,
    Adjunction.comp_unit_app] at h
  simp only [Category.assoc] at h
  exact h

/-- The unit of `c^* ⊣ c_*` along `c = 𝟙`, followed by `c^* ≅ (𝟙)^* ≅ 𝟭`, is the inverse of
`c_* ≅ (𝟙)_* ≅ 𝟭`. -/
lemma upperStarLowerStarAdjunction_unit_app_upperStarId {U : Scheme.{u}} {c : U ⟶ U}
    (h : c = 𝟙 U) (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (upperStarLowerStarAdjunction Λ c).unit.app M ≫
        (c)_*⟦Λ⟧.map ((upperStarCongr Λ h ≪≫ upperStarId Λ U).hom.app M) =
      (lowerStarCongr Λ h ≪≫ lowerStarId Λ U).inv.app M := by
  have h₁ := unit_conjugateEquiv (upperStarLowerStarAdjunction Λ (𝟙 U))
    (upperStarLowerStarAdjunction Λ c) (upperStarCongr Λ h).hom M
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarCongr] at h₁
  have h₂ := unit_conjugateEquiv Adjunction.id (upperStarLowerStarAdjunction Λ (𝟙 U))
    (upperStarId Λ U).hom M
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarId] at h₂
  have nat := (lowerStarCongr Λ h).inv.naturality ((upperStarId Λ U).hom.app M)
  have h₀ : (Adjunction.id (C := Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))).unit.app M = 𝟙 M := rfl
  rw [h₀] at h₂
  erw [Category.id_comp] at h₂
  rw [Iso.symm_hom] at h₂
  rw [Iso.symm_hom] at h₁
  rw [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, ← Category.assoc, ← h₁,
    Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  erw [← nat]
  rw [← Category.assoc, ← h₂]
  rfl

/-- **Restriction of a pushforward along a section**: for `ι ≫ p = 𝟙 U`, the restriction
`p_* N ⟶ ι^* N` through the counit of `p^* ⊣ p_*` is `p_*` of the unit of `ι^* ⊣ ι_*`, up to the
composition and identity isomorphisms of the pushforwards. -/
lemma upperStarComp_hom_app_map_counit_eq_lowerStar_map_unit {U Z : Scheme.{u}} (ι : U ⟶ Z)
    (p : Z ⟶ U) (h : ι ≫ p = 𝟙 U)
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (upperStarId Λ U).inv.app ((p)_*⟦Λ⟧.obj N) ≫
        (upperStarCongr Λ h.symm).hom.app ((p)_*⟦Λ⟧.obj N) ≫
        (upperStarComp Λ ι p).hom.app ((p)_*⟦Λ⟧.obj N) ≫
        (ι)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ p).counit.app N) =
      (p)_*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ ι).unit.app N) ≫
        (lowerStarComp Λ ι p).hom.app ((ι)^*⟦Λ⟧.obj N) ≫
        (lowerStarCongr Λ h).hom.app ((ι)^*⟦Λ⟧.obj N) ≫
        (lowerStarId Λ U).hom.app ((ι)^*⟦Λ⟧.obj N) := by
  have H := Adjunction.counit_eq_unit_of_comp_eq_id (upperStarLowerStarAdjunction Λ ι)
    (upperStarLowerStarAdjunction Λ p) (upperStarLowerStarAdjunction Λ (ι ≫ p))
    (upperStarComp Λ ι p) (lowerStarComp Λ ι p)
    (upperStarLowerStarAdjunction_unit_app_upperStarComp Λ ι p)
    (upperStarCongr Λ h ≪≫ upperStarId Λ U) (lowerStarCongr Λ h ≪≫ lowerStarId Λ U)
    (fun M ↦ upperStarLowerStarAdjunction_unit_app_upperStarId Λ h M) N
  have hc : (upperStarCongr Λ h).inv = (upperStarCongr Λ h.symm).hom := rfl
  rw [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, hc] at H
  simp only [Category.assoc] at H
  exact H

end AlgebraicGeometry.ProEtale.CondensedRing
