/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModTrace
public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTraceMonoidal

/-!
# The trace of a Galois covering on module objects

Let `Λ` be a commutative condensed ring and `g : Y ⟶ X` a quasi-compact surjective weakly étale
morphism with a Galois action of a finite group `Γ` (`AlgebraicGeometry.ProEtale.IsGaloisAction`),
for instance a finite étale Galois covering. For the adjunction `g^* ⊣ g_*` on module objects over
`Λ` (`AlgebraicGeometry.ProEtale.CondensedRing.upperStarLowerStarAdjunction`), this file constructs
the *trace* `t : g^* ⋙ g_* ⟶ 𝟭` and the action `ρ a` of `a : Γ` on `g^* ⋙ g_*`
(`AlgebraicGeometry.ProEtale.CondensedRing.galoisTrace`,
`AlgebraicGeometry.ProEtale.CondensedRing.galoisAction`), with

* `u ≫ t = |Γ| • 𝟙` (`AlgebraicGeometry.ProEtale.CondensedRing.unit_comp_galoisTrace`),
* `t ≫ u = ∑ a, ρ a` (`AlgebraicGeometry.ProEtale.CondensedRing.galoisTrace_comp_unit`),

for the unit `u` of `g^* ⊣ g_*`. They are the lifts of the trace and the action on abelian sheaves
(`CategoryTheory.Adjunction.mapModTrace`), which are `Λ`-linear since the action is monoidal.
-/

@[expose] public section

universe u

open CategoryTheory Category MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The unit of the extension and restriction of scalars along the isomorphism `α_g` is an
isomorphism. -/
instance isIso_extendRestrictAdjunction_condensedPullbackHom_unit :
    IsIso (Mod.extendRestrictAdjunction (condensedPullbackHom Λ g)).unit := by
  have (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((g)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))) :
      IsIso ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ g)).unit.app N) := by
    have h := Adjunction.unit_leftAdjointUniq_hom_app
      (Mod.extendRestrictAdjunction (condensedPullbackHom Λ g))
      (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ g)).symm.toAdjunction N
    have : IsIso ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ g)).unit.app N ≫
        (Mod.comap (condensedPullbackHom Λ g)).map
          ((Adjunction.leftAdjointUniq (Mod.extendRestrictAdjunction (condensedPullbackHom Λ g))
            (Mod.comapEquivalenceOfIsIso
              (condensedPullbackHom Λ g)).symm.toAdjunction).hom.app N)) := by
      erw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((Mod.comap (condensedPullbackHom Λ g)).map
          ((Adjunction.leftAdjointUniq (Mod.extendRestrictAdjunction (condensedPullbackHom Λ g))
            (Mod.comapEquivalenceOfIsIso
              (condensedPullbackHom Λ g)).symm.toAdjunction).hom.app N))
  exact NatIso.isIso_of_isIso_app _

/-- The comparison `G (F M) ⟶ g_* g^* M` between the composite of the lifted adjunction of
abelian sheaves and the composite `g^* ⋙ g_*` on module objects: extension of scalars along the
isomorphism `α_g` and the identification of the pushforwards. -/
noncomputable def mapModCompToUpperStarLowerStar :
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g).mapModComp (condensedRingObj Λ X) ⟶
      (g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧ :=
  Functor.whiskerLeft ((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X))
      (Functor.whiskerRight (Mod.extendRestrictAdjunction (condensedPullbackHom Λ g)).unit
        (linearLowerStar Λ g)) ≫
    Functor.whiskerLeft ((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X) ⋙
      Mod.extendScalars (condensedPullbackHom Λ g)) (comapPullbackHomCompIso Λ g).hom

instance : IsIso (mapModCompToUpperStarLowerStar Λ g) := by
  unfold mapModCompToUpperStarLowerStar
  infer_instance

/-- The unit of `g^* ⊣ g_*` on module objects is the unit of the lifted adjunction of abelian
sheaves followed by the comparison `mapModCompToUpperStarLowerStar`. -/
lemma upperStarLowerStarAdjunction_unit_eq :
    (upperStarLowerStarAdjunction Λ g).unit =
      ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g).mapModAdjunction
        (condensedRingObj Λ X)).unit ≫ mapModCompToUpperStarLowerStar Λ g := by
  ext M : 2
  simp [upperStarLowerStarAdjunction, mapModCompToUpperStarLowerStar, Adjunction.comp_unit_app]
  rfl


section Trace

variable [WeaklyEtale g] [Surjective g] [QuasiCompact g]
  {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)
  [Group Γ] [Fintype Γ] (hmul : ∀ a b, ρ a ≫ ρ b = ρ (a * b)) (hgal : IsGaloisAction g ρ)

/-- **The trace of a Galois covering on module objects** `g^* ⋙ g_* ⟶ 𝟭`. -/
noncomputable def galoisTrace : (g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧ ⟶ 𝟭 _ :=
  inv (mapModCompToUpperStarLowerStar Λ g) ≫
    Adjunction.mapModTrace (condensedRingObj Λ X) (unit_comp_galoisActionNatTrans g hρ)
      (galoisTraceNatTrans_comp_unit g hρ hmul hgal)

/-- **The action of `a : Γ` on `g^* ⋙ g_*`** for module objects. -/
noncomputable def galoisAction (a : Γ) : (g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧ ⟶ (g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧ :=
  inv (mapModCompToUpperStarLowerStar Λ g) ≫
    Adjunction.mapModAction (condensedRingObj Λ X) (unit_comp_galoisActionNatTrans g hρ) a ≫
      mapModCompToUpperStarLowerStar Λ g

/-- **The unit followed by the trace is the degree**: `u ≫ t = |Γ| • 𝟙` on module objects. -/
theorem unit_comp_galoisTrace :
    (upperStarLowerStarAdjunction Λ g).unit ≫ galoisTrace Λ g hρ hmul hgal =
      Fintype.card Γ • 𝟙 _ := by
  rw [upperStarLowerStarAdjunction_unit_eq, galoisTrace, assoc, IsIso.hom_inv_id_assoc]
  exact Adjunction.unit_comp_mapModTrace _ _ _ (unit_comp_galoisTraceNatTrans g hρ hmul hgal)

/-- **The trace followed by the unit is the norm**: `t ≫ u = ∑ a, ρ a` on module objects. -/
theorem galoisTrace_comp_unit :
    galoisTrace Λ g hρ hmul hgal ≫ (upperStarLowerStarAdjunction Λ g).unit =
      ∑ a, galoisAction Λ g hρ a := by
  rw [upperStarLowerStarAdjunction_unit_eq, galoisTrace, assoc,
    reassoc_of% (Adjunction.mapModTrace_comp_unit (condensedRingObj Λ X) _ _)]
  simp only [galoisAction, Preadditive.sum_comp, Preadditive.comp_sum]

end Trace

end AlgebraicGeometry.ProEtale.CondensedRing
