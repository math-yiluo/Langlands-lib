/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal

/-!
# The exceptional base change map at the unit for an open immersion

Let `j : U ⟶ V` be an open immersion of separated `k₁`-schemes of finite type and
`j' : U' ⟶ V'` an open immersion of separated `k₂`-schemes of finite type, together with maps
`πU : U' ⟶ U`, `πV : V' ⟶ V` such that `πU ≫ j = j' ≫ πV`. For **any** compact-support base change
isomorphism `bc : Rj_! ⋙ πV^* ≅ πU^* ⋙ Rj'_!` and any isomorphism `e : πV^* ℚ̄_ℓ ≅ ℚ̄_ℓ`, the
exceptional base change map at the unit `smoothUnitBaseChange : πU^* Rj^! ℚ̄_ℓ ⟶ Rj'^! ℚ̄_ℓ` is an
isomorphism (`ProEtale.CondensedRing.isIso_smoothUnitBaseChange_of_isOpenImmersion`).

This is the open-immersion piece of the compatibility of `Rf^!` with a change of the base field
for a smooth `f`, factored locally as an étale map to `𝔸^d_Y`, the open immersion `𝔸^d_Y ⊆ ℙ^d_Y`
and the projection `ℙ^d_Y ⟶ Y`.

## Proof

The formal input is `CategoryTheory.Adjunction.isIso_unitBaseChange_of_isIso_unit`: for
adjunctions `a ⊣ a'`, `b ⊣ b'` with invertible units (`a`, `b` fully faithful) and a natural
isomorphism `a' ⋙ G ≅ H ⋙ b'`, the map `unitBaseChange` attached to an invertible base change
morphism and an invertible `e` is invertible, whatever the base change morphism is. Indeed it is
`η'_{G a' U} ≫ b'(bc⁻¹) ≫ b' H (ε_U) ≫ b'(e)`, and `b' H (ε_U)` is conjugate to `G a' (ε_U)`,
which is invertible by the triangle identity.

For `Rj_! ⊣ Rj^!`, `Rj_! ≅ j_!` is the extension by zero
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl`),
which is fully faithful, and `Rj^! ≅ j^*`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl`), so that
`Rj^! ⋙ πU^* ≅ j^* ⋙ πU^* ≅ πV^* ⋙ j'^* ≅ πV^* ⋙ Rj'^!` by the composition isomorphisms of the
derived pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  {a : C ⥤ D} {a' : D ⥤ C} (adj : a ⊣ a') {b : C' ⥤ D'} {b' : D' ⥤ C'} (adj' : b ⊣ b')
  {G : C ⥤ C'} {H : D ⥤ D'} (bc : a ⋙ H ⟶ G ⋙ b) [IsIso bc] {U : D} {U' : D'}
  (e : H.obj U ⟶ U')

/-- For adjunctions `a ⊣ a'` and `b ⊣ b'` with invertible units and a natural isomorphism
`τ : a' ⋙ G ≅ H ⋙ b'`, the map `CategoryTheory.Adjunction.unitBaseChange` attached to any
invertible base change morphism `bc` and any invertible `e` is invertible. -/
lemma isIso_unitBaseChange_of_isIso_unit [IsIso adj.unit] [IsIso adj'.unit] [IsIso e]
    (τ : a' ⋙ G ≅ H ⋙ b') : IsIso (unitBaseChange adj adj' bc e) := by
  have : IsIso (a'.map (adj.counit.app U)) := by
    have : IsIso (adj.unit.app (a'.obj U) ≫ a'.map (adj.counit.app U)) := by
      rw [adj.right_triangle_components U]; exact IsIso.id _
    exact IsIso.of_isIso_comp_left (adj.unit.app (a'.obj U)) _
  have : IsIso (b'.map (H.map (adj.counit.app U))) := by
    have h := τ.hom.naturality (adj.counit.app U)
    simp only [Functor.comp_map] at h
    have : IsIso (τ.hom.app _ ≫ b'.map (H.map (adj.counit.app U))) := by
      rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_left (τ.hom.app _) _
  simp only [unitBaseChange, Functor.comp_obj, Functor.id_obj, mateEquiv_apply, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.comp_id, Category.id_comp, Functor.comp_map, Category.assoc]
  infer_instance

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section OpenImmersion

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The unit of `Rj_! ⊣ Rj^!` along an open immersion is an isomorphism: `Rj_!` is isomorphic to
the extension by zero, which is fully faithful. -/
instance isIso_boundedConstructibleUpperShriekAdjunction_unit_of_isOpenImmersion :
    IsIso (boundedConstructibleUpperShriekAdjunction ℓ j).unit := by
  have hL := ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ j).fullyFaithfulLOfIsIsoUnit).ofIso
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).symm
  have := hL.full
  have := hL.faithful
  exact (boundedConstructibleUpperShriekAdjunction ℓ j).unit_isIso_of_L_fully_faithful

end OpenImmersion

section BaseChange

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {U V : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  {U' V' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  (j : U ⟶ V) (j' : U' ⟶ V') [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {πU : U'.left ⟶ U.left} {πV : V'.left ⟶ V.left}

/-- The pullbacks commute with the restrictions to opens: `j^* ⋙ πU^* ≅ πV^* ⋙ j'^*` on bounded
constructible complexes for a commutative square `πU ≫ j = j' ≫ πV`, from the composition
isomorphisms of the derived pullbacks. -/
noncomputable def boundedConstructibleUpperStarCompUpperStarOfMapIso
    (h : πU ≫ j.left = j'.left ≫ πV) :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l j ⋙
        boundedConstructibleUpperStarOfMap l (X := U) (Y := U') πU ≅
      boundedConstructibleUpperStarOfMap l (X := V) (Y := V') πV ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l j' :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftCompιIso _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility _ l j) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp _ πU j.left).symm ≪≫
      eqToIso (by rw [h]) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp _ j'.left πV) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility _ l j').symm ≪≫
      (Functor.associator _ _ _).symm)

variable (bc : boundedConstructibleLowerShriek l j ⋙ boundedConstructibleUpperStarOfMap l πV ≅
    boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l j')
  (e : (boundedConstructibleUpperStarOfMap l πV).obj (𝟙_ _) ⟶ 𝟙_ _)

/-- **Exceptional base change at the unit for an open immersion.** For open immersions `j`, `j'`
in a commutative square `πU ≫ j = j' ≫ πV`, any compact-support base change isomorphism `bc` and
any isomorphism `e : πV^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`, the map `πU^* Rj^! ℚ̄_ℓ ⟶ Rj'^! ℚ̄_ℓ` is an isomorphism. -/
theorem isIso_smoothUnitBaseChange_of_isOpenImmersion (h : πU ≫ j.left = j'.left ≫ πV)
    [IsIso e] : IsIso (smoothUnitBaseChange l j j' bc e) :=
  Adjunction.isIso_unitBaseChange_of_isIso_unit _ _ _ _
    (Functor.isoWhiskerRight (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl l j) _ ≪≫
      boundedConstructibleUpperStarCompUpperStarOfMapIso l j j' h ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl l j').symm)

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
