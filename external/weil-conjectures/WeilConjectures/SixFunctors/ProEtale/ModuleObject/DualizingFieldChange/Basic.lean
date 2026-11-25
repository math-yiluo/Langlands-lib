/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange
import WeilConjectures.Tactic.ExactModProofs

/-!

# Dualizing complexes of proper schemes and change of the base field

Let `F` and `L` be fields, `πₛ : Spec L ⟶ Spec F` a morphism (for instance that of a field
extension `F ⟶ L`), `X` a proper `F`-scheme and `X_L` an `L`-scheme with a cartesian square

```
X_L --π--> X
 |         |
a_L        a
 v         v
Spec L -πₛ-> Spec F
```

This file constructs the comparison map `φ : π^* ω_X ⟶ ω_{X_L}` of the dualizing complexes
(`ProEtale.CondensedRing.dualizingComplexBaseChange`, for a map `e : πₛ^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`, in practice
the inverse of the unit isomorphism of the monoidal functor `πₛ^*`) and proves its compatibility
with the traces
(`ProEtale.CondensedRing.baseChange_comp_map_dualizingComplexBaseChange_comp_trace`):
`tr_{X_L} ∘ Ra_{L*}(φ) ∘ BC(ω_X) = e ∘ πₛ^*(tr_X)`, which characterizes it
(`ProEtale.CondensedRing.eq_dualizingComplexBaseChange_of_trace`).

The map is the mate, under the adjunctions `Ra_* ⊣ Ra^!` and `Ra_{L*} ⊣ Ra_L^!`, of the inverse of
the proper base change morphism `BC : πₛ^* Ra_* ⟶ Ra_{L*} π^*` on bounded constructible
complexes (`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap`), evaluated at the unit.
`BC` is invertible by proper base change over an arbitrary base
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`). The formal part is
`CategoryTheory.Adjunction.unitBaseChange`.

## Not treated here

That `φ` is an isomorphism (duality commutes with any base change of the base field, SGA 4½
[Th. finitude]). It is not a formal consequence of the base change isomorphism: the mate of an
isomorphism need not be invertible.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### The formal construction -/

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  {a : C ⥤ D} {a' : D ⥤ C} (adj : a ⊣ a') {b : C' ⥤ D'} {b' : D' ⥤ C'} (adj' : b ⊣ b')
  {G : C ⥤ C'} {H : D ⥤ D'} (bc : a ⋙ H ⟶ G ⋙ b) [IsIso bc] {U : D} {U' : D'}
  (e : H.obj U ⟶ U')

/-- For adjunctions `a ⊣ a'`, `b ⊣ b'` and an invertible base change morphism
`bc : H a ⟶ b G`, the map `G a' U ⟶ b' U'` attached to `e : H U ⟶ U'`: the mate of `bc⁻¹`
evaluated at `U`, followed by `b'(e)`. For the structure morphisms `a`, `b` of a proper scheme and
of its base change, and `U`, `U'` the units, it is the comparison `π^* ω_X ⟶ ω_{X_L}` of the
dualizing complexes. -/
noncomputable def unitBaseChange : G.obj (a'.obj U) ⟶ b'.obj U' :=
  (mateEquiv adj adj' (inv bc)).app U ≫ b'.map e

/-- The **trace compatibility** of `CategoryTheory.Adjunction.unitBaseChange`:
`bc ≫ b(φ) ≫ ε' = H(ε) ≫ e` for the counits `ε`, `ε'`. -/
@[reassoc]
lemma app_comp_map_unitBaseChange_comp_counit :
    bc.app (a'.obj U) ≫ b.map (unitBaseChange adj adj' bc e) ≫ adj'.counit.app U' =
      H.map (adj.counit.app U) ≫ e := by
  have h := mateEquiv_counit adj adj' (inv bc) U
  have h₂ : b.map (b'.map e) ≫ adj'.counit.app U' = adj'.counit.app (H.obj U) ≫ e :=
    adj'.counit.naturality e
  simp only [unitBaseChange, Functor.map_comp, Category.assoc]
  rw [h₂, reassoc_of% h]
  simp

/-- `CategoryTheory.Adjunction.unitBaseChange` is the only map with the trace compatibility
`CategoryTheory.Adjunction.app_comp_map_unitBaseChange_comp_counit`. -/
lemma eq_unitBaseChange_of_comp_counit {φ : G.obj (a'.obj U) ⟶ b'.obj U'}
    (h : bc.app (a'.obj U) ≫ b.map φ ≫ adj'.counit.app U' = H.map (adj.counit.app U) ≫ e) :
    φ = unitBaseChange adj adj' bc e := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit, ← cancel_epi (bc.app (a'.obj U)), h,
    app_comp_map_unitBaseChange_comp_counit]

/-- `CategoryTheory.Adjunction.unitBaseChange` transported along equalities `a' U = ω` and
`b' U' = ω'`, to avoid unfolding `ω` and `ω'` (in practice, dualizing complexes). -/
noncomputable def unitBaseChangeOfEq {ω : C} (hω : a'.obj U = ω) {ω' : C'} (hω' : b'.obj U' = ω') :
    G.obj ω ⟶ ω' :=
  eqToHom (congrArg G.obj hω.symm) ≫ unitBaseChange adj adj' bc e ≫ eqToHom hω'

/-- The trace compatibility of `CategoryTheory.Adjunction.unitBaseChangeOfEq`, for maps `t`, `t'`
which are the counits transported along the equalities. -/
lemma app_comp_map_unitBaseChangeOfEq_comp {ω : C} (hω : a'.obj U = ω) {ω' : C'}
    (hω' : b'.obj U' = ω') {t : a.obj ω ⟶ U}
    (ht : eqToHom (congrArg a.obj hω) ≫ t = adj.counit.app U)
    {t' : b.obj ω' ⟶ U'} (ht' : eqToHom (congrArg b.obj hω') ≫ t' = adj'.counit.app U') :
    bc.app ω ≫ b.map (unitBaseChangeOfEq adj adj' bc e hω hω') ≫ t' = H.map t ≫ e := by
  subst hω hω'
  simp only [eqToHom_refl, Category.id_comp] at ht ht'
  subst ht ht'
  simp [unitBaseChangeOfEq, app_comp_map_unitBaseChange_comp_counit]

/-- `CategoryTheory.Adjunction.unitBaseChangeOfEq` is the only map with the trace compatibility
`CategoryTheory.Adjunction.app_comp_map_unitBaseChangeOfEq_comp`. -/
lemma eq_unitBaseChangeOfEq_of_comp {ω : C} (hω : a'.obj U = ω) {ω' : C'}
    (hω' : b'.obj U' = ω') {t : a.obj ω ⟶ U}
    (ht : eqToHom (congrArg a.obj hω) ≫ t = adj.counit.app U)
    {t' : b.obj ω' ⟶ U'} (ht' : eqToHom (congrArg b.obj hω') ≫ t' = adj'.counit.app U')
    {φ : G.obj ω ⟶ ω'} (h : bc.app ω ≫ b.map φ ≫ t' = H.map t ≫ e) :
    φ = unitBaseChangeOfEq adj adj' bc e hω hω' := by
  subst hω hω'
  simp only [eqToHom_refl, Category.id_comp] at ht ht'
  subst ht ht'
  simpa [unitBaseChangeOfEq] using eq_unitBaseChange_of_comp_counit adj adj' bc e h

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Base change along morphisms of schemes over different fields -/

section BaseChangeOfMap

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {X Y : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y'.left ⟶ Y.left} {g' : X'.left ⟶ X.left}

/-- The base change morphism `Lg^* Rf_* ⟶ Rf'_* Lg'^*` on bounded constructible complexes for a
commutative square `g' ≫ f = f' ≫ g` of schemes of finite type over possibly different fields: the
restriction of the ambient base change morphism `ProEtale.CondensedRing.baseChangeMap`. -/
noncomputable def boundedConstructibleBaseChangeOfMap (sq : CommSq g' f'.left f.left g) :
    boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g' ⋙
        boundedConstructibleLowerStar ℓ f' :=
  NearbyCyclesModel.liftExchange (baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f' K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g' K.obj K.property)

/-- **Proper base change** on bounded constructible complexes, for a cartesian square of schemes
of finite type over possibly different fields: the restriction of
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`. -/
theorem isIso_boundedConstructibleBaseChangeOfMap [IsProper f.left]
    (sq : IsPullback g' f'.left f.left g) :
    IsIso (boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  rw [← ObjectProperty.isIso_hom_iff]
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  have : IsNoetherian Y'.left := isNoetherian_of_locallyOfFiniteType Y'.hom
  have := isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ Y.hom Y'.hom sq.toCommSq sq K.obj
    K.property
  unfold boundedConstructibleBaseChangeOfMap boundedConstructibleLowerStar
    boundedConstructibleUpperStarOfMap
  rw [NearbyCyclesModel.liftExchange_app_hom]
  dsimp only [Functor.comp_obj, ObjectProperty.lift_obj_obj, ObjectProperty.ι_obj] at this ⊢
  cast_proofs this

end BaseChangeOfMap
/-! ### The comparison of dualizing complexes of proper schemes -/

section Dualizing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]

/-- The adjunction `Ra_* ⊣ Ra^!` for the structure morphism `a` of a proper scheme: the adjunction
`Ra_! ⊣ Ra^!` read through `Ra_! ≅ Ra_*`. Its counit at the unit is the trace
`NearbyCyclesModel.trace`. -/
noncomputable def properLowerStarUpperShriekAdjunction (X : Over (Spec (.of k₁)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsProper (toPoint X).left] :
    boundedConstructibleLowerStar ℓ (toPoint X) ⊣
      boundedConstructibleUpperShriek ℓ (toPoint X) :=
  (boundedConstructibleUpperShriekAdjunction ℓ (toPoint X)).ofNatIsoLeft
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X))

/-- The counit of `Ra_* ⊣ Ra^!` at the unit is the trace. -/
lemma properLowerStarUpperShriekAdjunction_counit_app_unit (X : Over (Spec (.of k₁)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsProper (toPoint X).left] :
    (properLowerStarUpperShriekAdjunction ℓ X).counit.app (𝟙_ _) = NearbyCyclesModel.trace ℓ X :=
  rfl

/-- The dualizing complex of `X` is the exceptional inverse image of the unit along the structure
morphism `toPoint X`. -/
lemma upperShriek_toPoint_obj_unit (X : Over (Spec (.of k₁))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] :
    (boundedConstructibleUpperShriek ℓ (toPoint X)).obj (𝟙_ _) = dualizingComplex ℓ X :=
  rfl

variable {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [IsProper (toPoint X).left]
  {X' : Over (Spec (.of k₂))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [IsProper (toPoint X').left]
  {π : X'.left ⟶ X.left} {πₛ : Spec (.of k₂) ⟶ Spec (.of k₁)}
  (e : (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).obj (𝟙_ _) ⟶
    𝟙_ _)

/-- The trace is the counit of `Ra_* ⊣ Ra^!`, transported along `Ra^! ℚ̄_ℓ = ω_X`. -/
lemma eqToHom_comp_trace (X : Over (Spec (.of k₁))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [IsProper (toPoint X).left] :
    eqToHom (congrArg (boundedConstructibleLowerStar ℓ (toPoint X)).obj
        (upperShriek_toPoint_obj_unit ℓ X)) ≫ NearbyCyclesModel.trace ℓ X =
      (properLowerStarUpperShriekAdjunction ℓ X).counit.app (𝟙_ _) := by
  rw [eqToHom_refl, Category.id_comp]
  rfl

/-- The **comparison of dualizing complexes** `π^* ω_X ⟶ ω_{X'}` along a cartesian square
`π ≫ a = a' ≫ πₛ`, `a` proper, for a map `e : πₛ^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` (in practice the inverse of the unit
isomorphism of the monoidal functor `πₛ^*`): the mate of the inverse of the proper base change
isomorphism `πₛ^* Ra_* ≅ Ra'_* π^*` under `Ra_* ⊣ Ra^!` and `Ra'_* ⊣ Ra'^!`, at the unit,
followed by `Ra'^!(e)` (`CategoryTheory.Adjunction.unitBaseChange`). -/
noncomputable def dualizingComplexBaseChange
    (sq : IsPullback π (toPoint X').left (toPoint X).left πₛ) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π).obj (dualizingComplex ℓ X) ⟶
      dualizingComplex ℓ X' :=
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq
  Adjunction.unitBaseChangeOfEq (properLowerStarUpperShriekAdjunction ℓ X)
    (properLowerStarUpperShriekAdjunction ℓ X') (boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq)
    e (upperShriek_toPoint_obj_unit ℓ X) (upperShriek_toPoint_obj_unit ℓ X')

/-- **Trace compatibility** of the comparison `φ : π^* ω_X ⟶ ω_{X'}` of the dualizing complexes:
`tr_{X'} ∘ Ra'_*(φ) ∘ BC(ω_X) = e ∘ πₛ^*(tr_X)`. -/
theorem baseChange_comp_map_dualizingComplexBaseChange_comp_trace
    (sq : IsPullback π (toPoint X').left (toPoint X).left πₛ) :
    (boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq).app (dualizingComplex ℓ X) ≫
        (boundedConstructibleLowerStar ℓ (toPoint X')).map (dualizingComplexBaseChange ℓ e sq) ≫
          NearbyCyclesModel.trace ℓ X' =
      (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).map
          (NearbyCyclesModel.trace ℓ X) ≫ e := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq
  exact Adjunction.app_comp_map_unitBaseChangeOfEq_comp _ _ _ e (upperShriek_toPoint_obj_unit ℓ X)
    (upperShriek_toPoint_obj_unit ℓ X') (eqToHom_comp_trace ℓ X)
    (eqToHom_comp_trace ℓ X')

/-- The comparison of dualizing complexes is the only map `π^* ω_X ⟶ ω_{X'}` with the trace
compatibility `ProEtale.CondensedRing.baseChange_comp_map_dualizingComplexBaseChange_comp_trace`. -/
theorem eq_dualizingComplexBaseChange_of_trace
    (sq : IsPullback π (toPoint X').left (toPoint X).left πₛ)
    {φ : (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π).obj (dualizingComplex ℓ X) ⟶
      dualizingComplex ℓ X'}
    (h : (boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq).app (dualizingComplex ℓ X) ≫
        (boundedConstructibleLowerStar ℓ (toPoint X')).map φ ≫ NearbyCyclesModel.trace ℓ X' =
      (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).map
          (NearbyCyclesModel.trace ℓ X) ≫ e) :
    φ = dualizingComplexBaseChange ℓ e sq := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq
  refine Adjunction.eq_unitBaseChangeOfEq_of_comp _ _ _ e (upperShriek_toPoint_obj_unit ℓ X)
    (upperShriek_toPoint_obj_unit ℓ X') (eqToHom_comp_trace ℓ X)
    (eqToHom_comp_trace ℓ X') ?_
  cast_proofs h

end Dualizing

end AlgebraicGeometry.ProEtale.CondensedRing
