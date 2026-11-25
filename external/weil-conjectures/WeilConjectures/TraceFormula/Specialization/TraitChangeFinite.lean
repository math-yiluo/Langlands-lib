/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
public import WeilConjectures.TraceFormula.Specialization.FinitePointConservative
public import WeilConjectures.TraceFormula.Specialization.TraitChangeTrait
public import WeilConjectures.TraceFormula.Specialization.TraitChangeSquare
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Change of trait for models finite over the trait

Let `k'` be a separably closed field, `S = Spec k'⟦t⟧`, `K` a separably closed extension of `k'`
and `S' = Spec K⟦t⟧`. Let `N` be a model of finite type over `S` whose structure morphism
`q : 𝒴 ⟶ S` is finite, `N'' = N ×_S S'` its change of trait, and `N_η̄`, `N''_η̄` the models of
their geometric generic fibres (`ε = 𝟙`, `NearbyCyclesModel.toGeneric`). The pullback exchange of
`φ : N''_η̄ ⟶ N_η̄` (`NearbyCyclesModel.traitChangeGenericHom`) is invertible at every bounded
constructible `A` whose nearby cycles are bounded constructible
(`NearbyCyclesModel.isIso_pullbackExchange_traitChangeGenericHom_app_of_isFinite`). This is the
finite case of the invariance of nearby cycles under change of trait (SGA 4½, [Th. finitude], §3;
`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap`), for the models of the geometric
generic fibres.

## Proof

Consider the commutative square of morphisms of models
```
N''_η̄ ──φ──▶ N_η̄
  │ψ''        │ψ
  ▼           ▼
 S'  ──τ───▶  S
```
where `ψ`, `ψ''` are the structure morphisms to the traits
(`NearbyCyclesModel.IsTraitModelOver.toTraitGeneric`) and `τ` is the morphism of traits
(`NearbyCyclesModel.traitGenericModelMap`). By the square law of the pushforward exchanges
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_square_of_isProper`),
```
Lσ_s^*(χ_ψ) ∘ bc_s ∘ Rq''_{s*}(α_φ) = α_τ(Rq_{η*}) ∘ Ψ_{S'}(bc_η) ∘ χ_{ψ''}.
```
* `χ_ψ`, `χ_{ψ''}` are the proper exchanges (blueprint `prose-E-03` (2),
  `NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`);
* `bc_s`, `bc_η` are the base change morphisms of the cartesian squares of special and of generic
  fibres, invertible by proper base change (blueprint
  `proposition-proper-direct-image-constructible-complexes`,
  `ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`);
* `α_τ` is the change of trait for the trait itself, invertible on bounded constructible complexes
  (`NearbyCyclesModel.isIso_pullbackExchange_traitGenericModelMap_app`), and `Rq_{η*}` preserves
  them (`boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj`).

So `Rq''_{s*}(α_φ)` is invertible, hence `α_φ` is, the pushforward along the finite morphism
`q''_s : N''_s ⟶ Spec K` to a separably closed point being conservative
(`ProEtale.CondensedRing.isIso_of_isIso_map_rightDerivedLowerStar_of_isFinite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

/-! ### The morphism of traits -/

section TraitMap

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The morphism of traits `S' = Spec K⟦t⟧ ⟶ S = Spec k'⟦t⟧`, as a morphism of the models of their
geometric generic points, over `Spec Ω_K ⟶ Spec Ω` and `Spec K ⟶ Spec k'`. -/
@[simps]
noncomputable def traitGenericModelMap :
    (traitGenericModel K).Hom (traitGenericModel k') (traitGenericPointMap k' K)
      (Spec.map (CommRingCat.ofHom (algebraMap k' K))) where
  total := traitMap k' K
  generic := traitGenericPointMap k' K
  comm_j := (traitGenericPoint_traitMap k' K).symm
  comm_i := (traitClosedPoint_traitMap k' K).symm
  comm_ε := by simp [traitGenericModel]

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed K]

/-- The pullback exchange of the morphism of traits `S' ⟶ S` is invertible at bounded
constructible complexes on `Spec Ω`: both specialization units are invertible, and such complexes
are finite direct sums of shifts of the unit. -/
theorem isIso_pullbackExchange_traitGenericModelMap_app
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (traitGenericField k'))))
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (Spec (.of (traitGenericField k')))))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of (traitGenericField k')))) B) :
    IsIso (((traitGenericModelMap k' K).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app
      B) := by
  have := isIso_unit_traitGenericModel (Profinite.padicAlgClRingObj ℓ) k'
  have := isIso_unit_traitGenericModel (Profinite.padicAlgClRingObj ℓ) K
  exact Hom.isIso_pullbackExchange_app_of_shiftDecomposition _ _
    (nonempty_shiftDecomposition_of_boundedConstructible ℓ (K := traitGenericField k') B hB)

end TraitMap

/-! ### The squares of the change of trait -/

section Squares

variable {k' : Type u} [Field k'] (K : Type u) [Field K] [Algebra k' K]
  {Y : Scheme.{u}} {Y' : Over (Spec (.of k'))} {N : NearbyCyclesModel Y Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}
  (hN : N.IsTraitModelOver q g)

/-- The change of trait `N'' = N ×_S S'` of a model of finite type over the trait. -/
noncomputable abbrev traitChange :=
  baseChange hN q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)

/-- The projection `N'' ⟶ N` of the change of trait. -/
noncomputable abbrev traitChangeHom :=
  baseChangeHom hN q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)

/-- The projection `N''_η̄ ⟶ N_η̄` of the models of the geometric generic fibres. -/
@[simps]
noncomputable def traitChangeGenericHom :
    (traitChange K hN).toGeneric.Hom N.toGeneric
      (baseChangeGenericMap hN q (Category.comp_id q) (traitMap k' K) (Category.comp_id _))
      (baseChangeSpecialMap hN q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)) where
  total := pullback.fst _ _
  generic := baseChangeGenericMap hN q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)
  comm_j := baseChangeGenericMap_j _ _ _ _ _
  comm_i := baseChangeSpecialMap_i _ _ _ _ _
  comm_ε := by simp

include hN in
/-- **The square of geometric generic fibres of the change of trait is cartesian**:
`N''_η̄ = N_η̄ ×_{Spec Ω} Spec Ω_K`. -/
lemma isPullback_baseChangeGenericMap_traitChange :
    IsPullback (baseChangeGenericMap hN q (Category.comp_id q) (traitMap k' K)
        (Category.comp_id _)) (pullback.snd _ _) g (traitGenericPointMap k' K) := by
  have hs := (IsPullback.of_hasPullback (pullback.snd q (traitMap k' K))
    (traitGenericPoint K)).paste_horiz (IsPullback.of_hasPullback q (traitMap k' K))
  have big : IsPullback (baseChangeGenericMap hN q (Category.comp_id q) (traitMap k' K)
      (Category.comp_id _) ≫ N.j) (pullback.snd _ _) q
        (traitGenericPointMap k' K ≫ traitGenericPoint k') := by
    rw [baseChangeGenericMap_j, ← traitGenericPoint_traitMap]
    exact hs
  exact IsPullback.of_right big (baseChangeGenericMap_g _ _ _ _ _) hN.isPullback_j

/-- The map of special fibres of the change of trait lies over `Spec K ⟶ Spec k'`. -/
@[reassoc]
lemma baseChangeSpecialMap_hom_traitChange :
    baseChangeSpecialMap hN q (Category.comp_id q) (traitMap k' K) (Category.comp_id _) ≫
      Y'.hom = (baseChangeSpecial q (traitMap k' K)).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k' K)) :=
  hN.isPullback_i.lift_snd _ _ _

include hN in
/-- **The square of special fibres of the change of trait is cartesian**:
`N''_s = N_s ×_{Spec k'} Spec K`. -/
lemma isPullback_baseChangeSpecialMap_traitChange :
    IsPullback (baseChangeSpecialMap hN q (Category.comp_id q) (traitMap k' K)
        (Category.comp_id _)) (baseChangeSpecial q (traitMap k' K)).hom Y'.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k' K))) := by
  have hs := (IsPullback.of_hasPullback (pullback.snd q (traitMap k' K))
    (traitClosedPoint K)).paste_horiz (IsPullback.of_hasPullback q (traitMap k' K))
  have big : IsPullback (baseChangeSpecialMap hN q (Category.comp_id q) (traitMap k' K)
      (Category.comp_id _) ≫ N.i) (baseChangeSpecial q (traitMap k' K)).hom q
        (Spec.map (CommRingCat.ofHom (algebraMap k' K)) ≫ traitClosedPoint k') := by
    rw [baseChangeSpecialMap_i, ← traitClosedPoint_traitMap]
    exact hs
  exact IsPullback.of_right big (baseChangeSpecialMap_hom_traitChange K hN) hN.isPullback_i

end Squares

/-! ### The finite case -/

section Finite

variable {k' : Type u} [Field k'] (K : Type u) [Field K] [Algebra k' K]
  {Y : Scheme.{u}} {Y' : Over (Spec (.of k'))} {N : NearbyCyclesModel Y Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}
  (hN : N.IsTraitModelOver q g)
  {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [IsSepClosed K]

set_option hygiene false in
/-- The condensed field `ℚ̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj ℓ

/-- **Change of trait for the model of the geometric generic fibre of a model finite over the
trait**: the pullback exchange of `N''_η̄ ⟶ N_η̄` is invertible at bounded constructible `A` whose
nearby cycles are bounded constructible, by the square argument
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_square_of_isProper`). -/
theorem isIso_pullbackExchange_traitChangeGenericHom_app_of_isFinite [IsFinite q]
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.generic))}
    (hA : boundedConstructible _ A)
    (hΨ : boundedConstructible _ ((N.toGeneric.nearbyCycles 𝐐).obj A)) :
    IsIso (((traitChangeGenericHom K hN).pullbackExchange 𝐐).app A) := by
  have hN'' := IsTraitModelOver.baseChange hN q (Category.comp_id q) (traitMap k' K)
    (Category.comp_id _)
  have : IsProper g := MorphismProperty.of_isPullback hN.isPullback_j inferInstance
  have : IsProper Y'.hom := MorphismProperty.of_isPullback hN.isPullback_i inferInstance
  have : IsFinite (pullback.snd q (traitMap k' K)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsProper (pullback.snd (pullback.snd q (traitMap k' K)) (traitGenericPoint K)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsFinite (baseChangeSpecial q (traitMap k' K)).hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hb : baseChangeGenericMap hN q (Category.comp_id q) (traitMap k' K) (Category.comp_id _) ≫
      g = pullback.snd _ _ ≫ traitGenericPointMap k' K := baseChangeGenericMap_g _ _ _ _ _
  have hs := baseChangeSpecialMap_hom_traitChange K hN
  have : IsIso (traitGenericModel k').ε :=
    inferInstanceAs (IsIso (𝟙 (Spec (.of (traitGenericField k')))))
  have : IsIso (traitGenericModel K).ε :=
    inferInstanceAs (IsIso (𝟙 (Spec (.of (traitGenericField K)))))
  -- the proper exchanges
  have hχ : IsIso ((hN.toTraitGeneric.pushforwardExchange 𝐐).app A) := by
    have : IsProper hN.toTraitGeneric.total := inferInstanceAs (IsProper q)
    exact hN.toTraitGeneric.isIso_pushforwardExchange_app_of_isProper
      (traitGenericPoint k' ≫ traitToBase k' k') ⟨_, ⟨hN.isTraitModel.exists_isPullback⟩⟩
      ⟨𝟙 _, isTraitModel_traitGenericModel k'⟩ hN.isPullback_i
      (IsPullback.of_horiz_isIso ⟨rfl⟩) hA
  -- proper base change on the special fibres
  have : Fact (ringChar K ≠ ℓ) := ⟨Algebra.ringChar_eq k' K ▸ Fact.out⟩
  have hbc' := isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ (𝟙 _) (𝟙 _)
    ⟨hs⟩ (isPullback_baseChangeSpecialMap_traitChange K hN) ((N.toGeneric.nearbyCycles 𝐐).obj A)
    hΨ
  -- the change of trait of the trait
  have hτ := isIso_pullbackExchange_traitGenericModelMap_app k' K (ℓ := ℓ)
    (boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj ℓ
      (𝟙 (Spec (.of (traitGenericField k')))) g A hA)
  have : IsProper hN''.toTraitGeneric.total :=
    inferInstanceAs (IsProper (pullback.snd q (traitMap k' K)))
  exact Hom.isIso_pullbackExchange_app_of_square_of_isProper ℓ
    (traitGenericPoint k' ≫ traitToBase k' k') (traitGenericPoint K ≫ traitToBase K K)
    (by exact ⟨_, ⟨hN''.isTraitModel.exists_isPullback⟩⟩) ⟨𝟙 _, isTraitModel_traitGenericModel K⟩
    (traitChangeGenericHom K hN) hN.toTraitGeneric hN''.toTraitGeneric (traitGenericModelMap k' K)
    (by simp [pullback.condition, -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase])
    (by simp [hb]) hb hs
    (isPullback_baseChangeGenericMap_traitChange K hN) hN''.isPullback_i
    (IsPullback.of_horiz_isIso ⟨rfl⟩) A hA hχ hbc' hτ
    fun a h ↦ isIso_of_isIso_map_rightDerivedLowerStar_of_isFinite 𝐐
      (baseChangeSpecial q (traitMap k' K)).hom a h

end Finite

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
