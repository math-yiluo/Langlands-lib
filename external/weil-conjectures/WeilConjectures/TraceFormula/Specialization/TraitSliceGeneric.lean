/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BaseChangePaste
public import WeilConjectures.TraceFormula.Specialization.TraitSlice

/-!

# The square of generic fibres of the slice

Let `M''` be the slice model of a model `M` over `S = Spec k'⟦t⟧` along the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`NearbyCyclesModel.sliceModel`), with geometric generic fibre
`𝒳'' ×_{Spec K⟦t⟧} E` over a scheme `E` mapping to `Spec K⟦t⟧` and to `Spec Ω`. The pullback
exchange of the slice is invertible as soon as the base change morphism of the square of generic
fibres
```
𝒳'' ×_{Spec K⟦t⟧} E ---> 𝒳_η̄
        |                 |
        v                 v
       𝒳''  ------------> 𝒳
```
is (`NearbyCyclesModel.isIso_pullbackExchange_sliceHom`). This file splits that square.

* It factors through the cartesian square of `j : 𝒳_η̄ ⟶ 𝒳` along `𝒳'' ⟶ 𝒳`, with corner
  `𝒳'' ×_𝒳 𝒳_η̄ = 𝒳'' ×_S Spec Ω` (`NearbyCyclesModel.sliceGenericBase`), followed by the
  comparison `𝒳'' ×_{Spec K⟦t⟧} E ⟶ 𝒳'' ×_𝒳 𝒳_η̄` (`NearbyCyclesModel.sliceGenericToBase`) over
  `𝒳''`. The base change morphism of the generic fibres is invertible when those of the cartesian
  square and of the comparison square are
  (`NearbyCyclesModel.isIso_baseChangeMap_sliceHom`).
* If `E = Spec K⟦t⟧ ×_S Spec Ω`, i.e. the square of `γ : E ⟶ Spec K⟦t⟧` and `δ : E ⟶ Spec Ω` over
  `S` is cartesian, then the square of generic fibres itself is cartesian
  (`NearbyCyclesModel.isPullback_sliceHom_j`), and the comparison is an isomorphism.

In the cartesian case, the slice identification is therefore exactly base change of `Rj_*` along
the morphism `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ 𝒳`, a base change of the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S`. Since `σ` factors through the completion of a strict localization, it is
not weakly étale, and weakly étale base change
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`) does not apply to it.

## Main statements

* `ProEtale.CondensedRing.isIso_baseChangeMap_congr`: the base change morphisms of two squares
  with equal sides are simultaneously invertible.
* `NearbyCyclesModel.isIso_baseChangeMap_sliceHom`: reduction of the base change morphism of
  the generic fibres to those of the cartesian square and of the comparison square.
* `NearbyCyclesModel.isIso_pullbackExchange_sliceHom_of_isPullback`: in the cartesian case, the
  pullback exchange of the slice is invertible given base change along `𝒳'' ⟶ 𝒳`.
* `NearbyCyclesModel.isPullback_sliceHom_j`: the square of generic fibres is cartesian when `E` is
  the fibre product `Spec K⟦t⟧ ×_S Spec Ω`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Congr

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The base change morphisms of two commutative squares with the same vertical maps and equal
horizontal maps are simultaneously invertible. -/
lemma isIso_baseChangeMap_congr {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {g₁ g₂ : Y' ⟶ Y} {g₁' g₂' : X' ⟶ X} (sq₁ : CommSq g₁' p' p g₁) (sq₂ : CommSq g₂' p' p g₂)
    (e : g₁ = g₂) (e' : g₁' = g₂') :
    IsIso (baseChangeMap Λ sq₁) ↔ IsIso (baseChangeMap Λ sq₂) := by
  subst e e'
  rfl

end Congr

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] (x : K)
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  {E : Scheme.{u}} {γ : E ⟶ trait K} {δ : E ⟶ Spec (.of (traitGenericField k'))}
  (hγδ : γ ≫ traitMap k' K = δ ≫ traitGenericPoint k')

/-! ### The cartesian square of `j` along the slice -/

variable (M) (b) in
/-- The base change `𝒳'' ×_𝒳 𝒳_η̄` of the geometric generic fibre `j : 𝒳_η̄ ⟶ 𝒳` along the
projection `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ 𝒳` of the slice. -/
noncomputable abbrev sliceGenericBase : Scheme.{u} :=
  pullback M.j (pullback.fst b (traitSlice x))

variable (M) (b) in
/-- The square of `j : 𝒳_η̄ ⟶ 𝒳` along `𝒳'' ⟶ 𝒳` is cartesian. -/
lemma isPullback_sliceGenericBase :
    IsPullback (pullback.fst M.j (pullback.fst b (traitSlice x)))
      (pullback.snd M.j (pullback.fst b (traitSlice x))) M.j (pullback.fst b (traitSlice x)) :=
  IsPullback.of_hasPullback _ _

/-- The comparison `𝒳'' ×_{Spec K⟦t⟧} E ⟶ 𝒳'' ×_𝒳 𝒳_η̄` over `𝒳''` from the geometric generic
fibre of the slice model to the base change of the geometric generic fibre of `M`. -/
noncomputable def sliceGenericToBase : sliceGeneric x b γ ⟶ sliceGenericBase x M b :=
  pullback.lift (sliceGenericMap x hM hb hγδ) (pullback.fst _ _)
    (hM.isPullback_j.lift_fst _ _ _)

@[reassoc (attr := simp)]
lemma sliceGenericToBase_fst :
    sliceGenericToBase x hM hb hγδ ≫ pullback.fst _ _ = sliceGenericMap x hM hb hγδ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sliceGenericToBase_snd :
    sliceGenericToBase x hM hb hγδ ≫ pullback.snd _ _ = pullback.fst _ _ :=
  pullback.lift_snd _ _ _

/-- The comparison square: the comparison `𝒳'' ×_{Spec K⟦t⟧} E ⟶ 𝒳'' ×_𝒳 𝒳_η̄` lies over the
identity of `𝒳''`. -/
lemma commSq_sliceGenericToBase :
    CommSq (sliceGenericToBase x hM hb hγδ) (sliceModel x hM hb hγδ).j
      (pullback.snd M.j (pullback.fst b (traitSlice x))) (𝟙 _) :=
  ⟨by rw [sliceGenericToBase_snd, Category.comp_id]; rfl⟩

/-- The square of generic fibres of the slice as the pasting of the comparison square and the
cartesian square `isPullback_sliceGenericBase`. -/
lemma commSq_sliceGenericToBase_comp :
    CommSq (sliceGenericToBase x hM hb hγδ ≫ pullback.fst M.j (pullback.fst b (traitSlice x)))
      (sliceModel x hM hb hγδ).j M.j (𝟙 _ ≫ pullback.fst b (traitSlice x)) :=
  (commSq_sliceGenericToBase x hM hb hγδ).horiz_comp
    (isPullback_sliceGenericBase x M b).toCommSq

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Reduction of the generic base change of the slice to the comparison square**: if base
change of `Rj_*` along `𝒳'' ⟶ 𝒳` holds (the base change morphism of the cartesian square
`isPullback_sliceGenericBase` is invertible) and the base change morphism of the comparison square
`𝒳'' ×_{Spec K⟦t⟧} E ⟶ 𝒳'' ×_𝒳 𝒳_η̄` over `𝒳''` is invertible, then the base change morphism of
the square of geometric generic fibres of the slice is invertible. By
`ProEtale.CondensedRing.isIso_baseChangeMap_paste_iff`, given the first hypothesis, the second
one is only needed on the pullbacks of complexes on `𝒳_η̄`, and is then also necessary. -/
theorem isIso_baseChangeMap_sliceHom
    [IsIso (baseChangeMap Λ (isPullback_sliceGenericBase x M b).toCommSq)]
    [IsIso (baseChangeMap Λ (commSq_sliceGenericToBase x hM hb hγδ))] :
    IsIso (baseChangeMap Λ (sliceHom x hM hb hγδ).commSq_j) :=
  (isIso_baseChangeMap_congr Λ _ (commSq_sliceGenericToBase_comp x hM hb hγδ)
    (Category.id_comp _).symm (sliceGenericToBase_fst x hM hb hγδ).symm).mpr
    (isIso_baseChangeMap_paste Λ (isPullback_sliceGenericBase x M b).toCommSq
      (commSq_sliceGenericToBase x hM hb hγδ) (commSq_sliceGenericToBase_comp x hM hb hγδ))

/-! ### The cartesian case -/

include hb in
/-- **The square of generic fibres of the slice is cartesian** when `E` is the fibre product
`Spec K⟦t⟧ ×_S Spec Ω`: then `𝒳'' ×_{Spec K⟦t⟧} E = 𝒳'' ×_𝒳 𝒳_η̄`. -/
lemma isPullback_sliceHom_j (hE : IsPullback γ δ (traitMap k' K) (traitGenericPoint k')) :
    IsPullback (sliceHom x hM hb hγδ).generic (sliceModel x hM hb hγδ).j M.j
      (sliceHom x hM hb hγδ).total := by
  have hs := (IsPullback.of_hasPullback (pullback.snd b (traitSlice x)) γ).flip.paste_horiz
    hE.flip
  have e : (sliceHom x hM hb hγδ).generic ≫ g = pullback.snd _ _ ≫ δ :=
    hM.isPullback_j.lift_snd _ _ _
  rw [← e, ← pullback_fst_comp_eq_snd_traitMap x hb] at hs
  exact IsPullback.of_right hs (sliceHom x hM hb hγδ).comm_j hM.isPullback_j.flip

/-- In the cartesian case, the comparison `𝒳'' ×_{Spec K⟦t⟧} E ⟶ 𝒳'' ×_𝒳 𝒳_η̄` is an
isomorphism. -/
lemma isIso_sliceGenericToBase (hE : IsPullback γ δ (traitMap k' K) (traitGenericPoint k')) :
    IsIso (sliceGenericToBase x hM hb hγδ) := by
  have h := isPullback_sliceHom_j x hM hb hγδ hE
  have : sliceGenericToBase x hM hb hγδ = h.isoPullback.hom := by
    ext <;> simp [sliceHom, sliceModel]
  rw [this]
  infer_instance

/-- **Reduction of the slice identification in the cartesian case**: if `E` is the fibre product
`Spec K⟦t⟧ ×_S Spec Ω`, the pullback exchange of the slice is invertible as soon as base change of
`Rj_*` along `𝒳'' ⟶ 𝒳` holds: the comparison square is then a cartesian square with invertible
horizontal maps, whose base change morphism is invertible by weakly étale base change. -/
theorem isIso_pullbackExchange_sliceHom_of_isPullback
    (hE : IsPullback γ δ (traitMap k' K) (traitGenericPoint k'))
    [IsIso (baseChangeMap Λ (isPullback_sliceGenericBase x M b).toCommSq)] :
    IsIso ((sliceHom x hM hb hγδ).pullbackExchange Λ) := by
  have := isIso_sliceGenericToBase x hM hb hγδ hE
  have h₂ : IsPullback (sliceGenericToBase x hM hb hγδ) (sliceModel x hM hb hγδ).j
      (pullback.snd M.j (pullback.fst b (traitSlice x))) (𝟙 _) :=
    IsPullback.of_horiz_isIso (commSq_sliceGenericToBase x hM hb hγδ)
  have : WeaklyEtale (sliceGenericToBase x hM hb hγδ) := MorphismProperty.of_isIso _ _
  have : WeaklyEtale (𝟙 (pullback b (traitSlice x))) := MorphismProperty.of_isIso _ _
  have : IsIso (baseChangeMap Λ (commSq_sliceGenericToBase x hM hb hγδ)) :=
    isIso_baseChangeMap_of_weaklyEtale Λ h₂
  have : IsIso (baseChangeMap Λ (sliceHom x hM hb hγδ).commSq_j) :=
    isIso_baseChangeMap_sliceHom x hM hb hγδ Λ
  exact isIso_pullbackExchange_sliceHom x hM hb hγδ Λ

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
