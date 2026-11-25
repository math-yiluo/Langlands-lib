/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict

/-!

# The standard model of a scheme over the trait, and closed embeddings of models

For a morphism `q : T ⟶ S` to the trait `S = Spec k'⟦t⟧`, the *standard model*
`NearbyCyclesModel.traitStdModel q` of `T` has total space `T`, geometric generic fibre
`T ×_S η̄` and special fibre `T ×_S s` (`NearbyCyclesModel.traitStdSpecialFibre q`), with the
first projections as inclusions and `ε = j`; it is a model of finite type over the trait when `q`
is (`NearbyCyclesModel.isTraitModel_traitStdModel`).

A morphism `c : 𝒳 ⟶ T` over `S` from the total space of a model `M` of finite type over the trait
induces a morphism of models `M.geometric ⟶ (traitStdModel q).geometric`
(`NearbyCyclesModel.traitStdHom`), whose squares of geometric generic fibres and of special fibres
are cartesian (`NearbyCyclesModel.isPullback_traitStdHom_generic`,
`NearbyCyclesModel.isPullback_traitStdHom_special`). This is used with a closed immersion of an
affine total space into an affine space `𝔸ⁿ_S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {T : Scheme.{u}} (q : T ⟶ trait k')

/-- The special fibre `T ×_S s` of a scheme `q : T ⟶ S` over the trait, as a scheme over `k'`. -/
noncomputable def traitStdSpecialFibre : Over (Spec (.of k')) :=
  Over.mk (pullback.snd q (traitClosedPoint k'))

/-- The *standard model* of a scheme `q : T ⟶ S` over the trait: total space `T`, geometric
generic fibre `T ×_S η̄`, special fibre `T ×_S s`, with the first projections as inclusions and
the identification `ε = j`. -/
@[simps]
noncomputable def traitStdModel : NearbyCyclesModel T (traitStdSpecialFibre q).left where
  total := T
  generic := pullback q (traitGenericPoint k')
  j := pullback.fst q (traitGenericPoint k')
  i := pullback.fst q (traitClosedPoint k')
  ε := pullback.fst q (traitGenericPoint k')

/-- The standard model of a scheme separated and of finite type over the trait is a model of
finite type over the trait. -/
lemma isTraitModel_traitStdModel [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q] :
    (traitStdModel q).IsTraitModel :=
  ⟨⟨q, pullback.snd q (traitGenericPoint k'), inferInstance, inferInstance, inferInstance,
    IsPullback.of_hasPullback _ _, IsPullback.of_hasPullback _ _⟩⟩

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {qM : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hj : IsPullback M.j g qM (traitGenericPoint k'))
  (hi : IsPullback M.i X'.hom qM (traitClosedPoint k')) (c : M.total ⟶ T) (hc : c ≫ q = qM)

include hj hc in
/-- The square inducing the morphism `𝒳_η̄ ⟶ T ×_S η̄` of geometric generic fibres commutes. -/
lemma traitStdHom_generic_w : (M.j ≫ c) ≫ q = g ≫ traitGenericPoint k' := by
  rw [Category.assoc, hc, hj.w]

include hi hc in
/-- The square inducing the morphism `X' ⟶ T ×_S s` of special fibres commutes. -/
lemma traitStdHom_special_w : (M.i ≫ c) ≫ q = X'.hom ≫ traitClosedPoint k' := by
  rw [Category.assoc, hc, hi.w]

/-- The morphism of special fibres `X' ⟶ T ×_S s` induced by `c`. -/
noncomputable def traitStdSpecialHom : X'.left ⟶ (traitStdSpecialFibre q).left :=
  pullback.lift (M.i ≫ c) X'.hom (traitStdHom_special_w q hi c hc)

/-- The morphism of geometric models `M.geometric ⟶ (traitStdModel q).geometric` induced by a
morphism `c : 𝒳 ⟶ T` over the trait. -/
@[simps]
noncomputable def traitStdHom :
    M.geometric.Hom (traitStdModel q).geometric c (traitStdSpecialHom q hi c hc) where
  total := c
  generic := pullback.lift (M.j ≫ c) g (traitStdHom_generic_w q hj c hc)
  comm_j := pullback.lift_fst _ _ _
  comm_i := pullback.lift_fst _ _ _
  comm_ε := pullback.lift_fst _ _ _

/-- The square of geometric generic fibres of `traitStdHom` is cartesian. -/
lemma isPullback_traitStdHom_generic :
    IsPullback (traitStdHom q hj hi c hc).generic M.j (traitStdModel q).j c := by
  refine IsPullback.of_right (h₁₂ := pullback.snd q (traitGenericPoint k'))
    (v₁₃ := traitGenericPoint k') (h₂₂ := q) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback q (traitGenericPoint k')).flip
  simp only [traitStdHom_generic, pullback.lift_snd, hc]
  exact hj.flip

/-- The square of special fibres of `traitStdHom` is cartesian. -/
lemma isPullback_traitStdHom_special :
    IsPullback M.i (traitStdSpecialHom q hi c hc) c (traitStdModel q).i := by
  refine (IsPullback.of_right (h₁₂ := pullback.snd q (traitClosedPoint k'))
    (v₁₃ := traitClosedPoint k') (h₂₂ := q) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback q (traitClosedPoint k')).flip).flip
  simp only [pullback.lift_snd, hc]
  exact hi.flip

/-- The morphism of special fibres induced by a closed immersion is a closed immersion. -/
lemma isClosedImmersion_traitStdSpecialHom [IsClosedImmersion c] :
    IsClosedImmersion (traitStdSpecialHom q hi c hc) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_traitStdHom_special q hi c hc) ‹_›

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
