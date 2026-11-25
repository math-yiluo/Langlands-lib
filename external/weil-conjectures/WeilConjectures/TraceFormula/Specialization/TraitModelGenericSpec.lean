/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitModelCompactification

/-!

# The generic fibre of a trait model over the base

Let `S = Spec k'⟦t⟧` be the trait, `Spec K ⟶ S` its generic point (`K = Frac k'⟦t⟧`) and
`Spec Ω ⟶ Spec K` the geometric generic point. For a `k`-scheme `X`, `X ×_k Spec Ω` is the base
change of `X ×_k Spec K` along the faithfully flat `Spec Ω ⟶ Spec K`
(`AlgebraicGeometry.isPullback_traitGenericBaseChangeMap`).

If `M` is a trait model of `X` over the base whose geometric generic fibre is all of
`X ×_k Spec Ω`, and `e : 𝒳 ⟶ X` factors the identification `ε`, then `(e, q)` identifies the
generic fibre `𝒳 ×_S Spec K` with `X ×_k Spec K`
(`NearbyCyclesModel.IsTraitModelOfBase.exists_isPullback_traitGenericSpec`):
this holds over `Spec Ω` and descends along `Spec Ω ⟶ Spec K` (Stacks 02L4). Consequently
morphisms into `𝒳` over `Spec K` are determined by their composites with `e`
(`NearbyCyclesModel.eq_of_isPullback_traitGenericSpec`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

section TraitGenericBaseChange

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The base change morphism `X ×_k Spec Ω ⟶ X ×_k Spec K` of a `k`-scheme `X` along the
geometric generic point `Spec Ω ⟶ Spec K` of the trait (`K = Frac k'⟦t⟧`). -/
noncomputable def traitGenericBaseChangeMap (X : Over (Spec (.of k))) :
    pullback X.hom (traitGenericPoint k' ≫ traitToBase k k') ⟶
      pullback X.hom (traitGenericSpec k' ≫ traitToBase k k') :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ traitGenericPointToSpec k') (by
    rw [pullback.condition, Category.assoc, traitGenericPointToSpec_traitGenericSpec_assoc])

@[reassoc (attr := simp)]
lemma traitGenericBaseChangeMap_fst (X : Over (Spec (.of k))) :
    traitGenericBaseChangeMap k' X ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma traitGenericBaseChangeMap_snd (X : Over (Spec (.of k))) :
    traitGenericBaseChangeMap k' X ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ traitGenericPointToSpec k' :=
  pullback.lift_snd _ _ _

/-- `X ×_k Spec Ω` is the base change of `X ×_k Spec K` along `Spec Ω ⟶ Spec K`. -/
lemma isPullback_traitGenericBaseChangeMap (X : Over (Spec (.of k))) :
    IsPullback (traitGenericBaseChangeMap k' X) (pullback.snd _ _) (pullback.snd _ _)
      (traitGenericPointToSpec k') := by
  refine IsPullback.of_right ?_ (traitGenericBaseChangeMap_snd k' X)
    (IsPullback.of_hasPullback _ _)
  rw [traitGenericBaseChangeMap_fst, traitGenericPointToSpec_traitGenericSpec_assoc]
  exact IsPullback.of_hasPullback _ _

/-- The base change `X ×_k Spec Ω ⟶ X ×_k Spec K` is surjective, flat and quasi-compact. -/
lemma traitGenericBaseChangeMap_mem (X : Over (Spec (.of k))) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (traitGenericBaseChangeMap k' X) :=
  MorphismProperty.of_isPullback (isPullback_traitGenericBaseChangeMap k' X).flip
    (traitGenericPointToSpec_mem k')

end TraitGenericBaseChange

namespace ProEtale.CondensedRing.NearbyCyclesModel

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- The identification `ε` of the geometric generic fibre of a trait model of `X` over the base
lies over the geometric generic point `Spec Ω ⟶ S ⟶ Spec k`. -/
lemma IsTraitModelOfBase.ε_hom {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))}
    {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (h : M.IsTraitModelOfBase k q g) :
    M.ε ≫ X.hom = g ≫ traitGenericPoint k' ≫ traitToBase k k' := by
  obtain ⟨u, -, hu₁, hu₂⟩ := h.exists_openImmersion
  rw [← hu₁, ← hu₂, Category.assoc, Category.assoc, pullback.condition]

/-- The geometric generic fibre of a model of finite type over the trait is the base change of
its generic fibre `𝒳 ×_S Spec K` along `Spec Ω ⟶ Spec K`. -/
lemma IsTraitModelOver.isPullback_traitGenericPointToSpec {X : Scheme.{u}}
    {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g) :
    IsPullback (pullback.lift M.j (g ≫ traitGenericPointToSpec k') (by
        rw [Category.assoc, traitGenericPointToSpec_traitGenericSpec, hM.isPullback_j.w]) :
        M.generic ⟶ pullback q (traitGenericSpec k'))
      g (pullback.snd _ _) (traitGenericPointToSpec k') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, traitGenericPointToSpec_traitGenericSpec]
  exact hM.isPullback_j

/-- The inclusion `𝒳_Ω ⟶ 𝒳 ×_S Spec K` of the geometric generic fibre of a model of finite type
over the trait in its generic fibre is an epimorphism (it is faithfully flat). -/
lemma IsTraitModelOver.epi_lift_traitGenericPointToSpec {X : Scheme.{u}}
    {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g) :
    Epi (pullback.lift M.j (g ≫ traitGenericPointToSpec k') (by
        rw [Category.assoc, traitGenericPointToSpec_traitGenericSpec, hM.isPullback_j.w]) :
        M.generic ⟶ pullback q (traitGenericSpec k')) := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := MorphismProperty.of_isPullback hM.isPullback_traitGenericPointToSpec.flip
    (traitGenericPointToSpec_mem k')
  exact Flat.epi_of_flat_of_surjective _

/-- **The generic fibre of a trait model over the base.** Let `M` be a trait model of `X` over
the base whose geometric generic fibre is all of `X ×_k Spec Ω`, and `e : 𝒳 ⟶ X` a factorisation
of `ε`. Then over the generic point `Spec K` of the trait (`K = Frac k'⟦t⟧`), `(e, q)` identifies
`𝒳 ×_S Spec K` with `X ×_k Spec K`: this is true over `Spec Ω`, and descends along the faithfully
flat `Spec Ω ⟶ Spec K` (Stacks 02L4). The inverse is given by `σ : X ×_k Spec K ⟶ 𝒳`, which
exhibits `X ×_k Spec K` as the base change of `q` along `Spec K ⟶ S`. -/
lemma IsTraitModelOfBase.exists_isPullback_traitGenericSpec {X : Over (Spec (.of k))}
    {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (h : M.IsTraitModelOfBase k q g)
    (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    {e : M.total ⟶ X.left} (he : M.j ≫ e = M.ε) (he' : e ≫ X.hom = q ≫ traitToBase k k') :
    ∃ σ : pullback X.hom (traitGenericSpec k' ≫ traitToBase k k') ⟶ M.total,
      σ ≫ e = pullback.fst _ _ ∧ IsPullback σ (pullback.snd _ _) q (traitGenericSpec k') := by
  have hM := h.isTraitModelOver
  let E : pullback q (traitGenericSpec k') ⟶
      pullback X.hom (traitGenericSpec k' ≫ traitToBase k k') :=
    pullback.lift (pullback.fst _ _ ≫ e) (pullback.snd _ _) (by
      rw [Category.assoc, he', pullback.condition_assoc])
  have hEfst : E ≫ pullback.fst _ _ = pullback.fst _ _ ≫ e := pullback.lift_fst _ _ _
  have hEsnd : E ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hP : IsPullback (pullback.lift M.j (g ≫ traitGenericPointToSpec k') (by
        rw [Category.assoc, traitGenericPointToSpec_traitGenericSpec, hM.isPullback_j.w]) :
        M.generic ⟶ pullback q (traitGenericSpec k'))
      hgen.isoPullback.hom E (traitGenericBaseChangeMap k' X) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_traitGenericBaseChangeMap k' X)
    · rw [IsPullback.isoPullback_hom_snd, hEsnd]
      exact hM.isPullback_traitGenericPointToSpec
    · apply pullback.hom_ext
      · rw [Category.assoc, hEfst, pullback.lift_fst_assoc, he, Category.assoc,
          traitGenericBaseChangeMap_fst, IsPullback.isoPullback_hom_fst]
      · rw [Category.assoc, hEsnd, pullback.lift_snd, Category.assoc,
          traitGenericBaseChangeMap_snd, IsPullback.isoPullback_hom_snd_assoc]
  have : IsIso E :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms _)
      hP.flip (traitGenericBaseChangeMap_mem k' X) (inferInstanceAs (IsIso _))
  refine ⟨inv E ≫ pullback.fst _ _, by rw [Category.assoc, ← hEfst, IsIso.inv_hom_id_assoc], ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (inv E)) rfl ?_
  · rw [Category.assoc, pullback.condition, ← hEsnd, Category.assoc, IsIso.inv_hom_id_assoc]
  · rw [asIso_hom, ← hEsnd, IsIso.inv_hom_id_assoc]

/-- Two morphisms to the total space `𝒳` of a model over the generic point `Spec K` of the trait
agree as soon as their composites with `e : 𝒳 ⟶ X` agree, when `X ×_k Spec K` is the generic
fibre of `𝒳` (`NearbyCyclesModel.IsTraitModelOfBase.exists_isPullback_traitGenericSpec`). -/
lemma eq_of_isPullback_traitGenericSpec {X : Over (Spec (.of k))} {Z T : Scheme.{u}}
    {q : Z ⟶ trait k'} {e : Z ⟶ X.left}
    {σ : pullback X.hom (traitGenericSpec k' ≫ traitToBase k k') ⟶ Z}
    (hσe : σ ≫ e = pullback.fst _ _)
    (hσ : IsPullback σ (pullback.snd _ _) q (traitGenericSpec k')) {f₁ f₂ : T ⟶ Z}
    {t : T ⟶ Spec (.of (FractionRing (PowerSeries k')))} (h₁ : f₁ ≫ q = t ≫ traitGenericSpec k')
    (h₂ : f₂ ≫ q = t ≫ traitGenericSpec k') (he : f₁ ≫ e = f₂ ≫ e) : f₁ = f₂ := by
  rw [← hσ.lift_fst f₁ t h₁, ← hσ.lift_fst f₂ t h₂]
  congr 1
  apply pullback.hom_ext
  · rw [← hσe, ← Category.assoc, ← Category.assoc, hσ.lift_fst, hσ.lift_fst, he]
  · rw [hσ.lift_snd, hσ.lift_snd]

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry

