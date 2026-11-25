/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.StrictlyHenselianStalk

/-!
# Stalks as sections over a strictly henselian pro-étale neighbourhood

Let `g : Spec K ⟶ Y` be a geometric point of a scheme `Y`, `K` algebraically closed, and
`h : Spec A ⟶ Y` a weakly étale morphism from the spectrum of a strictly henselian local ring,
together with a lift `t` of `g` to `Spec A` through the closed point. Then `(Spec A, t)` is a
pro-étale neighbourhood of `g` through which every other one factors, and the germ map
`P(Spec A) ⟶ P_g` is bijective for every sheaf of modules `P` on `Y_proét`
(`AlgebraicGeometry.ProEtale.bijective_germ_of_weaklyEtale_of_isStrictlyHenselianLocalRing`).

Indeed every element of the stalk is the germ of a section over a neighbourhood `(V, t')`
(`AlgebraicGeometry.ProEtale.exists_germ_eq`), and the base change `V ×_Y Spec A ⟶ Spec A` is
weakly étale, so it has a section through the point given by `t` and `t'`
(`AlgebraicGeometry.Scheme.exists_section_comp_eq_of_weaklyEtale`, by Olivier's theorem): this is
a morphism of neighbourhoods `Spec A ⟶ V`. Similarly a section over `Spec A` with vanishing germ
vanishes on a neighbourhood `V' ⟶ Spec A`
(`AlgebraicGeometry.ProEtale.exists_map_eq_zero_of_germ_eq_zero`), which has a section.

This is the first step of the computation of boundary stalks of direct images as inertia
invariants (blueprint `lemma-boundary-stalk--1`): the stalk of `j_* F` at a geometric
point is the module of sections of `F` over the punctured strictly henselian neighbourhood.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type u} [CommRing A] [IsStrictlyHenselianLocalRing A] {K : Type u} [Field K]
  {Y : Scheme.{u}} (g : Spec (.of K) ⟶ Y) (h : Spec (.of A) ⟶ Y) [WeaklyEtale h]

/-- The strictly henselian pro-étale neighbourhood `(Spec A, t)` of a geometric point `g` maps to
every pro-étale neighbourhood `(V, t')` of `g`, compatibly with the points. -/
lemma exists_hom_of_isStrictlyHenselianLocalRing
    (t : ProEt.mk (𝟙 (Spec (.of K))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj (ProEt.mk h))
    (ht : (t.left ≫ pullback.fst h g) (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint A)
    {V : Y.ProEt}
    (t' : ProEt.mk (𝟙 (Spec (.of K))) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) :
    ∃ f : ProEt.mk h ⟶ V, t ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f = t' := by
  set c : Spec (.of K) ⟶ Spec (.of A) := t.left ≫ pullback.fst h g
  have ht₂ : t.left ≫ pullback.snd h g = 𝟙 _ := MorphismProperty.Over.w t
  have ht'₂ : t'.left ≫ pullback.snd V.hom g = 𝟙 _ := MorphismProperty.Over.w t'
  have hc : c ≫ h = g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht₂]
    exact Category.id_comp g
  have hy : (t'.left ≫ pullback.fst V.hom g) ≫ V.hom = c ≫ h := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht'₂, hc]
    exact Category.id_comp g
  -- the point of `V ×_Y Spec A` given by `t'` and `t`
  let y : Spec (.of K) ⟶ pullback V.hom h := pullback.lift _ _ hy
  obtain ⟨s, hs, hcs⟩ := exists_section_comp_eq_of_weaklyEtale (pullback.snd V.hom h) c ht y
    (pullback.lift_snd _ _ _)
  have hf : (s ≫ pullback.fst V.hom h) ≫ V.hom = h := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  refine ⟨MorphismProperty.Over.homMk (s ≫ pullback.fst V.hom h) hf, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change t.left ≫ pullback.lift (pullback.fst h g ≫ s ≫ pullback.fst V.hom h)
      (pullback.snd h g) _ ≫ pullback.fst V.hom g = _
    rw [pullback.lift_fst, ← Category.assoc, ← Category.assoc]
    change (c ≫ s) ≫ pullback.fst V.hom h = _
    rw [hcs, pullback.lift_fst]
  · change t.left ≫ pullback.lift (pullback.fst h g ≫ s ≫ pullback.fst V.hom h)
      (pullback.snd h g) _ ≫ pullback.snd V.hom g = _
    rw [pullback.lift_snd, ht₂, ht'₂]

variable [IsAlgClosed K] {R : Type (u + 1)} [Ring R]
  (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))

/-- **Stalks are sections over a strictly henselian neighbourhood.** Let `g : Spec K ⟶ Y` be a
geometric point, `h : Spec A ⟶ Y` weakly étale with `A` strictly henselian local and `t` a lift
of `g` to `Spec A` through the closed point. For every sheaf of modules `P` on `Y_proét` the germ
map `P(Spec A) ⟶ P_g = Γ(Spec K, g^* P)` is bijective. -/
theorem bijective_germ_of_weaklyEtale_of_isStrictlyHenselianLocalRing
    (t : ProEt.mk (𝟙 (Spec (.of K))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj (ProEt.mk h))
    (ht : (t.left ≫ pullback.fst h g) (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint A) :
    Function.Bijective (germ _ g P t) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun σ hσ ↦ ?_, fun a ↦ ?_⟩
  · obtain ⟨V', f, t', hft, hf⟩ := exists_map_eq_zero_of_germ_eq_zero g P t σ hσ
    -- `V' ⟶ Spec A` is weakly étale, so it has a section through the point
    have hy : (t'.left ≫ pullback.fst V'.hom g) ≫ f.left = t.left ≫ pullback.fst h g := by
      rw [← hft]
      change _ = t'.left ≫ (pullback.lift (pullback.fst V'.hom g ≫ f.left)
        (pullback.snd V'.hom g) _ ≫ pullback.fst h g)
      rw [pullback.lift_fst, Category.assoc]
    have : WeaklyEtale (f.left ≫ h) := by
      rw [show f.left ≫ h = V'.hom from MorphismProperty.Over.w f]
      infer_instance
    have : WeaklyEtale f.left := WeaklyEtale.of_comp f.left h
    obtain ⟨s, hs, -⟩ := exists_section_comp_eq_of_weaklyEtale f.left _ ht _ hy
    have hsV : s ≫ V'.hom = h := by
      rw [← MorphismProperty.Over.w f, ← Category.assoc, hs, Category.id_comp]
      rfl
    let ψ : ProEt.mk h ⟶ V' := MorphismProperty.Over.homMk s hsV
    have hψ : ψ ≫ f = 𝟙 _ := MorphismProperty.Over.Hom.ext hs
    have e := congrArg (fun φ ↦ P.obj.map φ.op σ) hψ
    simp only [op_comp, Functor.map_comp, op_id, CategoryTheory.Functor.map_id] at e
    rw [ConcreteCategory.comp_apply, hf, map_zero] at e
    simpa using e.symm
  · obtain ⟨V, t', σ, rfl⟩ := exists_germ_eq g P a
    obtain ⟨f, hf⟩ := exists_hom_of_isStrictlyHenselianLocalRing g h t ht t'
    refine ⟨P.obj.map f.op σ, ?_⟩
    rw [← ConcreteCategory.comp_apply, map_germ f t' t hf]

end AlgebraicGeometry.ProEtale
