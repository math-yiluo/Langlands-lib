/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Morphisms of pro-étale module objects are determined locally

To construct the trace `g_* g^* ⟶ 𝟭` of a finite étale `g : Y ⟶ X` by descent from a cover over
which `g` splits, and to check that its composite with the unit is multiplication by the degree,
one needs that morphisms of module objects on `X_proét` are determined by their pullbacks along
a pro-étale covering family. This file proves this:

* `AlgebraicGeometry.ProEtale.hom_ext_of_localizationRestriction`: two morphisms of sheaves on
  `X_proét` whose restrictions along every member of a pro-étale covering family agree are equal;
* `AlgebraicGeometry.ProEtale.hom_ext_of_upperStar`: the same for the pullbacks `(g i)^*`;
* `AlgebraicGeometry.ProEtale.CondensedRing.hom_ext_of_upperStar`: the same for module objects
  over a condensed ring `Λ`, and its variant
  `AlgebraicGeometry.ProEtale.CondensedRing.natTrans_ext_of_upperStar` for natural
  transformations of functors with values in module objects.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

section Sheaf

variable (A : Type u') [Category.{u + 1} A] {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}}
  (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]

/-- **Morphisms of pro-étale sheaves are determined locally**: two morphisms of sheaves on
`X_proét` whose restrictions along every member of a pro-étale covering family `g i : W i ⟶ X`
agree are equal. At a weakly étale `X`-scheme `V`, the base changes `V ×_X W i` cover `V`, and
over them both morphisms are given by their restrictions along `g i`. -/
lemma hom_ext_of_localizationRestriction (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X)
    {G G' : Sheaf (ProEt.topology X) A} {φ ψ : G ⟶ G'}
    (h : ∀ i, (localizationRestriction A (g i) inferInstance).map φ =
      (localizationRestriction A (g i) inferInstance).map ψ) :
    φ = ψ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ?_))
  induction V using Opposite.rec with | op V => ?_
  refine G'.property.hom_ext_ofArrows _ (ProEt.ofArrows_baseChange_mem_topology V g hg)
    fun i ↦ ?_
  rw [← φ.hom.naturality, ← ψ.hom.naturality]
  congr 1
  -- the base change `V ×_X W i` is the image of the weakly étale `W i`-scheme
  -- `V ×_X W i ⟶ W i` under the localization functor along `g i`
  have hw : WeaklyEtale (pullback.snd V.hom (g i)) := inferInstance
  let e : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).obj
      (MorphismProperty.Over.mk ⊤ _ hw) ≅ ProEt.baseChange (g i) V :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp [ProEt.baseChange, pullback.condition])
  have key (χ : G ⟶ G') : χ.hom.app (op (ProEt.baseChange (g i) V)) =
      G.obj.map e.hom.op ≫ χ.hom.app (op _) ≫ G'.obj.map e.inv.op := by
    rw [χ.hom.naturality_assoc, ← G'.obj.map_comp, ← op_comp, e.inv_hom_id, op_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have := congrArg (fun χ ↦ χ.hom.app (op (MorphismProperty.Over.mk ⊤ _ hw))) (h i)
  simp only [localizationRestriction_map_hom_app] at this
  rw [key φ, key ψ, this]

end Sheaf

section UpperStar

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]

/-- Two morphisms of sheaves on `X_proét` whose pullbacks along every member of a pro-étale
covering family `g i : W i ⟶ X` agree are equal. -/
lemma hom_ext_of_upperStar (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X)
    {G G' : Sheaf (ProEt.topology X) A} {φ ψ : G ⟶ G'}
    (h : ∀ i, (g i)^*[A].map φ = (g i)^*[A].map ψ) :
    φ = ψ := by
  refine hom_ext_of_localizationRestriction A g hg fun i ↦ ?_
  have e := upperStarIsoLocalizationRestriction A (g i) inferInstance
  rw [← cancel_epi (e.hom.app G), ← e.hom.naturality, ← e.hom.naturality, h i]

end UpperStar

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]

/-- **Morphisms of pro-étale module objects are determined locally**: two morphisms of module
objects over `Λ_X` whose pullbacks along every member of a pro-étale covering family
`g i : W i ⟶ X` agree are equal. -/
lemma hom_ext_of_upperStar (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X)
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)} {φ ψ : M ⟶ N}
    (h : ∀ i, (g i)^*⟦Λ⟧.map φ = (g i)^*⟦Λ⟧.map ψ) :
    φ = ψ := by
  refine (Mod.forget (condensedRingObj Λ X)).map_injective
    (ProEtale.hom_ext_of_upperStar Ab.{u + 1} g hg fun i ↦ ?_)
  have hφ := (upperStarForgetIso Λ (g i)).hom.naturality φ
  have hψ := (upperStarForgetIso Λ (g i)).hom.naturality ψ
  dsimp only [Functor.comp_map] at hφ hψ
  rw [← cancel_mono ((upperStarForgetIso Λ (g i)).hom.app N), hφ, hψ, h i]

/-- Two natural transformations of functors with values in pro-étale module objects over `Λ_X`
agree as soon as their pullbacks along every member of a pro-étale covering family
`g i : W i ⟶ X` agree. -/
lemma natTrans_ext_of_upperStar (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X)
    {C : Type*} [Category C]
    {F G : C ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)} {α β : F ⟶ G}
    (h : ∀ i, Functor.whiskerRight α (g i)^*⟦Λ⟧ = Functor.whiskerRight β (g i)^*⟦Λ⟧) :
    α = β :=
  NatTrans.ext (funext fun c ↦ hom_ext_of_upperStar Λ g hg fun i ↦
    congrArg (fun χ ↦ χ.app c) (h i))

/-- Multiplication by an integer `d` on a pro-étale module object can be recognised locally:
an endomorphism whose pullbacks along every member of a pro-étale covering family are
multiplication by `d` is multiplication by `d`. This is the form in which the identity
`unit ≫ trace = d • 𝟙` of a finite étale cover of degree `d` is checked over a splitting cover. -/
lemma eq_nsmul_id_of_upperStar (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X)
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)} (φ : M ⟶ M) (d : ℕ)
    (h : ∀ i, (g i)^*⟦Λ⟧.map φ = d • 𝟙 _) :
    φ = d • 𝟙 M :=
  hom_ext_of_upperStar Λ g hg fun i ↦ by
    rw [h i, Functor.map_nsmul, CategoryTheory.Functor.map_id]

end CondensedRing

end AlgebraicGeometry.ProEtale
