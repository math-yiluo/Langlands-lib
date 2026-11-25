/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsGlobal

/-!
# Extension by zero preserves products

Let `X` be quasi-compact and quasi-separated and `j : U ⟶ X` a quasi-compact open immersion with
closed complement `i : Z ⟶ X`. The extension by zero `j_!` of pro-étale sheaves of modules preserves
products (`AlgebraicGeometry.ProEtale.isIso_piComparison_openImmersionLowerShriek`, part (3) of
blueprint `proposition-extension-zero-restriction-closed-subscheme`): the comparison map
`j_! ∏ Nₐ ⟶ ∏ j_! Nₐ` is an isomorphism after `j^*`, since `j^* j_! = 𝟭`, and after `i^*`, where
both sides vanish since `i^*` preserves products
(`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_of_isCompl`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

/-- `H.map (piComparison G f) ≫ piComparison H (G ∘ f) = piComparison (G ⋙ H) f`. -/
lemma _root_.CategoryTheory.Limits.map_piComparison_comp_piComparison {C D E : Type*}
    [Category* C] [Category* D] [Category* E] (G : C ⥤ D) (H : D ⥤ E) {β : Type*}
    [HasLimitsOfShape (Discrete β) C] [HasLimitsOfShape (Discrete β) D]
    [HasLimitsOfShape (Discrete β) E] (f : β → C) :
    H.map (piComparison G f) ≫ piComparison H (fun b ↦ G.obj (f b)) =
      piComparison (G ⋙ H) f := by
  refine Pi.hom_ext _ _ fun b ↦ ?_
  simp only [Category.assoc, piComparison_comp_π, ← H.map_comp]
  exact (piComparison_comp_π (G ⋙ H) f b).symm

variable {R : Type (u + 1)} [Ring R] {Z U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (3): let `X` be
quasi-compact and quasi-separated and `j : U ⟶ X` a quasi-compact open immersion with closed
complement `i`. The
extension by zero `j_!` of pro-étale sheaves of modules preserves products. -/
theorem isIso_piComparison_openImmersionLowerShriek
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) {β : Type (u + 1)}
    (N : β → Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) :
    IsIso (piComparison (j)_!open[ModuleCat.{u + 1} R] N) := by
  set c := piComparison (j)_!open[ModuleCat.{u + 1} R] N
  have : PreservesLimitsOfSize.{u + 1, u + 1} ((i)^*[ModuleCat.{u + 1} R]) :=
    preservesLimitsOfSize_upperStar_of_isCompl i j hij
  -- after `i^*` both sides vanish
  have hi : IsIso ((i)^*[ModuleCat.{u + 1} R].map c) := by
    have hz : ∀ b, IsZero ((i)^*[ModuleCat.{u + 1} R].obj
        ((j)_!open[ModuleCat.{u + 1} R].obj (N b))) := fun b ↦
      isZero_upperStar_openImmersionLowerShriek _ j i
        (Set.disjoint_iff_inter_eq_empty.1 hij.disjoint.symm) _
    have hsrc : IsZero ((i)^*[ModuleCat.{u + 1} R].obj
        ((j)_!open[ModuleCat.{u + 1} R].obj (∏ᶜ N))) :=
      isZero_upperStar_openImmersionLowerShriek _ j i
        (Set.disjoint_iff_inter_eq_empty.1 hij.disjoint.symm) _
    have hprod : IsZero (∏ᶜ fun b ↦ (i)^*[ModuleCat.{u + 1} R].obj
        ((j)_!open[ModuleCat.{u + 1} R].obj (N b))) := by
      rw [IsZero.iff_id_eq_zero]
      exact Pi.hom_ext _ _ fun b ↦ (hz b).eq_of_tgt _ _
    have htgt := hprod.of_iso
      (asIso (piComparison (i)^*[ModuleCat.{u + 1} R]
        (fun b ↦ (j)_!open[ModuleCat.{u + 1} R].obj (N b))))
    exact ⟨⟨0, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩⟩
  -- after `j^*` the comparison is that of `j_! ⋙ j^* ≅ 𝟭`
  have hj : IsIso ((j)^*[ModuleCat.{u + 1} R].map c) := by
    have : PreservesLimitsOfShape (Discrete β) ((j)^*[ModuleCat.{u + 1} R]) :=
      preservesLimitsOfShape_of_natIso (upperStarIsoOpenImmersionRestriction _ j).symm
    have : PreservesLimitsOfShape (Discrete β)
        ((j)_!open[ModuleCat.{u + 1} R] ⋙ (j)^*[ModuleCat.{u + 1} R]) :=
      preservesLimitsOfShape_of_natIso
        (asIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).unit)
    have h := map_piComparison_comp_piComparison (j)_!open[ModuleCat.{u + 1} R]
      (j)^*[ModuleCat.{u + 1} R] N
    have : IsIso ((j)^*[ModuleCat.{u + 1} R].map c ≫ piComparison (j)^*[ModuleCat.{u + 1} R]
        (fun b ↦ (j)_!open[ModuleCat.{u + 1} R].obj (N b))) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (piComparison (j)^*[ModuleCat.{u + 1} R]
      (fun b ↦ (j)_!open[ModuleCat.{u + 1} R].obj (N b)))
  exact isIso_of_isIso_upperStar_of_isCompl i j hij c

end ProEtale

end AlgebraicGeometry
