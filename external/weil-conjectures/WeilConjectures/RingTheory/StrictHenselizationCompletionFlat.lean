/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.FlatColimitRings
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import WeilConjectures.RingTheory.PointedEtaleCompletionStageFlat
import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Flatness of the completion of a strict henselization

Source: Stacks Project, More on Algebra, Lemma Tag 06LJ, proof of (c),
paragraph beginning “To finish the proof of (c)”
(blueprint: lem-sc-strict-henselization-completion-flat).
-/

@[expose] public section

universe v

namespace Algebra

/-- The maximal-ideal completion of a strict henselization is flat over the
strict henselization.
Source: Stacks Project, More on Algebra, Lemma Tag 06LJ, proof of (c)
(blueprint: lem-sc-strict-henselization-completion-flat).

Proof: Write the strict henselization as the filtered colimit of pointed étale
algebras from `lem-weil-pbc-strict-henselization-triples`. For each pointed
étale algebra, the map to the completed strict henselization is flat by the
per-triple completion-flatness assertion
`lem-sc-etale-triple-to-sh-completion-flat`. The composite maps are therefore
flat, and the filtered-colimit flatness lemma
`lem-weil-pbc-colimit-rings-flat` gives flatness of the canonical map from the
strict henselization to its completion. -/
theorem strictHenselization_completion_flat
    (R K C : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K] [CommRing C]
    [Algebra R C] (hC : IsStrictHenselization R K C) :
    (algebraMap C
      (AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R C)) C)).Flat := by
  classical
  let P : CategoryTheory.ObjectProperty (CategoryTheory.Over (CommAlgCat.of R K)) :=
    fun X ↦ Etale R X.left
  let D := P.ι.comp (CategoryTheory.Over.forget (CommAlgCat.of R K))
  obtain ⟨c, ⟨hc⟩, ⟨e⟩⟩ := hC
  let cC : CategoryTheory.Limits.Cocone D := c.extend e.hom
  have hcC : CategoryTheory.Limits.IsColimit cC := hc.extendIso e.hom
  obtain ⟨hsmall, hfiltered⟩ := pointedEtale_small_filtered R K
  let : CategoryTheory.EssentiallySmall.{v} P.FullSubcategory := hsmall
  let : CategoryTheory.IsFiltered P.FullSubcategory := hfiltered
  let s := CategoryTheory.equivSmallModel.{v} P.FullSubcategory
  let : CategoryTheory.IsFiltered (CategoryTheory.SmallModel.{v} P.FullSubcategory) :=
    CategoryTheory.IsFiltered.of_equivalence s
  let cs := cC.whisker s.inverse
  have hcs : CategoryTheory.Limits.IsColimit cs := hcC.whiskerEquivalence s.symm
  let U := CategoryTheory.forget₂ (CommAlgCat.{v} R) CommRingCat.{v}
  let F := (s.inverse.comp D).comp U
  let cr : CategoryTheory.Limits.Cocone F := U.mapCocone cs
  have hcr : CategoryTheory.Limits.IsColimit cr := by
    let E := commAlgCatEquivUnder (CommRingCat.of R)
    exact CategoryTheory.Limits.isColimitOfPreserves
      (E.functor.comp (CategoryTheory.Under.forget (CommRingCat.of R))) hcs
  let : CategoryTheory.Limits.HasColimit F := ⟨⟨cr, hcr⟩⟩
  let E := (hcr.coconePointUniqueUpToIso
    (CategoryTheory.Limits.colimit.isColimit F)).commRingCatIsoToRingEquiv
  let γ := algebraMap C
    (AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R C)) C)
  have hE : ∀ i, E.toRingHom.comp (cr.ι.app i).hom =
      (CategoryTheory.Limits.colimit.ι F i).hom := by
    intro i
    exact congrArg CommRingCat.Hom.hom
      (hcr.comp_coconePointUniqueUpToIso_hom (CategoryTheory.Limits.colimit.isColimit F) i)
  have hstage : ∀ i, (γ.comp (cr.ι.app i).hom).Flat := by
    intro i
    exact pointedEtale_completion_stage_flat R K cC hcC (s.inverse.obj i)
  have hψ : (γ.comp E.symm.toRingHom).Flat := by
    apply RingHom.flat_of_flat_comp_colimit_ι F
    intro i
    have he : E.symm.toRingHom.comp (CategoryTheory.Limits.colimit.ι F i).hom =
        (cr.ι.app i).hom := by
      rw [← hE i, ← RingHom.comp_assoc]
      simp
    rw [RingHom.comp_assoc, he]
    exact hstage i
  have h := (RingHom.Flat.of_bijective E.bijective).comp hψ
  have he : (γ.comp E.symm.toRingHom).comp E.toRingHom = γ := by
    apply RingHom.ext
    intro x
    exact congrArg γ (E.symm_apply_apply x)
  change γ.Flat
  exact he ▸ h

end Algebra
