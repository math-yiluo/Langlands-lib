/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat

import WeilConjectures.RingTheory.StrictHenselizationCompletionFlatOverBase
import Mathlib.RingTheory.Unramified.Finite
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import WeilConjectures.RingTheory.FlatColimitRings
import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Flatness from a pointed etale stage to the strict henselization completion

Source: Stacks Project, More on Algebra, Tag 06LJ, proof of (c).
(blueprint: lem-sc-pointed-etale-completion-stage-flat).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Every coprojection of the pointed etale algebra presentation becomes flat
when followed by completion at the extended maximal ideal.
Source: Stacks Project, More on Algebra, Tag 06LJ, proof of (c), paragraph
beginning “To finish the proof of (c)”.
(blueprint: lem-sc-pointed-etale-completion-stage-flat).

Proof: The given colimit cocone, with the identity isomorphism on its vertex,
is a strict henselization in the pointed-algebra definition. Apply
`strictHenselization_completion_flat_over_base` to make its completion flat over `R`.
The coprojection followed by completion is an `R`-algebra map from the etale stage `S`.
Use this map for the `S`-action on the completion; its algebra-map compatibility gives
an `R`-`S` scalar tower. An etale algebra is formally unramified and of finite type,
so Mathlib's `FormallyUnramified.flat_of_restrictScalars` makes the completion flat
as an `S`-module. By the definition of flat ring maps, this is the required flatness. -/
theorem pointedEtale_completion_stage_flat
    (R K : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K]
    (c : Cocone ((ObjectProperty.ι
      (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)) ⋙
        Over.forget (CommAlgCat.of R K)))
    (hc : IsColimit c)
    (t : ObjectProperty.FullSubcategory
      (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)) :
    ((algebraMap c.pt
      (AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R c.pt)) c.pt)).comp
        (c.ι.app t).hom.toRingHom).Flat := by
  let C := c.pt
  let S := t.obj.left
  let B := AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R C)) C
  have hC : IsStrictHenselization R K C := ⟨c, ⟨hc⟩, ⟨Iso.refl _⟩⟩
  have hflat := strictHenselization_completion_flat_over_base R K C hC
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.mp hflat
  have : Etale R S := t.property
  let f : S →ₐ[R] B := (IsScalarTower.toAlgHom R C B).comp (c.ι.app t).hom
  let : Algebra S B := f.toRingHom.toAlgebra
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  change f.toRingHom.Flat
  rw [RingHom.Flat]
  exact FormallyUnramified.flat_of_restrictScalars R S B

/-- The two flat factors in the pointed etale completion map.
Source: Stacks Project, More on Algebra, Tag 06LJ, proof of (c).
(blueprint: new-pointed-etale-completion-stage-flat-factors). -/
theorem pointedEtale_completion_stage_flat_factors
    (R K : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K]
    (c : Cocone ((ObjectProperty.ι
      (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)) ⋙
        Over.forget (CommAlgCat.of R K)))
    (hc : IsColimit c)
    (t : ObjectProperty.FullSubcategory
      (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)) :
    (c.ι.app t).hom.toRingHom.Flat ∧
      (algebraMap c.pt
        (AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R c.pt)) c.pt)).Flat := by
  classical
  let C := c.pt
  have hC : IsStrictHenselization R K C := ⟨c, ⟨hc⟩, ⟨Iso.refl _⟩⟩
  constructor
  · obtain ⟨p, hp, a, hsep, ι, ⟨hc'⟩, hι⟩ := hC.triples_presentation R K C
    let := a
    have := hsep
    have hflat := AlgebraicGeometry.Scheme.strictHenselization_faithfullyFlat
      (CommRingCat.of R) p hp K _ hc' (CommRingCat.ofHom (algebraMap R C)) hι
    have : Module.Flat R C := RingHom.flat_algebraMap_iff.mp hflat.flat
    let S := t.obj.left
    have : Etale R S := t.property
    let f : S →ₐ[R] C := (c.ι.app t).hom
    let : Algebra S C := f.toRingHom.toAlgebra
    have : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
    change f.toRingHom.Flat
    rw [RingHom.Flat]
    exact FormallyUnramified.flat_of_restrictScalars R S C
  · let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
    let D := P.ι.comp (Over.forget (CommAlgCat.of R K))
    obtain ⟨hsmall, hfiltered⟩ := pointedEtale_small_filtered R K
    let : EssentiallySmall.{u} P.FullSubcategory := hsmall
    let : IsFiltered P.FullSubcategory := hfiltered
    let s := equivSmallModel.{u} P.FullSubcategory
    let : IsFiltered (SmallModel.{u} P.FullSubcategory) := IsFiltered.of_equivalence s
    let cs := c.whisker s.inverse
    have hcs : IsColimit cs := hc.whiskerEquivalence s.symm
    let U := forget₂ (CommAlgCat.{u} R) CommRingCat.{u}
    let F := (s.inverse.comp D).comp U
    let cr : Cocone F := U.mapCocone cs
    have hcr : IsColimit cr := by
      let E := commAlgCatEquivUnder (CommRingCat.of R)
      exact isColimitOfPreserves (E.functor.comp (Under.forget (CommRingCat.of R))) hcs
    let : HasColimit F := ⟨⟨cr, hcr⟩⟩
    let E := (hcr.coconePointUniqueUpToIso
      (colimit.isColimit F)).commRingCatIsoToRingEquiv
    let γ := algebraMap C
      (AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R C)) C)
    have hE : ∀ i, E.toRingHom.comp (cr.ι.app i).hom = (colimit.ι F i).hom := by
      intro i
      exact congrArg CommRingCat.Hom.hom
        (hcr.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) i)
    have hstage : ∀ i, (γ.comp (cr.ι.app i).hom).Flat := by
      intro i
      exact pointedEtale_completion_stage_flat R K c hc (s.inverse.obj i)
    have hψ : (γ.comp E.symm.toRingHom).Flat := by
      apply RingHom.flat_of_flat_comp_colimit_ι F
      intro i
      have he : E.symm.toRingHom.comp (colimit.ι F i).hom = (cr.ι.app i).hom := by
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
