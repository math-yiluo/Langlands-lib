/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples

/-!
# EtaleResidueTripleUnitRefinement

Source: Stacks Project, Algebra, Tags 04GN and 04GP.
(blueprint: lem-weil-pbc-etale-triple-unit-refinement).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tags 04GN and 04GP.

Proof: For an element f outside the prime q of a triple, form the principal localization B_f.
The map B → K extends to B_f because the image of f in K is nonzero and hence a unit.
Let q' be the kernel of this extension and extend the resulting injection B_f/q' → K
to its fraction field. This gives the residue-field embedding of the new triple.
The extended map agrees on R, so q' lies over p and the triple is compatible with χ.
Principal localization is etale, and composition with the given etale map is etale.
The localization map is a morphism of triples and takes f to a unit.
(blueprint: lem-weil-pbc-etale-triple-unit-refinement). -/
theorem etaleResidueTriple_unit_refinement
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (t : EtaleResidueTriples R p K χ) (f : t.B) (hf : f ∉ t.q.asIdeal) :
    ∃ (s : EtaleResidueTriples R p K χ) (a : t ⟶ s),
      IsUnit (((etaleResidueTriplesRingDiagram R p K χ).map a).hom f) := by
  classical
  let β := ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom
  have eval_zero (x : t.B) : β x = 0 ↔ x ∈ t.q.asIdeal := by
    change t.φ.hom (((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q).hom x) = 0 ↔ _
    rw [map_eq_zero]
    have hcanon := Spec.algebraMap_residueFieldIso_inv t.B t.q
    change CommRingCat.ofHom (algebraMap t.B t.q.asIdeal.ResidueField) ≫
      (Spec.residueFieldIso t.B t.q).inv =
        (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q at hcanon
    rw [← hcanon]
    change (Spec.residueFieldIso t.B t.q).inv.hom
      (algebraMap t.B t.q.asIdeal.ResidueField x) = 0 ↔ _
    rw [map_eq_zero]
    exact show x ∈ RingHom.ker (algebraMap t.B t.q.asIdeal.ResidueField) ↔
        x ∈ t.q.asIdeal by rw [Ideal.ker_algebraMap_residueField]
  have hu : IsUnit (β f) := IsUnit.mk0 _ (fun h ↦ hf ((eval_zero f).mp h))
  let L := Localization.Away f
  let B' : CommRingCat.{u} := CommRingCat.of L
  let ι : t.B ⟶ B' := CommRingCat.ofHom (algebraMap t.B L)
  let β' : L →+* K := IsLocalization.Away.lift f hu
  let q' : Spec B' := ⟨RingHom.ker β', RingHom.ker_isPrime β'⟩
  have : q'.asIdeal.IsPrime := q'.isPrime
  let φ' : (Spec B').residueField q' ⟶ CommRingCat.of K :=
    (Spec.residueFieldIso B' q').hom ≫ CommRingCat.ofHom
      (Ideal.ResidueField.lift q'.asIdeal β' le_rfl (by
        intro x hx
        exact IsUnit.mk0 _ hx))
  have hφ : (ΓSpecIso B').inv ≫ (Spec B').Γevaluation q' ≫ φ' =
      CommRingCat.ofHom β' := by
    dsimp only [φ']
    have hcanon := Spec.algebraMap_residueFieldIso_inv B' q'
    change CommRingCat.ofHom (algebraMap B' q'.asIdeal.ResidueField) ≫
      (Spec.residueFieldIso B' q').inv =
        (ΓSpecIso B').inv ≫ (Spec B').Γevaluation q' at hcanon
    rw [← Category.assoc, ← hcanon]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun x ↦ Ideal.ResidueField.lift_algebraMap q'.asIdeal β'
      le_rfl (by intro y hy; exact IsUnit.mk0 _ hy) x)
  have hq : Spec.map ι q' = t.q := by
    apply PrimeSpectrum.ext
    ext x
    change β' (algebraMap t.B L x) = 0 ↔ x ∈ t.q.asIdeal
    rw [IsLocalization.Away.lift_eq]
    exact eval_zero x
  let α' := t.α ≫ ι
  have hover : Spec.map α' q' = p := by
    rw [Spec.map_comp]
    change Spec.map t.α (Spec.map ι q') = p
    rw [hq, t.over]
  have hcompat : α' ≫ (ΓSpecIso B').inv ≫ (Spec B').Γevaluation q' ≫ φ' =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ := by
    rw [hφ]
    change t.α ≫ (ι ≫ CommRingCat.ofHom β') = _
    have hext : ι ≫ CommRingCat.ofHom β' = CommRingCat.ofHom β := by
      apply CommRingCat.hom_ext
      exact IsLocalization.Away.lift_comp f hu
    rw [hext]
    exact t.compatible
  have := t.etale
  have hetale : Etale (Spec.map α') := by
    rw [Spec.map_comp]
    infer_instance
  let s : EtaleResidueTriples R p K χ := ⟨B', α', hetale, q', hover, φ', hcompat⟩
  have hw : ι ≫ (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ =
      (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ := by
    change ι ≫ ((ΓSpecIso B').inv ≫ (Spec B').Γevaluation q' ≫ φ') = _
    rw [hφ]
    apply CommRingCat.hom_ext
    exact IsLocalization.Away.lift_comp f hu
  let a : t ⟶ s := ⟨Under.homMk (Over.homMk ι hw) (by rfl)⟩
  refine ⟨s, a, ?_⟩
  change IsUnit (algebraMap t.B L f)
  exact IsLocalization.Away.algebraMap_isUnit f

end AlgebraicGeometry.Scheme
