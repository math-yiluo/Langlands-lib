/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.RingTheory.EtaleResidueTripleUnitRefinement
import WeilConjectures.RingTheory.EtaleResidueTripleIdealRefinement
import WeilConjectures.RingTheory.EtaleResidueTriplesRepresentatives

/-!
# Localization properties of the pointed etale colimit

Source: Stacks Project, Algebra, Tag 04GN (lemma-henselization), second and third
paragraphs of its proof, applied to triples as in Tag 04GP (lemma-strict-henselization).
(blueprint: lem-weil-pbc-etale-triples-colimit-localization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tag 04GN (lemma-henselization), second and third
paragraphs of its proof, applied to triples as in Tag 04GP (lemma-strict-henselization).

Proof: Every colimit element x is represented by f at a triple (S,q,φ). If ψ(x) ≠ 0,
then f is outside q. The principal localization S_f remains etale over R and its map
to K extends because the image of f is a unit. Thus it is a later triple, and the image
of 1/f makes x a unit in the colimit. Conversely a unit cannot map to zero in a field.
The structural map R → K kills p, giving pC ⊆ ker ψ. If ψ(x)=0, its representative
f lies in q. Etaleness implies pS_q=qS_q. Clear denominators to find u outside q with
uf in pS. The later triple S_u represents x by an element of pS_u, so x lies in pC.
These two inclusions prove the equality of ideals. The zero ring cannot be the colimit,
since the compatible map to K is unital.
(blueprint: lem-weil-pbc-etale-triples-colimit-localization). -/
theorem etaleResidueTriples_colimit_localization
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c)
    (ρ : R ⟶ c.pt)
    (hρ : ∀ t, t.α ≫ c.ι.app t = ρ)
    (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) :
    (∀ x : c.pt, ψ x ≠ 0 → IsUnit x) ∧
      RingHom.ker ψ = p.asIdeal.map ρ.hom := by
  let χ := CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)
  have eval_zero (t : EtaleResidueTriples R p K χ) (f : t.B) :
      (((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom f = 0) ↔
        f ∈ t.q.asIdeal := by
    change t.φ.hom (((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q).hom f) = 0 ↔ _
    rw [map_eq_zero]
    have hcanon := Spec.algebraMap_residueFieldIso_inv t.B t.q
    change CommRingCat.ofHom (algebraMap t.B t.q.asIdeal.ResidueField) ≫
      (Spec.residueFieldIso t.B t.q).inv =
        (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q at hcanon
    rw [← hcanon]
    change (Spec.residueFieldIso t.B t.q).inv.hom
      (algebraMap t.B t.q.asIdeal.ResidueField f) = 0 ↔ _
    rw [map_eq_zero]
    exact show f ∈ RingHom.ker (algebraMap t.B t.q.asIdeal.ResidueField) ↔
        f ∈ t.q.asIdeal by rw [Ideal.ker_algebraMap_residueField]
  have eval_compat (t : EtaleResidueTriples R p K χ) (f : t.B) :
      ψ ((c.ι.app t).hom f) =
        ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom f :=
    DFunLike.congr_fun (hψ t) f
  constructor
  · intro x hx
    obtain ⟨t, f, rfl⟩ := etaleResidueTriples_colimit_representative R p K χ c hc x
    have hf : f ∉ t.q.asIdeal := by
      intro hf
      exact hx ((eval_compat t f).trans ((eval_zero t f).mpr hf))
    obtain ⟨s, a, ha⟩ := etaleResidueTriple_unit_refinement R p K χ t f hf
    have hw := ConcreteCategory.congr_hom (c.w a) f
    exact hw ▸ ha.map (c.ι.app s).hom
  · apply le_antisymm
    · intro x hx
      obtain ⟨t, f, rfl⟩ := etaleResidueTriples_colimit_representative R p K χ c hc x
      have hf : f ∈ t.q.asIdeal := (eval_zero t f).mp
        ((eval_compat t f).symm.trans (RingHom.mem_ker.mp hx))
      obtain ⟨s, a, ha⟩ := etaleResidueTriple_ideal_refinement R p K χ t f hf
      have hm := Ideal.mem_map_of_mem (c.ι.app s).hom ha
      rw [Ideal.map_map] at hm
      have hcomp : (c.ι.app s).hom.comp s.α.hom = ρ.hom :=
        congrArg CommRingCat.Hom.hom (hρ s)
      rw [hcomp] at hm
      exact (ConcreteCategory.congr_hom (c.w a) f) ▸ hm
    · rw [Ideal.map_le_iff_le_comap]
      let t : EtaleResidueTriples R p K χ :=
        ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
      have htρ : c.ι.app t = ρ := by simpa [t] using hρ t
      intro r hr
      change ψ (ρ.hom r) = 0
      rw [← htρ]
      exact (eval_compat t r).trans ((eval_zero t r).mpr hr)

end AlgebraicGeometry.Scheme
