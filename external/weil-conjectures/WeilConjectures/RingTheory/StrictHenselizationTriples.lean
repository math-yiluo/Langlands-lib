/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RingTheory.EtaleResidueTriplesColimit
import WeilConjectures.RingTheory.EtaleResidueTriplesLocalization
import WeilConjectures.RingTheory.EtaleResidueTriplesSimpleRoots
import WeilConjectures.RingTheory.EtaleResidueTriplesSurjective

/-!
# Strict henselization from etale triples

Source: Stacks Project, Algebra, Lemmas Tags 04GW and 04GP
(blueprint: lem-weil-pbc-strict-henselization-triples).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/- The filteredness part of strictHenselization_triples.
Source: Stacks Project, Algebra, Tag 04GW (lemma-strict-henselization-different).
(blueprint: lem-weil-pbc-strict-henselization-triples-filtered-part).
The preceding colimit construction identifies triples with etale algebras equipped with
an R-algebra map to K, proves essential smallness, and constructs the filtered colimit.
-/
private theorem strictHenselization_triples_filtered
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K] :
    IsFiltered (EtaleResidueTriples R p K
        (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))) := by
  exact (etaleResidueTriples_filtered_colimit R p K).1

/- The remaining colimit properties are assembled from the localization, simple-root,
and surjectivity lemmas above. Source: Stacks Project, Algebra, Tags 04GN and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-triples-colimit-properties). -/
private theorem strictHenselization_triples_colimit_properties
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K] :
    ∃ c : Cocone (etaleResidueTriplesRingDiagram R p K
          (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))),
        Nonempty (IsColimit c) ∧
        ∃ (_ : IsLocalRing c.pt) (ρ : R ⟶ c.pt) (ψ : c.pt →+* K),
          (∀ t, t.α ≫ c.ι.app t = ρ) ∧
          (∀ t, ψ.comp (c.ι.app t).hom =
            ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) ∧
          Function.Surjective ψ ∧
          IsLocalRing.maximalIdeal c.pt = RingHom.ker ψ ∧
          RingHom.ker ψ = p.asIdeal.map ρ.hom ∧
          (RingHom.ker ψ).comap ρ.hom = p.asIdeal ∧
          (∃ e : (c.pt ⧸ IsLocalRing.maximalIdeal c.pt) ≃+* K,
            e.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal c.pt)) = ψ) ∧
          IsStrictlyHenselianLocalRing c.pt := by
  obtain ⟨hfiltered, c, ⟨hc⟩, ρ, ψ, hρ, hψ⟩ :=
    etaleResidueTriples_filtered_colimit R p K
  have := hfiltered
  obtain ⟨hunit, hker⟩ := etaleResidueTriples_colimit_localization R p K c hc ρ hρ ψ hψ
  have hroot := etaleResidueTriples_colimit_simple_roots R p K c hc ψ hψ
  have hsurj := etaleResidueTriples_colimit_surjective R p K c hc ψ hψ hunit hroot
  have : Nontrivial c.pt := ψ.domain_nontrivial
  have : IsLocalRing c.pt :=
    IsLocalRing.of_is_unit_or_is_unit_of_add_one fun {a b} hab ↦ by
      by_cases ha : ψ a = 0
      · right
        apply hunit
        have h := congrArg ψ hab
        have hb : ψ b = 1 := by simpa [map_add, ha] using h
        rw [hb]
        exact one_ne_zero
      · exact Or.inl (hunit a ha)
  have hm := (IsLocalRing.ker_eq_maximalIdeal ψ hsurj).symm
  let e : (c.pt ⧸ IsLocalRing.maximalIdeal c.pt) ≃+* K :=
    (Ideal.quotEquivOfEq hm).trans (ψ.quotientKerEquivOfSurjective hsurj)
  have he : e.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal c.pt)) = ψ := by
    ext x
    simp [e]
  have : HenselianLocalRing c.pt := by
    refine HenselianLocalRing.mk ?_
    intro f hf a₀ ha hda
    have ha' : f.eval₂ ψ (ψ a₀) = 0 := by
      rw [Polynomial.eval₂_at_apply, ← RingHom.mem_ker, ← hm]
      exact ha
    have hda' : f.derivative.eval₂ ψ (ψ a₀) ≠ 0 := by
      rw [Polynomial.eval₂_at_apply]
      exact (hda.map ψ).ne_zero
    obtain ⟨a, ha, hψa⟩ := hroot f hf (ψ a₀) ha' hda'
    refine ⟨a, ha, ?_⟩
    rw [hm, RingHom.mem_ker, map_sub, hψa, sub_self]
  have : IsSepClosed K := IsSepClosure.sep_closed ((Spec R).residueField p)
  have : IsSepClosed (IsLocalRing.ResidueField c.pt) := IsSepClosed.of_ringEquiv e.symm
  refine ⟨c, ⟨hc⟩, inferInstance, ρ, ψ, hρ, hψ, hsurj, hm, hker, ?_, ⟨e, he⟩,
    ⟨inferInstance⟩⟩
  let t : EtaleResidueTriples R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)) :=
    ⟨R, 𝟙 R, inferInstance, p, by simp,
      CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K), by simp⟩
  have htρ : c.ι.app t = ρ := by simpa [t] using hρ t
  have htψ := hψ t
  rw [htρ] at htψ
  change ψ.comp ρ.hom =
    ((ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫
      CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)).hom at htψ
  ext r
  change ψ (ρ.hom r) = 0 ↔ r ∈ p.asIdeal
  rw [← RingHom.comp_apply, htψ]
  change algebraMap ((Spec R).residueField p) K
    (((ΓSpecIso R).inv ≫ (Spec R).Γevaluation p).hom r) = 0 ↔ r ∈ p.asIdeal
  rw [map_eq_zero]
  have hcanon := Spec.algebraMap_residueFieldIso_inv R p
  change CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField) ≫
    (Spec.residueFieldIso R p).inv = (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p at hcanon
  rw [← hcanon]
  change (Spec.residueFieldIso R p).inv.hom (algebraMap R p.asIdeal.ResidueField r) = 0 ↔ _
  rw [map_eq_zero]
  exact show r ∈ RingHom.ker (algebraMap R p.asIdeal.ResidueField) ↔ r ∈ p.asIdeal by
    rw [Ideal.ker_algebraMap_residueField]

/-- The category of etale residue triples is filtered and its ring colimit is strictly
henselian with the prescribed separable closure as residue field.
Source: Stacks Project, Algebra, Lemmas Tags 04GW and 04GP
(blueprint: lem-weil-pbc-strict-henselization-triples).

Proof:
1. Triples are etale R-algebras pointed in K, since a map to a field factors uniquely
through the residue field of its kernel.
2. Finite presentation gives essential smallness; construct the ring colimit using a
small skeleton (lem-weil-pbc-affine-etale-essentially-small-cover and
lem-weil-pbc-colimit-initial-full-subcategory).
3. Tensor products give common successors, including the identity triple for nonemptiness
(lem-weil-pbc-etale-ring-base-change, definition-torsion-sheaves--3).
4. For parallel maps beta1, beta2 : S → S', form E = S' ⊗[S] S' using these maps,
then S'' = E ⊗[S' ⊗[R] S'] S' using multiplication on the last factor. Both
base changes are etale by the same base-change and composition lemmas. The two maps
to K agree, hence extend to S''; its kernel and residue embedding define a triple.
The rightmost S' → S'' commutes with the maps to K and equalizes beta1 and beta2,
since beta1(s) ⊗ 1 = 1 ⊗ beta2(s) in E. This gives filteredness.
5. The compatible maps to K induce psi. Inverting an element with nonzero image shows
that the colimit is local, with maximal ideal ker psi.
6. The etale prime-generation lemma lem-weil-pbc-etale-prime-generates-maximal, followed
by localization away from the pointed prime, shows ker psi = p C: represent an
element of the kernel by f ∈ q at a stage S. Its image in S_q lies in p S_q; clearing
denominators gives u ∉ q with u f ∈ p S. The triple S_u makes f lie in p S_u.
The reverse inclusion follows because the structural map to K kills p.
7. Descend the finitely many coefficients of a monic polynomial to one stage, and use
the standard etale algebra localized at its derivative to lift each simple root in K
(lem-weil-pbc-filtered-colimit-algebras-elementwise and
lem-weil-pbc-standard-etale-monic-derivative).
8. The image of psi is a field containing kappa(p). Separability of every element of K
and step 7 imply surjectivity: lift the coefficients of its monic separable minimal
polynomial to C, then lift its simple root using step 7. The induced quotient
isomorphism identifies the residue
field with K, and contraction of the maximal ideal is p.
9. Step 7 and lem-weil-pbc-henselian-local-root-lifting give henselianity. The residue
field is K, hence separably closed, giving strict henselianity.
-/
theorem strictHenselization_triples
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K] :
    IsFiltered (EtaleResidueTriples R p K
        (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))) ∧
      ∃ c : Cocone (etaleResidueTriplesRingDiagram R p K
          (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))),
        Nonempty (IsColimit c) ∧
        ∃ (_ : IsLocalRing c.pt) (ρ : R ⟶ c.pt) (ψ : c.pt →+* K),
          (∀ t, t.α ≫ c.ι.app t = ρ) ∧
          (∀ t, ψ.comp (c.ι.app t).hom =
            ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) ∧
          Function.Surjective ψ ∧
          IsLocalRing.maximalIdeal c.pt = RingHom.ker ψ ∧
          RingHom.ker ψ = p.asIdeal.map ρ.hom ∧
          (RingHom.ker ψ).comap ρ.hom = p.asIdeal ∧
          (∃ e : (c.pt ⧸ IsLocalRing.maximalIdeal c.pt) ≃+* K,
            e.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal c.pt)) = ψ) ∧
          IsStrictlyHenselianLocalRing c.pt := by
  refine ⟨strictHenselization_triples_filtered R p K, ?_⟩
  exact strictHenselization_triples_colimit_properties R p K

end AlgebraicGeometry.Scheme
