/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.RingTheory.RootLiftingEtaleRetraction

/-! Uniqueness part of the henselian étale retraction theorem.

The standard étale presentation and simple-root uniqueness in Stacks Project, Tag 04GG,
show that two sections with the prescribed prime are equal.
(blueprint: lem-weil-pbc-henselian-etale-retraction-uniqueness)
-/

@[expose] public section

universe u

open AlgebraicGeometry

/-- The theorem is the uniqueness portion of Stacks Project Lemma Tag 04GG, implication
 (1) => (8).  Localize at an element outside q' and use a standard etale presentation.
 The two maps induce the same residue-field map, so their values on the presentation
 generator are roots congruent modulo the maximal ideal.  The standard-etale identity
 makes the derivative a unit; henselian simple-root uniqueness therefore identifies
 the generator images, and the universal property plus localization identifies the
 two algebra maps.  (blueprint: lem-weil-pbc-henselian-etale-retraction-uniqueness)
-/
theorem algHom_eq_of_henselianLocalRing_etale
    {S B : Type u} [CommRing S] [CommRing B] [HenselianLocalRing S]
    (φ : S →+* B)
    [AlgebraicGeometry.Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)]
    (q' : Ideal B) [q'.IsPrime]
    (hq : q'.comap φ = IsLocalRing.maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm)) :
    letI : Algebra S B := φ.toAlgebra
    ∀ (σ τ : B →ₐ[S] S),
      (IsLocalRing.maximalIdeal S).comap σ.toRingHom = q' →
      (IsLocalRing.maximalIdeal S).comap τ.toRingHom = q' → σ = τ := by
  open CategoryTheory in
  exact by
    let : Algebra S B := φ.toAlgebra
    intro σ τ hσ hτ
    let x : PrimeSpectrum B := ⟨q', inferInstance⟩
    let f := Spec.map (CommRingCat.ofHom φ)
    let y : PrimeSpectrum S := f x
    let β : B →+* (Spec (.of B)).residueField x :=
      (Scheme.Spec.residueFieldIso (.of B) x).inv.hom.comp (algebraMap B q'.ResidueField)
    let α : S →+* (Spec (.of S)).residueField y :=
      (Scheme.Spec.residueFieldIso (.of S) y).inv.hom.comp
        (algebraMap S y.asIdeal.ResidueField)
    have hnat : β.comp φ = (f.residueFieldMap x).hom.comp α := by
      have hn : CommRingCat.ofHom φ ≫
          (CommRingCat.ofHom (algebraMap B q'.ResidueField) ≫
            (Scheme.Spec.residueFieldIso (.of B) x).inv) =
          (CommRingCat.ofHom (algebraMap S y.asIdeal.ResidueField) ≫
            (Scheme.Spec.residueFieldIso (.of S) y).inv) ≫ f.residueFieldMap x := by
        erw [Scheme.Spec.algebraMap_residueFieldIso_inv,
          Scheme.Spec.algebraMap_residueFieldIso_inv]
        change CommRingCat.ofHom φ ≫
          ((Scheme.ΓSpecIso (.of B)).inv ≫ (Spec (.of B)).Γevaluation x) =
          ((Scheme.ΓSpecIso (.of S)).inv ≫ (Spec (.of S)).Γevaluation y) ≫
            f.residueFieldMap x
        simp only [CategoryTheory.Category.assoc, Scheme.ΓSpecIso_inv_naturality_assoc]
        erw [Scheme.Γevaluation_naturality f x]
      exact congrArg (fun h : CommRingCat.of S ⟶ (Spec (.of B)).residueField x ↦ h.hom) hn
    have hsurj : Function.Surjective ((algebraMap B q'.ResidueField).comp φ) := by
      have heq : (algebraMap B q'.ResidueField).comp φ =
          (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm).comp
            (algebraMap S (IsLocalRing.maximalIdeal S).ResidueField) := by
        ext s
        exact (Ideal.ResidueField.map_algebraMap _ _ _ _ s).symm
      rw [heq]
      exact hres.2.comp (IsLocalRing.maximalIdeal S).algebraMap_residueField_surjective
    have hγ : Function.Surjective (β.comp φ) :=
      (Scheme.Spec.residueFieldIso (.of B) x).commRingCatIsoToRingEquiv.symm.surjective.comp
        hsurj
    have hspec : Function.Bijective (f.residueFieldMap x).hom := by
      refine ⟨RingHom.injective _, ?_⟩
      intro z
      obtain ⟨s, hs⟩ := hγ z
      exact ⟨α s, (DFunLike.congr_fun hnat s).symm.trans hs⟩
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap S B))) :=
      ‹Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)›
    obtain ⟨ρ, _, hunique⟩ :=
      IsLocalRing.existsUnique_algHom_of_monic_simple_root_lifting_etale
      (((HenselianLocalRing.TFAE S).out 1 2).mp
        (show HenselianLocalRing S from inferInstance)) q' hq hspec
    exact (hunique σ hσ).trans (hunique τ hτ).symm

