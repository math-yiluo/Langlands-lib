/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.RingTheory.Etale.LocalDimension
import WeilConjectures.RingTheory.FilteredColimitPrimeChainDimension
import WeilConjectures.RingTheory.RingKrullDimLeOfFaithfullyFlatOfIsLocalHom
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# Krull dimension of a strict henselization

Source: Stacks Project, More on Algebra, Tag 06LK
(blueprint: lem-sc-strict-henselization-dimension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

private theorem dimension_atPrime_congr {S : Type u} [CommRing S]
    (q q' : Ideal S) [q.IsPrime] [q'.IsPrime] (h : q = q') :
    ringKrullDim (Localization.AtPrime q) = ringKrullDim (Localization.AtPrime q') := by
  subst q'
  rfl

/-- Contract a finite chain to one stage, then lift it through the prime correspondence
for localization at the contraction of the colimit maximal ideal. Taking the supremum
of chain lengths gives the bound, without a finite-dimensionality assumption. -/
private theorem local_colimit_dimension_bound
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    [IsLocalRing c.pt] (d : WithBot ℕ∞)
    (hbound : ∀ i, ringKrullDim
      (Localization.AtPrime ((IsLocalRing.maximalIdeal c.pt).comap (c.ι.app i).hom)) ≤ d) :
    ringKrullDim c.pt ≤ d := by
  classical
  let e := (colimit.isColimit D).coconePointUniqueUpToIso hc
  rw [ringKrullDim, Order.krullDim]
  apply iSup_le
  intro p
  let P : Fin (p.length + 1) → Ideal (colimit D : CommRingCat.{u}) :=
    fun j ↦ (p j).asIdeal.comap e.hom.hom
  have hP : StrictMono P := by
    intro i j hij
    exact (Ideal.orderEmbeddingOfSurjective e.hom.hom
      e.commRingCatIsoToRingEquiv.surjective).strictMono (p.strictMono hij)
  obtain ⟨i, hprime, hstrict⟩ :=
    (CommRingCat.filteredColimit_prime_chain_and_dimension D).1 p.length P
      (fun j ↦ (p j).isPrime.comap e.hom.hom) hP
  let q := (IsLocalRing.maximalIdeal c.pt).comap (c.ι.app i).hom
  let Q : Fin (p.length + 1) → Set.Iic (⟨q, inferInstance⟩ : PrimeSpectrum (D.obj i)) :=
    fun j ↦ ⟨⟨(P j).comap (colimit.ι D i).hom, hprime j⟩, by
      change (P j).comap (colimit.ι D i).hom ≤ q
      have he := (colimit.isColimit D).comp_coconePointUniqueUpToIso_hom hc i
      have he' := congrArg CommRingCat.Hom.hom he
      change (p j).asIdeal.comap (e.hom.hom.comp (colimit.ι D i).hom) ≤ q
      change e.hom.hom.comp (colimit.ι D i).hom = (c.ι.app i).hom at he'
      rw [he']
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal (p j).isPrime.ne_top)⟩
  have hQ : StrictMono Q := fun j k hjk ↦ hstrict hjk
  let l := LTSeries.mk p.length
    (fun j ↦ (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime q) q).symm
      (Q j))
    (fun j k hjk ↦
      (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime q) q).symm.strictMono
        (hQ hjk))
  exact (Order.LTSeries.length_le_krullDim l).trans (hbound i)

namespace AlgebraicGeometry.Scheme

/-- Forget the étale structure morphism, retaining its ring. -/
private noncomputable def dimensionAffineEtaleRings (R : CommRingCat.{u}) :
    (Spec R).AffineEtaleᵒᵖ ⥤ CommRingCat.{u} where
  obj t := t.unop.left.unop
  map f := f.unop.left.unop

/-- Regard a pointed ring as an arrow from an affine étale ring to `K`. -/
private noncomputable def dimensionTriplesToPointedRings (R : CommRingCat.{u}) (p : Spec R)
    (K : Type u) [Field K] (χ : (Spec R).residueField p ⟶ CommRingCat.of K) :
    EtaleResidueTriples R p K χ ⥤ CostructuredArrow (dimensionAffineEtaleRings R) (.of K) where
  obj t := CostructuredArrow.mk (Y := Opposite.op
    (MorphismProperty.CostructuredArrow.mk ⊤ (Spec.map t.α) t.etale))
    ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ)
  map {t s} f := CostructuredArrow.homMk
    (Quiver.Hom.op (MorphismProperty.CostructuredArrow.homMk
      f.hom.right.left.op trivial (by
        have h := congrArg Over.Hom.left (Under.w f.hom)
        simp only [EtaleResidueTriple.factorization, Under.mk_hom, Over.homMk_left,
          Over.comp_left] at h
        change Spec.map f.hom.right.left ≫ Spec.map t.α = Spec.map s.α
        rw [← Spec.map_comp, h]))) (by
      change f.hom.right.left ≫
        ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) =
        (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ
      simpa only [EtaleResidueTriple.factorization,
        Under.mk_right, Over.mk_hom, Category.assoc] using Over.w f.hom.right)
  map_id t := by ext; rfl
  map_comp f g := by ext; rfl

/-- Every map of pointed étale rings comes from a map of triples.
This private comparison is the fully faithful construction used in
`EtaleResidueTriplesExistsColimit`; it supplies the small skeleton needed by the
prime-chain lemma without changing any public instance. -/
private noncomputable def dimensionTriplesToPointedRingsFullyFaithful
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K) :
    (dimensionTriplesToPointedRings R p K χ).FullyFaithful where
  preimage {t s} f := InducedCategory.homMk
    (Under.homMk (Over.homMk f.left.unop.left.unop (by
      have h := CostructuredArrow.w f
      change f.left.unop.left.unop ≫
        ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) =
        (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ at h
      simpa only [EtaleResidueTriple.factorization, Under.mk_right, Over.mk_hom,
        Category.assoc] using h)) (by
      apply Over.OverMorphism.ext
      change t.α ≫ f.left.unop.left.unop = s.α
      apply Spec.map_injective
      rw [Spec.map_comp]
      exact f.left.unop.w))
  map_preimage f := by ext; rfl
  preimage_map f := by ext; rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation into the field has kernel equal to the pointed prime. The étale local
 dimension lemma then bounds this stage localization by the dimension of the base. -/
private theorem dimension_triples_stage
    (R : CommRingCat.{u}) [IsLocalRing R] (p : Spec R)
    (hp : p.asIdeal = IsLocalRing.maximalIdeal R)
    (K : Type u) [Field K] (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (c : Cocone (etaleResidueTriplesRingDiagram R p K χ)) [IsLocalRing c.pt]
    (ψ : c.pt →+* K) (hm : IsLocalRing.maximalIdeal c.pt = RingHom.ker ψ)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom)
    (t : EtaleResidueTriples R p K χ) :
    ringKrullDim (Localization.AtPrime
      ((IsLocalRing.maximalIdeal c.pt).comap (c.ι.app t).hom)) ≤ ringKrullDim R := by
  have hq : (IsLocalRing.maximalIdeal c.pt).comap (c.ι.app t).hom = t.q.asIdeal := by
    rw [hm]
    ext x
    change (ψ.comp (c.ι.app t).hom) x = 0 ↔ x ∈ t.q.asIdeal
    rw [hψ t]
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
  rw [dimension_atPrime_congr _ _ hq]
  have ht := t.etale
  have hetale : t.α.hom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp ht
  apply (RingHom.Etale.ringKrullDim_localization_eq
    t.α.hom hetale t.q.asIdeal).symm.le.trans
  have hover : t.q.asIdeal.comap t.α.hom = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal t.over
  apply (dimension_atPrime_congr _ _ (hover.trans hp)).le.trans
  let em := IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
    (S := Localization.AtPrime (IsLocalRing.maximalIdeal R)) (by
      intro x hx
      have hx' : x ∉ IsLocalRing.maximalIdeal R := hx
      change IsUnit x
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hx')
  exact em.toRingEquiv.ringKrullDim.symm.le

end AlgebraicGeometry.Scheme

namespace Algebra

/-- Strict henselization preserves the Krull dimension of any local commutative ring.
Here `C` is the strict henselization of `R` with respect to the separable closure `K` of
the residue field of `R`.
Source: Stacks Project, More on Algebra, Tag 06LK
(blueprint: lem-sc-strict-henselization-dimension).

Proof: The canonical local map is faithfully flat
(lem-sc-strict-henselization-faithfully-flat), so going down gives the lower bound
(lem-sc-faithfully-flat-local-dimension). For the upper bound, use the filtered étale
triples presentation (lem-weil-pbc-strict-henselization-triples). Every finite strict
chain of primes contracts to a strict chain in some stage
(lem-sc-filtered-colimit-prime-chain-dimension). All contracted primes lie below the
pointed prime at that stage, so the chain survives in its localization. Étale local
dimension invariance (lem-sc-etale-local-dimension) identifies that localization's
dimension with that of `R`. Every finite chain length is therefore bounded by
`ringKrullDim R`, which gives the upper bound, including when the dimension is infinite. -/
theorem ringKrullDim_eq_of_isStrictHenselization
    (R K C : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C] (hC : IsStrictHenselization R K C) :
    ringKrullDim R = ringKrullDim C := by
  classical
  obtain ⟨p, hp, a, hs, ι, ⟨hc⟩, hρ⟩ := hC.triples_presentation R K C
  let := a
  have := hs
  let χ := CommRingCat.ofHom
    (algebraMap ((AlgebraicGeometry.Spec (CommRingCat.of R)).residueField p) K)
  let D := AlgebraicGeometry.Scheme.etaleResidueTriplesRingDiagram
    (CommRingCat.of R) p K χ
  obtain ⟨hfiltered, c₀, ⟨hc₀⟩, hlocal, ρ₀, ψ₀, hρ₀, hψ₀, _, hm₀, _, hcontract, _⟩ :=
    AlgebraicGeometry.Scheme.strictHenselization_triples (CommRingCat.of R) p K
  have := hfiltered
  have := hlocal
  let e := hc.coconePointUniqueUpToIso hc₀
  rw [e.commRingCatIsoToRingEquiv.ringKrullDim]
  apply le_antisymm
  · have : IsLocalHom ρ₀.hom := by
      apply ((IsLocalRing.local_hom_TFAE ρ₀.hom).out 5 1).mp
      rw [hm₀, hcontract, hp]
    exact RingHom.ringKrullDim_le_of_faithfullyFlat_of_isLocalHom ρ₀.hom
      (AlgebraicGeometry.Scheme.strictHenselization_faithfullyFlat
        (CommRingCat.of R) p hp K c₀ hc₀ ρ₀ hρ₀)
  · let F := AlgebraicGeometry.Scheme.dimensionTriplesToPointedRings
      (CommRingCat.of R) p K χ
    have : F.Full :=
      (AlgebraicGeometry.Scheme.dimensionTriplesToPointedRingsFullyFaithful
        (CommRingCat.of R) p K χ).full
    have : F.Faithful :=
      (AlgebraicGeometry.Scheme.dimensionTriplesToPointedRingsFullyFaithful
        (CommRingCat.of R) p K χ).faithful
    have : EssentiallySmall.{u}
        (AlgebraicGeometry.Scheme.EtaleResidueTriples (CommRingCat.of R) p K χ) :=
      essentiallySmall_of_fully_faithful F
    let E := (equivSmallModel.{u}
      (AlgebraicGeometry.Scheme.EtaleResidueTriples (CommRingCat.of R) p K χ)).symm
    have : IsFiltered (SmallModel.{u}
        (AlgebraicGeometry.Scheme.EtaleResidueTriples (CommRingCat.of R) p K χ)) :=
      IsFiltered.of_equivalence E.symm
    have : IsLocalRing (c₀.whisker E.functor).pt := hlocal
    apply local_colimit_dimension_bound (E.functor ⋙ D) (c₀.whisker E.functor)
      (hc₀.whiskerEquivalence E)
    intro i
    exact AlgebraicGeometry.Scheme.dimension_triples_stage (CommRingCat.of R) p hp
      K χ c₀ ψ₀ hm₀ hψ₀ (E.functor.obj i)

end Algebra
