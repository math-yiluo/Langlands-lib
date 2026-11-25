/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart1Supplement3
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart2Supplement2

/-! # Points and components of the principal w-localization

Source: blueprint, proper base change, lemma "Points of the affine w-localization", order 1223
(blueprint: theorem-existence-contractible-covers--1).
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace PrincipalWLocalization

private theorem indZariski (A : Type u) [CommRing A] :
    Algebra.IndZariski A (algebra A) := by
  let P : CategoryTheory.Limits.ColimitPresentation (Index A) (algebra A) :=
    { diag := diagram
      ι := (CategoryTheory.Limits.colimit.cocone diagram).ι
      isColimit := CategoryTheory.Limits.colimit.isColimit diagram }
  exact Algebra.IndZariski.of_colimitPresentation A (algebra A) P fun i ↦
    inferInstanceAs (Algebra.IndZariski A (Stage i))

private theorem patchT2 (A : Type u) [CommRing A] :
    T2Space (WithConstructibleTopology (PrimeSpectrum A)) := by
  classical
  refine ⟨fun x y hxy ↦ ?_⟩
  obtain ⟨f, hf⟩ : ∃ f : A,
      ¬ (f ∈ x.ofTopology.asIdeal ↔ f ∈ y.ofTopology.asIdeal) := by
    by_contra! h
    exact hxy (WithTopology.ofTopology_injective _ (PrimeSpectrum.ext (Ideal.ext h)))
  let U : Set (WithConstructibleTopology (PrimeSpectrum A)) :=
    WithTopology.ofTopology ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))
  have hU : IsClopen U := by
    constructor
    · rw [WithConstructibleTopology.isClosed_iff]
      exact (PrimeSpectrum.isCompact_basicOpen f).isClosed_constructibleTopology_of_isOpen
        (PrimeSpectrum.basicOpen f).isOpen
    · rw [WithConstructibleTopology.isOpen_iff]
      exact (PrimeSpectrum.isCompact_basicOpen f).isOpen_constructibleTopology_of_isOpen
        (PrimeSpectrum.basicOpen f).isOpen
  by_cases hx : f ∈ x.ofTopology.asIdeal
  · have hy : f ∉ y.ofTopology.asIdeal := fun hy ↦ hf ⟨fun _ ↦ hy, fun _ ↦ hx⟩
    exact ⟨Uᶜ, U, hU.compl.isOpen, hU.isOpen, (fun h ↦ h hx), hy, disjoint_compl_left⟩
  · have hy : f ∈ y.ofTopology.asIdeal := by
      by_contra hy
      exact hf ⟨fun h ↦ (hx h).elim, fun h ↦ (hy h).elim⟩
    exact ⟨U, Uᶜ, hU.isOpen, hU.compl.isOpen, hx, (fun h ↦ h hy), disjoint_compl_right⟩

/-- The prime-pair description, local rings, component schemes, and closed points of the
finite-partition principal w-localization. The closed immersion from `Spec A_x` with image the
first-coordinate fibre equips that fibre with its canonical affine scheme structure. Its ring
map is an `A`-algebra map, so these identifications respect the structural morphism to `Spec A`.
The homeomorphism on closed points and the continuous first-coordinate map use the patch
rather than the Zariski topology on `Spec A`.

Source: blueprint order 1223 (blueprint: theorem-existence-contractible-covers--1).
Proof:
1. The proved `primeCharts` theorem supplies the prime-pair bijection, contraction formula,
continuous first coordinate, and the closed immersion of `Spec A_x` onto its first-coordinate
fibre. Its proof selects factors of each finite stage, uses compactness of the patch spectrum,
and constructs the explicit surjective evaluation maps.
2. The colimit presentation by finite products of principal localizations is ind-Zariski.
The proved upstream `Algebra.IndZariski.bijectiveOnStalks_algebraMap` identifies the local ring
at a prime with the localization of `A` at its contraction. Its canonical local-ring map fixes
`A`, hence the inverse bijection gives the required `A`-algebra equivalence.
3. Preimages of the basic patch clopens are clopen. They force the first coordinate to be
constant on connected components and on specializations. Every point of a fibre specializes
to the image of the closed point of `Spec A_x`, namely the diagonal point `(x,x)`. Thus two
points in the same fibre have the same connected component; distinct fibres are separated by
a basic patch clopen. This proves the component formula.
4. A diagonal point is closed because it is the image of the closed point of a local spectrum
under a closed immersion. Every point specializes to its diagonal point, so these are exactly
the closed points. The complement of the diagonal is the union, over `f : A`, of the open sets
where `f` belongs to the first prime and does not belong to the contracted prime. Indeed for
`y` strictly contained in `x` one can choose `f` in `x` but outside `y`.
5. The first-coordinate bijection from the closed points to the patch spectrum is continuous.
Its domain is compact, since the closed points are closed in an affine spectrum. The patch
spectrum is Hausdorff: distinct primes are separated by the complementary patch clopens
`D(f)` and `V(f)` for an element on which they differ. A continuous bijection from a compact
space to a Hausdorff space is a homeomorphism. Its inverse is the diagonal map. The closedness
and unique closed specialization establish w-locality.
6. Ind-Zariski algebras are flat by the proved upstream API. The structural spectrum map is
surjective because of the diagonal points. Mathlib's flat-surjective-spectrum criterion gives
faithful flatness. All constructions include the empty spectrum of the zero ring; the cut
partitions omit empty parts and statements quantified over primes are then vacuous.
-/
theorem points (A : Type u) [CommRing A] :
    ∃ e : PrimeSpectrum (algebra A) ≃
        {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal},
      (∀ q : PrimeSpectrum (algebra A),
        PrimeSpectrum.comap (algebraMap A (algebra A)) q = (e q).val.2) ∧
      (∀ q : PrimeSpectrum (algebra A),
        Nonempty (Localization.AtPrime q.asIdeal ≃ₐ[A]
          Localization.AtPrime (e q).val.2.asIdeal)) ∧
      (@Continuous (PrimeSpectrum (algebra A)) (PrimeSpectrum A) inferInstance
        (constructibleTopology (PrimeSpectrum A)) (fun q ↦ (e q).val.1)) ∧
      (∀ q : PrimeSpectrum (algebra A),
        connectedComponent q = {r | (e r).val.1 = (e q).val.1}) ∧
      (∀ x : PrimeSpectrum A,
        ∃ ρ : algebra A →ₐ[A] Localization.AtPrime x.asIdeal,
          IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ.toRingHom)) ∧
          Set.range (PrimeSpectrum.comap ρ.toRingHom) = {q | (e q).val.1 = x}) ∧
      (∀ q : PrimeSpectrum (algebra A),
        q ∈ closedPoints (PrimeSpectrum (algebra A)) ↔ (e q).val.1 = (e q).val.2) ∧
      IsClosed (closedPoints (PrimeSpectrum (algebra A))) ∧
      (∃ h : @Homeomorph (PrimeSpectrum A)
          (closedPoints (PrimeSpectrum (algebra A)))
          (constructibleTopology (PrimeSpectrum A)) inferInstance,
        ∀ x : PrimeSpectrum A, (e (h x).val).val = (x, x)) ∧
      Module.FaithfullyFlat A (algebra A) ∧ IsWLocalRing (algebra A) := by
  classical
  have hdata := primeCharts A
  obtain ⟨e, he, hπ, hρ⟩ := hdata
  have hind : Algebra.IndZariski A (algebra A) := indZariski A
  have hlocal (q : PrimeSpectrum (algebra A)) :
      Nonempty (Localization.AtPrime q.asIdeal ≃ₐ[A]
        Localization.AtPrime (e q).val.2.asIdeal) := by
    let f : Localization.AtPrime (PrimeSpectrum.comap
        (algebraMap A (algebra A)) q).asIdeal →ₐ[A] Localization.AtPrime q.asIdeal :=
      { toRingHom := Localization.localRingHom _ _ (algebraMap A (algebra A)) rfl
        commutes' a := by
          change Localization.localRingHom _ _ (algebraMap A (algebra A)) rfl
              (algebraMap A _ a) =
            algebraMap (algebra A) _ (algebraMap A (algebra A) a)
          exact Localization.localRingHom_to_map .. }
    have hf : Function.Bijective f :=
      Algebra.BijectiveOnStalks.bijective_localRingHom q.asIdeal
    have hh := (AlgEquiv.ofBijective f hf).symm
    rw [he q] at hh
    exact ⟨hh⟩
  let δ (x : PrimeSpectrum A) : PrimeSpectrum (algebra A) :=
    e.symm ⟨(x, x), le_rfl⟩
  have hδ (x : PrimeSpectrum A) : (e (δ x)).val = (x, x) := by
    simp [δ]
  have hclopen (f : A) : IsClopen {q | f ∉ (e q).val.1.asIdeal} := by
    have h : @IsClopen (PrimeSpectrum A) (constructibleTopology (PrimeSpectrum A))
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) :=
      ⟨(PrimeSpectrum.isCompact_basicOpen f).isClosed_constructibleTopology_of_isOpen
          (PrimeSpectrum.basicOpen f).isOpen,
        (PrimeSpectrum.isCompact_basicOpen f).isOpen_constructibleTopology_of_isOpen
          (PrimeSpectrum.basicOpen f).isOpen⟩
    exact @IsClopen.preimage _ _ _ (constructibleTopology (PrimeSpectrum A))
      _ h (fun q ↦ (e q).val.1) hπ
  have hcc_first {q r : PrimeSpectrum (algebra A)} (hr : r ∈ connectedComponent q) :
      (e r).val.1 = (e q).val.1 := by
    apply PrimeSpectrum.ext
    ext f
    constructor
    · intro hfr
      by_contra hfq
      exact ((hclopen f).connectedComponent_subset hfq hr) hfr
    · intro hfq
      by_contra hfr
      exact ((hclopen f).compl.connectedComponent_subset (by simpa using hfq) hr) hfr
  have hspec_first {q r : PrimeSpectrum (algebra A)} (h : q ⤳ r) :
      (e r).val.1 = (e q).val.1 := by
    apply hcc_first
    have hh := ConnectedComponents.coe_eq_coe.mp h.connectedComponents_mk_eq
    rw [hh]
    exact mem_connectedComponent
  have hρδ (x : PrimeSpectrum A)
      (ρ : algebra A →ₐ[A] Localization.AtPrime x.asIdeal)
      (hrange : Set.range (PrimeSpectrum.comap ρ.toRingHom) = {q | (e q).val.1 = x}) :
      PrimeSpectrum.comap ρ.toRingHom (IsLocalRing.closedPoint _) = δ x := by
    apply e.injective
    apply Subtype.ext
    apply Prod.ext
    · exact (hrange ▸ Set.mem_range_self (IsLocalRing.closedPoint _)).trans
        (congrArg Prod.fst (hδ x)).symm
    · rw [← he, ← PrimeSpectrum.comap_comp_apply]
      have hcomp : ρ.toRingHom.comp (algebraMap A (algebra A)) =
          algebraMap A (Localization.AtPrime x.asIdeal) := by
        ext a
        exact ρ.commutes a
      rw [hcomp]
      apply PrimeSpectrum.ext
      change Ideal.comap _ (IsLocalRing.maximalIdeal _) = _
      rw [show Ideal.comap (algebraMap A (Localization.AtPrime x.asIdeal))
        (IsLocalRing.maximalIdeal _) = x.asIdeal from
          Localization.AtPrime.under_maximalIdeal]
      exact congrArg (fun z ↦ z.2.asIdeal) (hδ x).symm
  have hspecial (q : PrimeSpectrum (algebra A)) : q ⤳ δ (e q).val.1 := by
    obtain ⟨ρ, _, hrange⟩ := hρ (e q).val.1
    have hq : q ∈ Set.range (PrimeSpectrum.comap ρ.toRingHom) := by
      rw [hrange]
      rfl
    obtain ⟨p, hp⟩ := hq
    have hh := (IsLocalRing.specializes_closedPoint p).map (PrimeSpectrum.continuous_comap
      ρ.toRingHom)
    rw [hp, hρδ _ ρ hrange] at hh
    exact hh
  have hδclosed (x : PrimeSpectrum A) : IsClosed ({δ x} : Set _) := by
    obtain ⟨ρ, hclosed, hrange⟩ := hρ x
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ.toRingHom)) := hclosed
    have hc : Topology.IsClosedEmbedding (PrimeSpectrum.comap ρ.toRingHom) :=
      (Spec.map (CommRingCat.ofHom ρ.toRingHom)).isClosedEmbedding
    rw [← hρδ _ ρ hrange, ← Set.image_singleton]
    exact hc.isClosedMap _ (IsLocalRing.isClosed_singleton_closedPoint _)
  have hdiag (q : PrimeSpectrum (algebra A)) :
      q ∈ closedPoints (PrimeSpectrum (algebra A)) ↔ (e q).val.1 = (e q).val.2 := by
    constructor
    · intro hq
      have hh : δ (e q).val.1 = q :=
        Set.mem_singleton_iff.mp ((hspecial q).mem_closed
          (mem_closedPoints_iff.mp hq) (Set.mem_singleton q))
      have hp := hδ (e q).val.1
      rw [hh] at hp
      exact (congrArg Prod.fst hp).trans (congrArg Prod.snd hp).symm
    · intro hq
      have hh : q = δ (e q).val.1 := by
        apply e.injective
        apply Subtype.ext
        rw [hδ]
        exact Prod.ext rfl hq.symm
      rw [hh]
      exact mem_closedPoints_iff.mpr (hδclosed _)
  have hcomponents (q : PrimeSpectrum (algebra A)) :
      connectedComponent q = {r | (e r).val.1 = (e q).val.1} := by
    apply Set.Subset.antisymm (fun r hr ↦ hcc_first hr)
    intro r hr
    have hh : ConnectedComponents.mk r = ConnectedComponents.mk q := by
      rw [(hspecial r).connectedComponents_mk_eq, (hspecial q).connectedComponents_mk_eq, hr]
    have hh' := ConnectedComponents.coe_eq_coe.mp hh
    rw [← hh']
    exact mem_connectedComponent
  have hclosed : IsClosed (closedPoints (PrimeSpectrum (algebra A))) := by
    have hcompl : (closedPoints (PrimeSpectrum (algebra A)))ᶜ =
        ⋃ f : A, {q | f ∈ (e q).val.1.asIdeal} ∩
          (PrimeSpectrum.comap (algebraMap A (algebra A))) ⁻¹' PrimeSpectrum.basicOpen f := by
      ext q
      simp only [Set.mem_compl_iff, hdiag, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_preimage, he]
      constructor
      · intro hne
        have hlt : (e q).val.2.asIdeal < (e q).val.1.asIdeal :=
          lt_of_le_of_ne (e q).property (fun h ↦ hne (PrimeSpectrum.ext h.symm))
        exact IsConcreteLE.exists_of_lt hlt
      · rintro ⟨f, hf, hnf⟩ h
        exact hnf (h ▸ hf)
    rw [← isOpen_compl_iff, hcompl]
    refine isOpen_iUnion fun f ↦ ?_
    have hf : IsOpen {q | f ∈ (e q).val.1.asIdeal} := by
      simpa only [Set.compl_ofPred, not_not] using (hclopen f).compl.isOpen
    exact hf.inter
      ((PrimeSpectrum.basicOpen f).isOpen.preimage (PrimeSpectrum.continuous_comap _))
  have hw : IsWLocalRing (algebra A) := by
    refine ⟨{ toSpectralSpace := inferInstance
              isClosed_closedPoints := hclosed
              eq_of_specializes := ?_ }⟩
    intro q c c' hc hc' hqc hqc'
    have hcdiag := (hdiag c).mp (mem_closedPoints_iff.mpr hc)
    have hc'diag := (hdiag c').mp (mem_closedPoints_iff.mpr hc')
    have heq := (hspec_first hqc).trans (hspec_first hqc').symm
    apply e.injective
    apply Subtype.ext
    exact Prod.ext heq (hcdiag.symm.trans (heq.trans hc'diag))
  have hff : Module.FaithfullyFlat A (algebra A) := by
    apply Module.FaithfullyFlat.of_comap_surjective
    intro x
    refine ⟨δ x, ?_⟩
    rw [he]
    exact congrArg Prod.snd (hδ x)
  have hhomeo : ∃ h : @Homeomorph (PrimeSpectrum A)
      (closedPoints (PrimeSpectrum (algebra A)))
      (constructibleTopology (PrimeSpectrum A)) inferInstance,
      ∀ x : PrimeSpectrum A, (e (h x).val).val = (x, x) := by
    have : CompactSpace (closedPoints (PrimeSpectrum (algebra A))) :=
      isCompact_iff_compactSpace.mp hclosed.isCompact
    have : T2Space (WithConstructibleTopology (PrimeSpectrum A)) :=
      patchT2 A
    let g : closedPoints (PrimeSpectrum (algebra A)) ≃
        WithConstructibleTopology (PrimeSpectrum A) :=
      { toFun := fun q ↦ WithTopology.toTopology _ (e q.val).val.1
        invFun := fun x ↦ ⟨δ x.ofTopology, mem_closedPoints_iff.mpr (hδclosed _)⟩
        left_inv := fun q ↦ by
          apply Subtype.ext
          apply e.injective
          apply Subtype.ext
          rw [hδ]
          exact Prod.ext rfl ((hdiag q.val).mp q.property)
        right_inv := fun x ↦ by
          apply WithTopology.ofTopology_injective
          exact congrArg Prod.fst (hδ x.ofTopology) }
    have hg : Continuous g :=
      @Continuous.comp _ (PrimeSpectrum A) _ _
        (constructibleTopology (PrimeSpectrum A)) _ _ _
        (WithTopology.continuous_toTopology _)
        (@Continuous.comp _ (PrimeSpectrum (algebra A)) (PrimeSpectrum A) _ _
          (constructibleTopology (PrimeSpectrum A)) _ _ hπ continuous_subtype_val)
    let H := g.toHomeomorphOfContinuousClosed hg hg.isClosedMap
    let T : @Homeomorph (PrimeSpectrum A)
        (WithConstructibleTopology (PrimeSpectrum A))
        (constructibleTopology (PrimeSpectrum A)) inferInstance :=
      @Homeomorph.mk _ _ (constructibleTopology (PrimeSpectrum A)) _
        (WithTopology.equiv _ _).symm (WithTopology.continuous_toTopology _)
        (WithTopology.continuous_ofTopology _)
    refine ⟨@Homeomorph.trans _ _ _ (constructibleTopology (PrimeSpectrum A)) _ _ T H.symm, ?_⟩
    intro x
    exact hδ x
  exact ⟨e, he, hlocal, hπ, hcomponents, hρ, hdiag, hclosed, hhomeo, hff, hw⟩

end PrincipalWLocalization
