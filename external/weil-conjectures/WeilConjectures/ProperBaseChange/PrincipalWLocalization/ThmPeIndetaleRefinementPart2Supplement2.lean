/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart2
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Prime charts of the principal w-localization

Source: blueprint order 1223, proof steps 1–7
(blueprint: lem-weil-pbc-principal-w-localization-prime-charts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrincipalWLocalization

variable {A : Type u} [CommRing A]

/-- The prime over `(x,y)` is the inverse image of the prime of `A_x` contracting to `y`.
This uses the explicit evaluation map and the localization prime correspondence.
Source: blueprint order 1223, step 3
(blueprint: lem-weil-pbc-principal-w-localization-prime-charts). -/
noncomputable def pairPoint (p :
    {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal}) :
    PrimeSpectrum (algebra A) :=
  PrimeSpectrum.comap (evaluation p.val.1).toRingHom
    ((IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime p.val.1.asIdeal) p.val.1.asIdeal).symm ⟨p.val.2, p.property⟩)

private theorem evaluation_comp (x : PrimeSpectrum A) :
    (evaluation x).toRingHom.comp (algebraMap A (algebra A)) =
      algebraMap A (Localization.AtPrime x.asIdeal) := by
  ext a
  exact (evaluation x).commutes a

private theorem pairPoint_contraction (p :
    {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal}) :
    PrimeSpectrum.comap (algebraMap A (algebra A)) (pairPoint p) = p.val.2 := by
  unfold pairPoint
  rw [← PrimeSpectrum.comap_comp_apply, evaluation_comp]
  exact congrArg Subtype.val
    ((IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime p.val.1.asIdeal) p.val.1.asIdeal).apply_symm_apply
        ⟨p.val.2, p.property⟩)

private noncomputable def stagePoint (q : PrimeSpectrum (algebra A)) (i : Index A) :
    (E : i.parts) × PrimeSpectrum (Localization.Away (i.denominator E)) :=
  (Equiv.ofBijective
    (PrimeSpectrum.sigmaToPi (fun E : i.parts ↦ Localization.Away (i.denominator E)))
    (PrimeSpectrum.sigmaToPi_bijective _)).symm
      (PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom q)

private theorem stagePoint_spec (q : PrimeSpectrum (algebra A)) (i : Index A) :
    PrimeSpectrum.sigmaToPi (fun E : i.parts ↦ Localization.Away (i.denominator E))
      (stagePoint q i) =
      PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom q :=
  (Equiv.ofBijective _ (PrimeSpectrum.sigmaToPi_bijective
    (fun E : i.parts ↦ Localization.Away (i.denominator E)))).apply_symm_apply _

private theorem stagePoint_parent (q : PrimeSpectrum (algebra A)) {i j : Index A}
    (h : i ≤ j) : parent h (stagePoint q j).1 = (stagePoint q i).1 := by
  let F := (stagePoint q j).1
  let p := (stagePoint q j).2
  let f : Localization.Away (i.denominator (parent h F)) →ₐ[A]
      Localization.Away (j.denominator F) :=
    IsLocalization.Away.liftAlgHom _ (f := Algebra.ofId A _)
      (IsLocalization.Away.isUnit_of_dvd _ (parent_dvd h F))
  have hh : PrimeSpectrum.sigmaToPi
      (fun E : i.parts ↦ Localization.Away (i.denominator E))
      ⟨parent h F, PrimeSpectrum.comap f.toRingHom p⟩ =
      PrimeSpectrum.comap (transition h).toRingHom
        (PrimeSpectrum.sigmaToPi (fun E : j.parts ↦ Localization.Away (j.denominator E))
          (stagePoint q j)) := by
    rw [PrimeSpectrum.sigmaToPi_apply, PrimeSpectrum.sigmaToPi_apply,
      ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
    rfl
  rw [stagePoint_spec, ← PrimeSpectrum.comap_comp_apply] at hh
  have hw : (colimit.ι diagram j).hom.toRingHom.comp (transition h).toRingHom =
      (colimit.ι diagram i).hom.toRingHom := by
    exact congrArg (fun f ↦ f.hom.toRingHom) (colimit.w diagram (homOfLE h))
  rw [hw, ← stagePoint_spec] at hh
  exact congrArg Sigma.fst ((PrimeSpectrum.sigmaToPi_bijective _).injective hh)

private theorem stagePoint_contraction (q : PrimeSpectrum (algebra A)) (i : Index A) :
    PrimeSpectrum.comap (algebraMap A
      (Localization.Away (i.denominator (stagePoint q i).1))) (stagePoint q i).2 =
      PrimeSpectrum.comap (algebraMap A (algebra A)) q := by
  calc
    _ = PrimeSpectrum.comap (algebraMap A (Stage i))
        (PrimeSpectrum.sigmaToPi
          (fun E : i.parts ↦ Localization.Away (i.denominator E)) (stagePoint q i)) := by
      rw [PrimeSpectrum.sigmaToPi_apply, ← PrimeSpectrum.comap_comp_apply]
      rfl
    _ = PrimeSpectrum.comap (algebraMap A (Stage i))
        (PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom q) := by
      rw [stagePoint_spec]
    _ = _ := by
      rw [← PrimeSpectrum.comap_comp_apply]
      congr 1
      ext a
      exact (colimit.ι diagram i).hom.commutes a

private theorem stagePoint_subset (q : PrimeSpectrum (algebra A)) {i j : Index A}
    (h : i ≤ j) : (stagePoint q j).1.val ⊆ (stagePoint q i).1.val := by
  have hh := (Classical.choose_spec (h (stagePoint q j).1)).1
  change (stagePoint q j).1.val ⊆ (parent h (stagePoint q j).1).val at hh
  rwa [stagePoint_parent q h] at hh

private theorem exists_selected_point (q : PrimeSpectrum (algebra A)) :
    ∃ x : PrimeSpectrum A, ∀ i : Index A, partAt i x = (stagePoint q i).1 := by
  classical
  let S : Index A → Set (WithConstructibleTopology (PrimeSpectrum A)) :=
    fun i ↦ WithTopology.ofTopology ⁻¹' (stagePoint q i).1.val
  have hclosed (i : Index A) : IsClosed (S i) := by
    rw [WithConstructibleTopology.isClosed_iff]
    exact (i.constructible _ (stagePoint q i).1.property).isClopen_constructibleTopology.1
  have hnonempty (i : Index A) : (S i).Nonempty := by
    obtain ⟨x, hx⟩ := i.nonempty _ (stagePoint q i).1.property
    exact ⟨WithTopology.toTopology _ x, hx⟩
  have hdir : Directed (· ⊇ ·) S := by
    intro i j
    refine ⟨IsFiltered.max i j, ?_, ?_⟩
    · intro x hx
      exact stagePoint_subset q (IsFiltered.leftToMax i j).le hx
    · intro x hx
      exact stagePoint_subset q (IsFiltered.rightToMax i j).le hx
  have : Nonempty (Index A) := IsFiltered.nonempty
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S
    hdir hnonempty (fun i ↦ (hclosed i).isCompact) hclosed
  refine ⟨x.ofTopology, fun i ↦ partAt_eq i _ _ (Set.mem_iInter.mp hx i)⟩

private theorem cutIndex_partAt (E : Set (PrimeSpectrum A))
    (hE : Topology.IsConstructible E) (f : A) (hf : E ⊆ PrimeSpectrum.basicOpen f)
    (x : PrimeSpectrum A) :
    (partAt (cutIndex E hE f hf) x).val = E ↔ x ∈ E := by
  classical
  constructor
  · intro h
    exact h ▸ mem_partAt _ x
  · intro hx
    let F : (cutIndex E hE f hf).parts :=
      ⟨E, Finset.mem_filter.mpr ⟨by simp, ⟨x, hx⟩⟩⟩
    exact congrArg Subtype.val (partAt_eq _ x F hx)

private theorem contraction_le_selected (q : PrimeSpectrum (algebra A)) (x : PrimeSpectrum A)
    (hx : ∀ i : Index A, partAt i x = (stagePoint q i).1) :
    (PrimeSpectrum.comap (algebraMap A (algebra A)) q).asIdeal ≤ x.asIdeal := by
  intro f hfy
  by_contra hfx
  let E : Set (PrimeSpectrum A) := PrimeSpectrum.basicOpen f
  have hE : Topology.IsConstructible E :=
    (PrimeSpectrum.isCompact_basicOpen f).isConstructible (PrimeSpectrum.basicOpen f).isOpen
  let i := cutIndex E hE f Set.Subset.rfl
  have hpart : (stagePoint q i).1.val = E := by
    rw [← hx i]
    exact (cutIndex_partAt E hE f Set.Subset.rfl x).mpr hfx
  have hden : i.denominator (stagePoint q i).1 = f := by
    change (if (stagePoint q i).1.val = E then f else 1) = f
    rw [ite_eq_left hpart]
  have hnot : i.denominator (stagePoint q i).1 ∉
      (PrimeSpectrum.comap (algebraMap A (algebra A)) q).asIdeal := by
    rw [← stagePoint_contraction q i]
    change algebraMap A (Localization.Away (i.denominator (stagePoint q i).1))
      (i.denominator (stagePoint q i).1) ∉ (stagePoint q i).2.asIdeal
    exact Ideal.notMem_of_isUnit _
      (IsLocalization.Away.algebraMap_isUnit (i.denominator (stagePoint q i).1))
  exact hnot (hden.symm ▸ hfy)

open Classical in
private noncomputable def characteristic (E : Set (PrimeSpectrum A))
    (hE : Topology.IsConstructible E) : algebra A :=
  let i := cutIndex E hE 1 (by simp)
  (colimit.ι diagram i).hom (fun F ↦ if F.val = E then 1 else 0)

open Classical in
private theorem evaluation_characteristic (E : Set (PrimeSpectrum A))
    (hE : Topology.IsConstructible E) (x : PrimeSpectrum A) :
    evaluation x (characteristic E hE) = if x ∈ E then 1 else 0 := by
  classical
  rw [characteristic, evaluation_ι]
  change partToLocal _ x (if (partAt _ x).val = E then 1 else 0) = _
  simp only [cutIndex_partAt]
  split_ifs <;> simp

private theorem pairPoint_characteristic (E : Set (PrimeSpectrum A))
    (hE : Topology.IsConstructible E)
    (p : {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal}) :
    characteristic E hE ∉ (pairPoint p).asIdeal ↔ p.val.1 ∈ E := by
  classical
  let P := (IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.val.1.asIdeal) p.val.1.asIdeal).symm ⟨p.val.2, p.property⟩
  change evaluation p.val.1 (characteristic E hE) ∉ P.asIdeal ↔ _
  rw [evaluation_characteristic]
  split_ifs with hx
  · exact iff_of_true P.isPrime.one_notMem hx
  · exact iff_of_false (fun h ↦ h P.asIdeal.zero_mem) hx

private theorem stagePoint_pairPoint
    (p : {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal})
    (i : Index A) : (stagePoint (pairPoint p) i).1 = partAt i p.val.1 := by
  let P := (IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.val.1.asIdeal) p.val.1.asIdeal).symm ⟨p.val.2, p.property⟩
  have hh : PrimeSpectrum.sigmaToPi
      (fun E : i.parts ↦ Localization.Away (i.denominator E))
      ⟨partAt i p.val.1, PrimeSpectrum.comap (partToLocal i p.val.1).toRingHom P⟩ =
      PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom (pairPoint p) := by
    rw [PrimeSpectrum.sigmaToPi_apply, ← PrimeSpectrum.comap_comp_apply]
    unfold pairPoint
    rw [← PrimeSpectrum.comap_comp_apply]
    have hcomp : (partToLocal i p.val.1).toRingHom.comp
        (Pi.evalRingHom (fun E : i.parts ↦ Localization.Away (i.denominator E))
          (partAt i p.val.1)) =
        (evaluation p.val.1).toRingHom.comp (colimit.ι diagram i).hom.toRingHom := by
      apply RingHom.ext
      intro b
      exact (evaluation_ι p.val.1 i b).symm
    rw [hcomp]
  rw [← stagePoint_spec] at hh
  exact (congrArg Sigma.fst ((PrimeSpectrum.sigmaToPi_bijective _).injective hh)).symm

private theorem stagePoint_eq_of_same_part (q r : PrimeSpectrum (algebra A)) (i : Index A)
    (hpart : (stagePoint q i).1 = (stagePoint r i).1)
    (hcontraction : PrimeSpectrum.comap (algebraMap A (algebra A)) q =
      PrimeSpectrum.comap (algebraMap A (algebra A)) r) :
    stagePoint q i = stagePoint r i := by
  have hcq := stagePoint_contraction q i
  have hcr := stagePoint_contraction r i
  generalize hq : stagePoint q i = Q at *
  generalize hr : stagePoint r i = R at *
  rcases Q with ⟨E, P⟩
  rcases R with ⟨F, Q⟩
  dsimp only at hpart hcq hcr
  subst F
  have heq : P = Q := PrimeSpectrum.localization_comap_injective
    (Localization.Away (i.denominator E)) (Submonoid.powers (i.denominator E))
      (hcq.trans (hcontraction.trans hcr.symm))
  rw [heq]

private theorem eq_of_stagePoint_eq (q r : PrimeSpectrum (algebra A))
    (h : ∀ i : Index A, stagePoint q i = stagePoint r i) : q = r := by
  apply PrimeSpectrum.ext
  ext a
  obtain ⟨i, b, rfl⟩ := Concrete.isColimit_exists_rep diagram (colimit.isColimit diagram) a
  change b ∈ (PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom q).asIdeal ↔
    b ∈ (PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom r).asIdeal
  rw [← stagePoint_spec, ← stagePoint_spec, h]

private theorem pairPoint_surjective : Function.Surjective (pairPoint (A := A)) := by
  intro q
  obtain ⟨x, hx⟩ := exists_selected_point q
  let p : {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal} :=
    ⟨(x, PrimeSpectrum.comap (algebraMap A (algebra A)) q), contraction_le_selected q x hx⟩
  refine ⟨p, eq_of_stagePoint_eq _ _ fun i ↦ ?_⟩
  apply stagePoint_eq_of_same_part
  · exact (stagePoint_pairPoint p i).trans (hx i)
  · exact pairPoint_contraction p

private theorem pairPoint_injective : Function.Injective (pairPoint (A := A)) := by
  intro p r hpr
  apply Subtype.ext
  have hsecond : p.val.2 = r.val.2 := by
    rw [← pairPoint_contraction, ← pairPoint_contraction, hpr]
  apply Prod.ext _ hsecond
  apply PrimeSpectrum.ext
  ext f
  have hE : Topology.IsConstructible (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) :=
    (PrimeSpectrum.isCompact_basicOpen f).isConstructible (PrimeSpectrum.basicOpen f).isOpen
  have hh := (pairPoint_characteristic _ hE p).symm.trans
    ((congrArg (fun q : PrimeSpectrum (algebra A) ↦
      characteristic _ hE ∉ q.asIdeal) hpr).to_iff.trans (pairPoint_characteristic _ hE r))
  exact not_iff_not.mp hh

/-- The prime-pair correspondence, its contraction, the continuous patch coordinate, and the
closed affine charts of its fibres.

Source: blueprint order 1223, proof steps 1–7
(blueprint: lem-weil-pbc-principal-w-localization-prime-charts).
Proof:
1. A prime of each finite product selects exactly one factor, by the finite-product spectrum
bijection. Compatibility of the colimit injections makes the selected parts refine each other.
2. The selected constructible parts are closed in the compact patch space. They form a directed
nonempty family, so they have a common point `x`.
3. For `f` outside `x`, use the cut by `D(f)` with denominator `f`. The selected factor inverts
`f`, so the contracted prime `y` does not contain `f`. Thus `y` is contained in `x`.
4. The prime over `(x,y)` is obtained from the explicit evaluation to `A_x` and the localization
prime correspondence. Its selected part at each stage is the part containing `x`. Two primes
with the same selected parts and the same contraction coincide, since localization primes are
determined by contraction and every colimit element has a stage representative.
5. The characteristic tuple of any constructible set evaluates to one at its points and zero
elsewhere. Thus it distinguishes the first coordinates. Contraction distinguishes the second,
so the correspondence is bijective.
6. The preimage of a constructible set under the first-coordinate map is the basic open of its
characteristic element. In particular the preimages of the patch subbasis are open, proving
continuity.
7. The evaluation map to `A_x` is surjective by `evaluation_surjective`, so its spectrum map is a
closed immersion. The prime correspondence identifies its range exactly with first coordinate
`x`, by the localization prime correspondence. This includes the zero ring: then no prime is
present and the statements about individual fibres are vacuous. -/
theorem primeCharts (A : Type u) [CommRing A] :
    ∃ e : PrimeSpectrum (algebra A) ≃
      {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal},
      (∀ q, PrimeSpectrum.comap (algebraMap A (algebra A)) q = (e q).val.2) ∧
      (@Continuous (PrimeSpectrum (algebra A)) (PrimeSpectrum A) inferInstance
        (constructibleTopology (PrimeSpectrum A)) (fun q ↦ (e q).val.1)) ∧
      (∀ x : PrimeSpectrum A,
        ∃ ρ : algebra A →ₐ[A] Localization.AtPrime x.asIdeal,
          IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ.toRingHom)) ∧
          Set.range (PrimeSpectrum.comap ρ.toRingHom) = {q | (e q).val.1 = x}) := by
  classical
  let d := Equiv.ofBijective (pairPoint (A := A)) ⟨pairPoint_injective, pairPoint_surjective⟩
  let e := d.symm
  have hpq (q : PrimeSpectrum (algebra A)) : pairPoint (e q) = q := d.apply_symm_apply q
  have hep (p : {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal}) :
      e (pairPoint p) = p := d.symm_apply_apply p
  refine ⟨e, ?_, ?_, ?_⟩
  · intro q
    rw [← hpq q, pairPoint_contraction, hep]
  · have hchar (E : Set (PrimeSpectrum A)) (hE : Topology.IsConstructible E)
        (q : PrimeSpectrum (algebra A)) :
        characteristic E hE ∉ q.asIdeal ↔ (e q).val.1 ∈ E := by
      rw [← hpq q]
      exact (pairPoint_characteristic E hE (e q)).trans (by rw [hep])
    change @Continuous _ _ _ (TopologicalSpace.generateFrom _) (fun q ↦ (e q).val.1)
    rw [continuous_generateFrom_iff]
    intro E hE
    have hc : Topology.IsConstructible E := by
      rcases hE with hE | hE
      · exact hE.2.isConstructible hE.1
      · have hh := (hE.2.isConstructible hE.1.isOpen_compl).compl
        simpa only [compl_compl] using hh
    have hpre : (fun q ↦ (e q).val.1) ⁻¹' E =
        (PrimeSpectrum.basicOpen (characteristic E hc) : Set (PrimeSpectrum (algebra A))) := by
      ext q
      exact (hchar E hc q).symm
    rw [hpre]
    exact (PrimeSpectrum.basicOpen _).isOpen
  · intro x
    refine ⟨evaluation x, IsClosedImmersion.spec_of_surjective _ (evaluation_surjective x), ?_⟩
    ext q
    constructor
    · rintro ⟨P, rfl⟩
      let o := IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime x.asIdeal)
        x.asIdeal
      let p : {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal} :=
        ⟨(x, (o P).val), (o P).property⟩
      have hh : pairPoint p = PrimeSpectrum.comap (evaluation x).toRingHom P := by
        change PrimeSpectrum.comap (evaluation x).toRingHom (o.symm (o P)) = _
        rw [o.symm_apply_apply]
      rw [← hh]
      change (e (pairPoint p)).val.1 = x
      rw [hep]
    · intro hq
      have hh : q ∈ Set.range (PrimeSpectrum.comap (evaluation (e q).val.1).toRingHom) :=
        ⟨_, hpq q⟩
      simpa only [Set.mem_ofPred_eq] using (hq ▸ hh)

end PrincipalWLocalization
