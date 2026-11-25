/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart1Supplement3

/-! # Evaluation of the principal w-localization at a prime

Source: blueprint order 1223, proof step 6
(blueprint: lem-weil-pbc-principal-w-localization-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization

variable {A : Type u} [CommRing A]

/-- The unique part containing a prime. The partition property determines this choice uniquely.
Source: blueprint order 1223, steps 3 and 6
(blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
noncomputable def partAt (i : Index A) (x : PrimeSpectrum A) : i.parts :=
  (i.partition x).choose

/-- The chosen part contains the prime, by the partition property.
Source: blueprint order 1223 (blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
theorem mem_partAt (i : Index A) (x : PrimeSpectrum A) : x ∈ (partAt i x).val :=
  (i.partition x).choose_spec.1

/-- Uniqueness identifies the part containing the prime.
Source: blueprint order 1223 (blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
theorem partAt_eq (i : Index A) (x : PrimeSpectrum A) (E : i.parts)
    (h : x ∈ E.val) : partAt i x = E :=
  ((i.partition x).choose_spec.2 E h).symm

/-- The selected part of a refinement has as parent the selected original part.
Source: blueprint order 1223 (blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
theorem parent_partAt {i j : Index A} (h : i ≤ j) (x : PrimeSpectrum A) :
    parent h (partAt j x) = partAt i x := by
  apply (partAt_eq i x _ _).symm
  exact (Classical.choose_spec (h (partAt j x))).1 (mem_partAt j x)

/-- The canonical map from the localization at a part's denominator to the localization at a
prime in that part. Its denominator is outside the prime, hence becomes a unit.
Source: blueprint order 1223, step 6
(blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
noncomputable def partToLocal (i : Index A) (x : PrimeSpectrum A) :
    Localization.Away (i.denominator (partAt i x)) →ₐ[A] Localization.AtPrime x.asIdeal :=
  IsLocalization.Away.liftAlgHom _ (f := Algebra.ofId A _)
    ((IsLocalization.AtPrime.isUnit_to_map_iff _ x.asIdeal _).mpr
      (i.nonvanishing (partAt i x) (mem_partAt i x)))

/-- Evaluate a stage on its unique part containing the prime.
Source: blueprint order 1223, step 6
(blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
noncomputable def stageEvaluation (i : Index A) (x : PrimeSpectrum A) :
    Stage i →ₐ[A] Localization.AtPrime x.asIdeal :=
  (partToLocal i x).comp
    (Pi.evalAlgHom A (fun E : i.parts ↦ Localization.Away (i.denominator E)) (partAt i x))

/-- Evaluation commutes with refinement: the child containing the point has as its parent
precisely the old part containing the point, and localization maps are unique on `A`.
Source: blueprint order 1223 (blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
theorem stageEvaluation_transition {i j : Index A} (h : i ≤ j)
    (x : PrimeSpectrum A) :
    (stageEvaluation j x).comp (transition h) = stageEvaluation i x := by
  have hp := parent_partAt h x
  ext b
  change (partToLocal j x)
      ((IsLocalization.Away.liftAlgHom (i.denominator (parent h (partAt j x)))
        (f := Algebra.ofId A (Localization.Away (j.denominator (partAt j x))))
        (IsLocalization.Away.isUnit_of_dvd _ (parent_dvd h (partAt j x))))
          (b (parent h (partAt j x)))) = (partToLocal i x) (b (partAt i x))
  have hsame (E F : i.parts) (hEF : E = F)
      (f : Localization.Away (i.denominator E) →ₐ[A] Localization.AtPrime x.asIdeal)
      (g : Localization.Away (i.denominator F) →ₐ[A] Localization.AtPrime x.asIdeal) :
      f (b E) = g (b F) := by
    subst F
    have hfg : f = g := by
      apply IsLocalization.algHom_ext (Submonoid.powers (i.denominator E))
      ext
    rw [hfg]
  exact hsame _ _ hp
    ((partToLocal j x).comp
      (IsLocalization.Away.liftAlgHom (i.denominator (parent h (partAt j x)))
        (f := Algebra.ofId A (Localization.Away (j.denominator (partAt j x))))
        (IsLocalization.Away.isUnit_of_dvd _ (parent_dvd h (partAt j x)))))
    (partToLocal i x)

/-- The cocone of stage evaluations. It is concrete and uses only the localization universal
property, rather than a choice of a map from an existence statement.
Source: blueprint order 1223, step 6
(blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
noncomputable def evaluationCocone (x : PrimeSpectrum A) : Cocone (diagram (A := A)) where
  pt := CommAlgCat.of A (Localization.AtPrime x.asIdeal)
  ι :=
    { app i := CommAlgCat.ofHom (stageEvaluation i x)
      naturality {i j} h := by
        apply CommAlgCat.hom_ext
        exact stageEvaluation_transition h.le x }

/-- The canonical evaluation map to `A_x`, induced by the explicit stage maps.
Source: blueprint order 1223, step 6
(blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
noncomputable def evaluation (x : PrimeSpectrum A) :
    algebra A →ₐ[A] Localization.AtPrime x.asIdeal :=
  (colimit.desc diagram (evaluationCocone x)).hom

/-- Evaluation on a colimit representative is evaluation at its selected coordinate.
Source: blueprint order 1223 (blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
theorem evaluation_ι (x : PrimeSpectrum A) (i : Index A) (b : Stage i) :
    evaluation x ((colimit.ι diagram i).hom b) = stageEvaluation i x b :=
  DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (colimit.ι_desc (evaluationCocone x) i)) b

/-- The partition by a constructible set and its complement, omitting empty parts. The chosen
set has denominator `f`, and its complement has denominator one.
Source: blueprint order 1223, steps 5 and 6
(blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
noncomputable def cutIndex (E : Set (PrimeSpectrum A)) (hE : Topology.IsConstructible E)
    (f : A) (hf : E ⊆ PrimeSpectrum.basicOpen f) : Index A := by
  classical
  refine
    { parts := ({E, Eᶜ} : Finset (Set (PrimeSpectrum A))).filter Set.Nonempty
      nonempty := fun F hF ↦ (Finset.mem_filter.mp hF).2
      constructible := ?_
      partition := ?_
      denominator := fun F ↦ if F.val = E then f else 1
      nonvanishing := ?_ }
  · intro F hF
    rcases Finset.mem_insert.mp (Finset.mem_filter.mp hF).1 with rfl | hF
    · exact hE
    · rw [Finset.mem_singleton] at hF
      simpa only [hF] using hE.compl
  · intro p
    by_cases hp : p ∈ E
    · let F : ({E, Eᶜ} : Finset _).filter Set.Nonempty :=
        ⟨E, Finset.mem_filter.mpr ⟨by simp, ⟨p, hp⟩⟩⟩
      refine ⟨F, hp, ?_⟩
      intro G hG
      apply Subtype.ext
      rcases Finset.mem_insert.mp (Finset.mem_filter.mp G.property).1 with h | h
      · exact h
      · rw [Finset.mem_singleton] at h
        exact False.elim ((h ▸ hG) hp)
    · let F : ({E, Eᶜ} : Finset _).filter Set.Nonempty :=
        ⟨Eᶜ, Finset.mem_filter.mpr ⟨by simp, ⟨p, hp⟩⟩⟩
      refine ⟨F, hp, ?_⟩
      intro G hG
      apply Subtype.ext
      rcases Finset.mem_insert.mp (Finset.mem_filter.mp G.property).1 with h | h
      · exact False.elim (hp (h ▸ hG))
      · exact Finset.mem_singleton.mp h
  · intro F
    split_ifs with h
    · intro p hp
      apply hf
      simpa only [h] using hp
    · simpa only [PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top] using
        Set.subset_univ F.val

/-- The evaluation map is onto. Write an element of `A_x` as `a/s`, cut by `D(s)` and its
complement, and put that fraction on `D(s)`; the other coordinate is immaterial. Evaluation
takes this tuple to the required fraction. The denominator may vary with the index.
Source: blueprint order 1223, proof step 6
(blueprint: lem-weil-pbc-principal-w-localization-evaluation). -/
theorem evaluation_surjective (x : PrimeSpectrum A) : Function.Surjective (evaluation x) := by
  classical
  intro z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq x.asIdeal.primeCompl z
  let E : Set (PrimeSpectrum A) := PrimeSpectrum.basicOpen (s : A)
  have hE : Topology.IsConstructible E :=
    (PrimeSpectrum.isCompact_basicOpen (s : A)).isConstructible
      (PrimeSpectrum.basicOpen (s : A)).isOpen
  let i := cutIndex E hE s Set.Subset.rfl
  have hxE : x ∈ E := s.property
  let F : i.parts := ⟨E, Finset.mem_filter.mpr ⟨by simp, ⟨x, hxE⟩⟩⟩
  have hp : partAt i x = F := partAt_eq i x F hxE
  have hd : i.denominator (partAt i x) = (s : A) := by
    rw [hp]
    simp [i, F, cutIndex]
  let b : Stage i := fun G ↦
    algebraMap A _ a * IsLocalization.Away.invSelf (i.denominator G)
  refine ⟨(colimit.ι diagram i).hom b, ?_⟩
  rw [evaluation_ι, IsLocalization.eq_mk'_iff_mul_eq]
  change partToLocal i x (b (partAt i x)) * algebraMap A _ (s : A) = _
  rw [← hd, ← (partToLocal i x).commutes, ← map_mul]
  change partToLocal i x
    ((algebraMap A _ a * IsLocalization.Away.invSelf (i.denominator (partAt i x))) *
      algebraMap A _ (i.denominator (partAt i x))) = _
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf _),
    IsLocalization.Away.mul_invSelf, mul_one, AlgHom.commutes]

end PrincipalWLocalization
