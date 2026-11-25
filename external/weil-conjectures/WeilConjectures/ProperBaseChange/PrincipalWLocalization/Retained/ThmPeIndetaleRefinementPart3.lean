/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.Retained.ThmPeIndetaleRefinementPart2Supplement3
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart2Supplement
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability

/-! # Properties of the retained localization

Source: blueprint, proper base change, order 1225, Properties of the retained localization
(blueprint: theorem-existence-contractible-covers--1).
-/

@[expose] public section

universe u

namespace PrincipalWLocalization.Retained

variable {R : Type u} [CommRing R]

/-- The canonical composite `R → R^w → R_[T]`.
Source: blueprint order 1225 (blueprint: theorem-existence-contractible-covers--1). -/
noncomputable def structuralMap (T : Set (PrimeSpectrum R)) (hT : IsClosed T) :
    R →+* algebra T hT :=
  (algebraMap (PrincipalWLocalization.algebra R) (algebra T hT)).comp
    (algebraMap R (PrincipalWLocalization.algebra R))

private noncomputable def partAt (i : Index R) (x : PrimeSpectrum R) : i.parts :=
  (i.partition x).choose

private theorem partAt_mem (i : Index R) (x : PrimeSpectrum R) : x ∈ (partAt i x).val :=
  (i.partition x).choose_spec.1

private theorem parent_partAt {i j : Index R} (h : i ≤ j) (x : PrimeSpectrum R) :
    parent h (partAt j x) = partAt i x := by
  apply (i.partition x).choose_spec.2
  exact ((h (partAt j x)).choose_spec.1) (partAt_mem j x)

private noncomputable def evalFactorAt (i : Index R) (E : i.parts) (x : PrimeSpectrum R)
    (hx : x ∈ E.val) : Localization.Away (i.denominator E) →ₐ[R]
      Localization.AtPrime x.asIdeal :=
  IsLocalization.Away.liftAlgHom (i.denominator E)
    (f := Algebra.ofId R (Localization.AtPrime x.asIdeal))
    (IsLocalization.map_units (Localization.AtPrime x.asIdeal)
      (M := x.asIdeal.primeCompl) ⟨i.denominator E, i.nonvanishing E hx⟩)

private noncomputable def evalFactor (i : Index R) (x : PrimeSpectrum R) :
    Localization.Away (i.denominator (partAt i x)) →ₐ[R]
      Localization.AtPrime x.asIdeal :=
  evalFactorAt i (partAt i x) x (partAt_mem i x)

private noncomputable def evalStage (i : Index R) (x : PrimeSpectrum R) :
    Stage i →ₐ[R] Localization.AtPrime x.asIdeal :=
  (evalFactor i x).comp (Pi.evalAlgHom R _ (partAt i x))

private theorem evalFactorAt_compatible {i j : Index R} (h : i ≤ j)
    (E : i.parts) (F : j.parts) (x : PrimeSpectrum R) (hxE : x ∈ E.val) (hxF : x ∈ F.val)
    (hpar : parent h F = E) (b : Stage i) :
    evalFactorAt j F x hxF ((PrincipalWLocalization.transition h b) F) =
      evalFactorAt i E x hxE (b E) := by
  subst E
  let φ : Localization.Away (i.denominator (parent h F)) →ₐ[R]
      Localization.Away (j.denominator F) :=
    IsLocalization.Away.liftAlgHom (i.denominator (parent h F))
      (f := Algebra.ofId R (Localization.Away (j.denominator F)))
      (IsLocalization.Away.isUnit_of_dvd _ (parent_dvd h F))
  have heq : (evalFactorAt j F x hxF).comp φ = evalFactorAt i (parent h F) x hxE :=
    (IsLocalization.algHom_subsingleton
      (Submonoid.powers (i.denominator (parent h F)))).elim _ _
  exact DFunLike.congr_fun heq (b (parent h F))

private theorem evalStage_compatible {i j : Index R} (h : i ≤ j) (x : PrimeSpectrum R) :
    (evalStage j x).comp (PrincipalWLocalization.transition h) = evalStage i x := by
  ext b
  exact evalFactorAt_compatible h (partAt i x) (partAt j x) x
    (partAt_mem i x) (partAt_mem j x) (parent_partAt h x) b

private noncomputable def evaluation (x : PrimeSpectrum R) :
    PrincipalWLocalization.algebra R →ₐ[R] Localization.AtPrime x.asIdeal :=
  (CategoryTheory.Limits.colimit.desc (diagram (A := R))
    { pt := CommAlgCat.of R (Localization.AtPrime x.asIdeal)
      ι :=
        { app := fun i ↦ CommAlgCat.ofHom (evalStage i x)
          naturality := by
            intro i j h
            apply CommAlgCat.hom_ext
            exact evalStage_compatible h.le x } }).hom

private theorem evaluation_ι (i : Index R) (x : PrimeSpectrum R) (b : Stage i) :
    evaluation x ((CategoryTheory.Limits.colimit.ι (diagram (A := R)) i).hom b) =
      evalStage i x b := by
  change ((CategoryTheory.CategoryStruct.comp
    (CategoryTheory.Limits.colimit.ι (diagram (A := R)) i) _).hom b) = _
  rw [CategoryTheory.Limits.colimit.ι_desc]
  rfl

private theorem evaluation_selector (E : Set (PrimeSpectrum R))
    (hE : Topology.IsConstructible E) (x : PrimeSpectrum R) :
    evaluation x (selector E hE) = @ite _ (x ∈ E) (Classical.propDecidable _) 1 0 := by
  classical
  unfold selector
  rw [evaluation_ι]
  have hparts : (partAt (selectorIndex E hE) x).val = E ∨
      (partAt (selectorIndex E hE) x).val = Eᶜ := by
    have h := (partAt (selectorIndex E hE) x).property
    change _ ∈ parts E at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (Finset.mem_filter.mp h).1
  have hsub : (partAt (selectorIndex E hE) x).val ⊆ E ↔ x ∈ E := by
    constructor
    · exact fun h ↦ h (partAt_mem _ _)
    · intro hx
      rcases hparts with h | h
      · exact h.subset
      · have hmem := partAt_mem (selectorIndex E hE) x
        rw [h] at hmem
        exact (hmem hx).elim
  change evalFactor _ x (if (partAt (selectorIndex E hE) x).val ⊆ E then 1 else 0) = _
  by_cases hx : x ∈ E
  · simp only [ite_eq_left hx, ite_eq_left (hsub.mpr hx), map_one]
  · simp only [ite_eq_right hx, ite_eq_right (fun h ↦ hx (hsub.mp h)), map_zero]

private theorem evaluation_surjective (x : PrimeSpectrum R) :
    Function.Surjective (evaluation x) := by
  classical
  intro z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq x.asIdeal.primeCompl z
  let D : Set (PrimeSpectrum R) := PrimeSpectrum.basicOpen s.val
  let i : Index R :=
    { selectorIndex D PrimeSpectrum.isConstructible_basicOpen with
      denominator := fun E ↦ if E.val ⊆ D then s.val else 1
      nonvanishing := by
        intro E y hy
        by_cases h : E.val ⊆ D
        · simpa only [ite_eq_left h] using h hy
        · simp only [ite_eq_right h, PrimeSpectrum.basicOpen_one,
            TopologicalSpace.Opens.coe_top, Set.mem_univ] }
  have hparts : (partAt i x).val = D ∨ (partAt i x).val = Dᶜ := by
    have h := (partAt i x).property
    change _ ∈ parts D at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (Finset.mem_filter.mp h).1
  have hsub : (partAt i x).val ⊆ D := by
    rcases hparts with h | h
    · exact h.subset
    · have hmem := partAt_mem i x
      rw [h] at hmem
      exact (hmem s.property).elim
  have hden : i.denominator (partAt i x) = s.val := ite_eq_left hsub
  let b : Stage i := fun E ↦ IsLocalization.mk' (Localization.Away (i.denominator E))
    a ⟨i.denominator E, Submonoid.mem_powers _⟩
  refine ⟨(CategoryTheory.Limits.colimit.ι (diagram (A := R)) i).hom b, ?_⟩
  rw [evaluation_ι]
  change evalFactor i x (b (partAt i x)) = _
  apply (IsLocalization.eq_mk'_iff_mul_eq).mpr
  have hb : algebraMap R (Localization.Away (i.denominator (partAt i x))) a =
      algebraMap R _ (i.denominator (partAt i x)) * b (partAt i x) := by
    exact (IsLocalization.mk'_spec (Localization.Away (i.denominator (partAt i x))) a
      ⟨i.denominator (partAt i x), Submonoid.mem_powers _⟩).symm.trans (mul_comm _ _)
  have hev := congrArg (evalFactor i x) hb
  calc
    evalFactor i x (b (partAt i x)) * algebraMap R _ s.val =
        algebraMap R _ s.val * evalFactor i x (b (partAt i x)) := mul_comm _ _
    _ = algebraMap R _ a := by
      simpa only [map_mul, AlgHom.commutes, hden] using hev.symm

private theorem indPrincipalZariski (T : Set (PrimeSpectrum R)) (hT : IsClosed T) :
    @Algebra.IsIndPrincipalZariski R (algebra T hT) _ _ (structuralMap T hT).toAlgebra := by
  have hret : Algebra.IsIndPrincipalZariski (PrincipalWLocalization.algebra R) (algebra T hT) := by
    refine ⟨Neighborhood T, inferInstance, inferInstance,
      CategoryTheory.Limits.ColimitPresentation.colimit (localizationDiagram T), ?_⟩
    intro E
    refine ⟨1, fun _ ↦ selector E.val E.property.1, ?_⟩
    exact ⟨(AlgEquiv.funUnique (PrincipalWLocalization.algebra R) (Fin 1)
      (Localization.Away (selector E.val E.property.1))).symm⟩
  exact RingHom.indEtale_principalZariski_stability.2.2.2.1
    (algebraMap R (PrincipalWLocalization.algebra R))
    (algebraMap (PrincipalWLocalization.algebra R) (algebra T hT))
    (by
      dsimp only
      rw [toAlgebra_algebraMap]
      exact PrincipalWLocalization.isIndPrincipalZariski)
    (by
      dsimp only
      rw [toAlgebra_algebraMap]
      exact hret)

private theorem surjective_toRetained (T : Set (PrimeSpectrum R)) (hT : IsClosed T) :
    Function.Surjective (algebraMap (PrincipalWLocalization.algebra R) (algebra T hT)) := by
  intro x
  obtain ⟨E, y, hy⟩ := CategoryTheory.Limits.Concrete.colimit_exists_rep (localizationDiagram T) x
  change Localization.Away (selector E.val E.property.1) at y
  obtain ⟨a, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
    (selector E.val E.property.1) (selector_idempotent E.val E.property.1) y
  refine ⟨a, ?_⟩
  change (CategoryTheory.Limits.colimit.ι (localizationDiagram T) E).hom
    (algebraMap _ (Localization.Away (selector E.val E.property.1)) a) = x at hy
  exact ((CategoryTheory.Limits.colimit.ι (localizationDiagram T) E).hom.commutes a).symm.trans hy

private theorem range_comap_eq_selectors (T : Set (PrimeSpectrum R)) (hT : IsClosed T) :
    Set.range (PrimeSpectrum.comap
      (algebraMap (PrincipalWLocalization.algebra R) (algebra T hT))) =
    {q | ∀ E : Neighborhood T, selector E.val E.property.1 ∉ q.asIdeal} := by
  set_option backward.isDefEq.respectTransparency false in
    unfold algebra
    ext q
    constructor
    · rintro ⟨p, rfl⟩ E he
      have hu := (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (selector E.val E.property.1))
        (selector E.val E.property.1)).map
          (CategoryTheory.Limits.colimit.ι (localizationDiagram T) E).hom
      have hu' : IsUnit (algebraMap (PrincipalWLocalization.algebra R) (algebra T hT)
          (selector E.val E.property.1)) := by
        change IsUnit (algebraMap _
          ((CategoryTheory.Limits.colimit (localizationDiagram T) : CommAlgCat _) : Type u) _)
        change IsUnit ((CategoryTheory.Limits.colimit.ι (localizationDiagram T) E).hom
          (algebraMap _ ((localizationDiagram T).obj E) (selector E.val E.property.1))) at hu
        simpa only [AlgHom.commutes] using hu
      exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem he hu')
    · intro hq
      let C := PrincipalWLocalization.algebra R
      let L := Localization.AtPrime q.asIdeal
      let maps (E : Neighborhood T) :
          Localization.Away (selector E.val E.property.1) →ₐ[C] L :=
        IsLocalization.Away.liftAlgHom (selector E.val E.property.1)
          (f := Algebra.ofId C L)
          (IsLocalization.map_units L (M := q.asIdeal.primeCompl)
            ⟨selector E.val E.property.1, hq E⟩)
      let c : CategoryTheory.Limits.Cocone (localizationDiagram T) :=
        { pt := CommAlgCat.of C L
          ι :=
            { app := fun E ↦ CommAlgCat.ofHom (maps E)
              naturality := by
                intro E F f
                apply CommAlgCat.hom_ext
                change (maps F).comp (transition f.le) = maps E
                exact (IsLocalization.algHom_subsingleton
                  (Submonoid.powers (selector E.val E.property.1))).elim _ _ } }
      let ρ : algebra T hT →ₐ[C] L :=
        (CategoryTheory.Limits.colimit.desc (localizationDiagram T) c).hom
      let p : PrimeSpectrum L := ⟨IsLocalRing.maximalIdeal L, inferInstance⟩
      refine ⟨PrimeSpectrum.comap ρ.toRingHom p, ?_⟩
      apply PrimeSpectrum.ext
      ext a
      change ρ (algebraMap C (algebra T hT) a) ∈ IsLocalRing.maximalIdeal L ↔ a ∈ q.asIdeal
      rw [ρ.commutes]
      exact IsLocalization.AtPrime.to_map_mem_maximal_iff L q.asIdeal a

private theorem mem_iff_neighborhoods (T : Set (PrimeSpectrum R)) (hT : IsClosed T)
    (x : PrimeSpectrum R) : (∀ E : Neighborhood T, x ∈ E.val) ↔ x ∈ T := by
  constructor
  · intro hx
    by_contra hxT
    obtain ⟨S, hS⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus T).mp hT
    have hnot : ¬S ⊆ (x.asIdeal : Set R) := by
      intro h
      apply hxT
      exact hS.symm ▸ h
    obtain ⟨f, hfS, hfx⟩ := Set.not_subset.mp hnot
    let E : Neighborhood T :=
      ⟨(PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))ᶜ,
        PrimeSpectrum.isConstructible_basicOpen.compl, by
          intro y hy
          simpa only [Set.mem_compl_iff, SetLike.mem_coe,
            PrimeSpectrum.mem_basicOpen, not_not] using
            (show y ∈ PrimeSpectrum.zeroLocus S from hS ▸ hy) hfS⟩
    have hxE := hx E
    change x ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))ᶜ at hxE
    exact hfx (by simpa only [Set.mem_compl_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      not_not] using hxE)
  · intro hx E
    exact E.property.2 hx

private theorem bijectiveOnStalks_of_principal {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (h : Algebra.IsIndPrincipalZariski A B) :
    (algebraMap A B).BijectiveOnStalks := by
  obtain ⟨I, _, _, P, hP⟩ := h
  apply RingHom.bijectiveOnStalks_algebraMap.mpr
  apply Algebra.BijectiveOnStalks.of_colimitPresentation P
  intro i
  obtain ⟨n, f, ⟨e⟩⟩ := hP i
  have hprod : (algebraMap A ((j : Fin n) → Localization.Away (f j))).BijectiveOnStalks := by
    apply RingHom.BijectiveOnStalks.pi
    intro j
    have : Algebra.IsStandardOpenImmersion A (Localization.Away (f j)) := ⟨f j, inferInstance⟩
    exact RingHom.BijectiveOnStalks.of_isStandardOpenImmersion A _
  have hcomp := hprod.comp e.symm.toRingEquiv.bijectiveOnStalks
  apply RingHom.bijectiveOnStalks_algebraMap.mp
  convert hcomp using 1
  ext a
  exact (e.symm.commutes a).symm

private theorem quotient_bijective_of_pairs {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.BijectiveOnStalks) (T : Set (PrimeSpectrum A))
    (e : PrimeSpectrum B ≃
      {p : PrimeSpectrum A × PrimeSpectrum A // p.1 ∈ T ∧ p.2.asIdeal ≤ p.1.asIdeal})
    (he : ∀ q, (e q).val.2 = PrimeSpectrum.comap f q)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set (PrimeSpectrum A)))
    (J : Ideal A) (hT : T = PrimeSpectrum.zeroLocus (J : Set A)) :
    Function.Bijective (Ideal.quotientMap (J.map f) f Ideal.le_comap_map) := by
  let g : PrimeSpectrum.zeroLocus (J.map f : Set B) →
      PrimeSpectrum.zeroLocus (J : Set A) := fun q ↦
    ⟨PrimeSpectrum.comap f q.val, (Ideal.map_le_iff_le_comap).mp q.property⟩
  have hdiag (q : PrimeSpectrum.zeroLocus (J.map f : Set B)) :
      (e q.val).val.1 = (e q.val).val.2 := by
    have hyT : (e q.val).val.2 ∈ T := by
      apply hT.symm ▸ (show (e q.val).val.2 ∈ PrimeSpectrum.zeroLocus (J : Set A) from ?_)
      rw [he]
      exact (g q).property
    have hymax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
      (hclosed _ hyT)
    exact (PrimeSpectrum.ext (hymax.eq_of_le (e q.val).val.1.isPrime.ne_top
      (e q.val).property.2)).symm
  have hg : Function.Bijective g := by
    constructor
    · intro q q' hq
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      apply Prod.ext
      · rw [hdiag q, hdiag q', he, he]
        exact congrArg Subtype.val hq
      · rw [he, he]
        exact congrArg Subtype.val hq
    · intro x
      have hxT : x.val ∈ T := hT.symm ▸ x.property
      let p := e.symm ⟨(x.val, x.val), hxT, le_rfl⟩
      have hp : PrimeSpectrum.comap f p = x.val := by
        rw [← he, Equiv.apply_symm_apply]
      refine ⟨⟨p, ?_⟩, ?_⟩
      · apply (Ideal.map_le_iff_le_comap).mpr
        change J ≤ (PrimeSpectrum.comap f p).asIdeal
        rw [hp]
        exact x.property
      · exact Subtype.ext hp
  let eA := J.primeSpectrumQuotientOrderIsoZeroLocus
  let eB := (J.map f).primeSpectrumQuotientOrderIsoZeroLocus
  let fbar := Ideal.quotientMap (J.map f) f Ideal.le_comap_map
  have hcomm : g ∘ eB = eA ∘ PrimeSpectrum.comap fbar := by
    funext q
    apply Subtype.ext
    change PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk (J.map f)) q) =
      PrimeSpectrum.comap (Ideal.Quotient.mk J) (PrimeSpectrum.comap fbar q)
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
    rw [Ideal.quotientMap_comp_mk]
  have hb : Function.Bijective (PrimeSpectrum.comap fbar) := by
    have hc : Function.Bijective (eA ∘ PrimeSpectrum.comap fbar) := by
      rw [← hcomm]
      exact hg.comp eB.bijective
    refine ⟨fun a b h ↦ hc.1 (congrArg eA h), ?_⟩
    intro p
    obtain ⟨q, hq⟩ := hc.2 (eA p)
    exact ⟨q, eA.injective hq⟩
  exact (hf.quotientMap J).bijective_of_bijective hb

private theorem closedPoints_homeomorph_of_range
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (j : Y → Z) (hj : Topology.IsClosedEmbedding j)
    (h : X ≃ₜ closedPoints Z) (T : Set X) (p : Z → X)
    (hp : ∀ x, p (h x).val = x) (hrange : Set.range j = {z | p z ∈ T}) :
    ∃ H : T ≃ₜ closedPoints Y, ∀ x : T, j (H x).val = (h x.val).val := by
  let l : closedPoints Y → closedPoints Z := fun y ↦
    ⟨j y.val, mem_closedPoints_iff.mpr (by
      simpa only [Set.image_singleton] using
        hj.isClosedMap _ (mem_closedPoints_iff.mp y.property))⟩
  have hl : Topology.IsEmbedding l :=
    (hj.isEmbedding.comp .subtypeVal).codRestrict _ _
  have hkT (y : closedPoints Y) : h.symm (l y) ∈ T := by
    have hmem : j y.val ∈ Set.range j := Set.mem_range_self y.val
    rw [hrange] at hmem
    have heq : p (j y.val) = h.symm (l y) := by
      simpa only [Homeomorph.apply_symm_apply] using hp (h.symm (l y))
    exact heq ▸ hmem
  let k : closedPoints Y → T := fun y ↦ ⟨h.symm (l y), hkT y⟩
  have hk : Topology.IsEmbedding k :=
    (h.symm.isEmbedding.comp hl).codRestrict _ _
  have hsurj : Function.Surjective k := by
    intro x
    have hmem : (h x.val).val ∈ Set.range j := by
      rw [hrange]
      change p (h x.val).val ∈ T
      rw [hp]
      exact x.property
    obtain ⟨y, hy⟩ := hmem
    have hyclosed : y ∈ closedPoints Y := mem_closedPoints_iff.mpr
      (hj.isEmbedding.isClosed_singleton_of_isClosed_image_singleton
        (hy ▸ mem_closedPoints_iff.mp (h x.val).property))
    refine ⟨⟨y, hyclosed⟩, ?_⟩
    apply Subtype.ext
    change h.symm (l ⟨y, hyclosed⟩) = x.val
    apply h.injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext hy
  let K : closedPoints Y ≃ₜ T := hk.toHomeomorphOfSurjective hsurj
  refine ⟨K.symm, ?_⟩
  intro x
  have hK : (k (K.symm x)).val = x.val := congrArg Subtype.val (K.apply_symm_apply x)
  calc
    j (K.symm x).val = (h ((k (K.symm x)).val)).val := by
      exact congrArg Subtype.val (h.apply_symm_apply (l (K.symm x))).symm
    _ = (h x.val).val := congrArg (fun x ↦ (h x).val) hK

/-- The retained localization is ind-Zariski, has the listed prime pairs and canonical local
rings, and under the closed-point hypothesis is w-local with patch closed-point space `T`.
The quotient assertion concerns the canonical map, not merely an abstract ring equivalence.
Source: blueprint order 1225 (blueprint: theorem-existence-contractible-covers--1).

Proof:
1. Express the retained algebra as the filtered colimit of the single principal selector
localizations. Compose this ind-principal-Zariski presentation with that of `R^w` using
lemma-stability.
2. Construct the evaluation map `R^w → R_x` directly from the finite product stages. Every
fraction comes from the stage with partition `D(s), V(s)` and denominators `s, 1`, so this
map is surjective. It sends the selector of `E` to one or zero according as `x ∈ E`.
Its closed point lies in the component with first coordinate `x`. Since the selector basic
open is clopen, it is constant on that component. Thus a selector avoids the prime `(x,y)`
exactly when `x ∈ E` (theorem-existence-contractible-covers--1).
3. Each idempotent localization map is surjective, so the map from `R^w` to the retained
algebra is surjective. Its spectrum is a closed subspace, consisting exactly of primes
avoiding every selector: for the converse, map the colimit to the ambient prime localization.
The intersection of all constructible supersets of `T` is `T`: for `x ∉ V(I)`, choose
`f ∈ I` outside `x`, and use `V(f)`. Restrict the ambient prime-pair equivalence to obtain
the stated retained pairs. Filtered colimits of finite products of principal localizations
are bijective on stalks, giving the canonical local-ring assertion.
4. W-locality descends along the surjection from `R^w`. Restrict the ambient homeomorphism
from the patch spectrum to its closed-point set along the retained closed embedding; its
range calculation gives the required homeomorphism and diagonal compatibility.
5. When `T=V(J)` consists of closed points, a quotient prime has `J ≤ y ≤ x`, so maximality
forces `y=x`. The canonical quotient spectrum map is therefore bijective. Bijectivity on
stalks descends to quotient maps, and the source library's
`RingHom.BijectiveOnStalks.bijective_of_bijective` then proves that the canonical quotient
ring map is bijective. No compact Hausdorff argument is needed. All constructions also
apply to the empty retained subset and to the zero ring.
-/
theorem properties (T : Set (PrimeSpectrum R)) (hT : IsClosed T) :
    @Algebra.IsIndPrincipalZariski R (algebra T hT) _ _ (structuralMap T hT).toAlgebra ∧
    (∃ e : PrimeSpectrum (algebra T hT) ≃
        {p : PrimeSpectrum R × PrimeSpectrum R // p.1 ∈ T ∧ p.2.asIdeal ≤ p.1.asIdeal},
      (∀ q : PrimeSpectrum (algebra T hT),
        ∃ hq : (e q).val.2.asIdeal = q.asIdeal.comap (structuralMap T hT),
          Function.Bijective (Localization.localRingHom (e q).val.2.asIdeal q.asIdeal
            (structuralMap T hT) hq)) ∧
      ((∀ x ∈ T, IsClosed ({x} : Set (PrimeSpectrum R))) →
        IsWLocalRing (algebra T hT) ∧
        (∃ h : @Homeomorph T (closedPoints (PrimeSpectrum (algebra T hT)))
            (TopologicalSpace.induced Subtype.val (constructibleTopology (PrimeSpectrum R)))
            inferInstance,
          ∀ x : T, (e (h x).val).val = (x.val, x.val)))) ∧
    ((∀ x ∈ T, IsClosed ({x} : Set (PrimeSpectrum R))) →
      ∀ J : Ideal R, T = PrimeSpectrum.zeroLocus (J : Set R) →
        Function.Bijective (Ideal.quotientMap (J.map (structuralMap T hT))
          (structuralMap T hT) Ideal.le_comap_map)) := by
  classical
  obtain ⟨e₀, hbase, _, _, hcomp, _, hclosed, _,
    ⟨h₀, hdiag⟩, _, hw⟩ := PrincipalWLocalization.points R
  have hsupp : ∀ (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E)
      (q : PrimeSpectrum (PrincipalWLocalization.algebra R)),
      selector E hE ∉ q.asIdeal ↔ (e₀ q).val.1 ∈ E := by
    intro E hE q
    let x := (e₀ q).val.1
    let L := Localization.AtPrime x.asIdeal
    let m : PrimeSpectrum L := ⟨IsLocalRing.maximalIdeal L, inferInstance⟩
    let qx := PrimeSpectrum.comap (evaluation x).toRingHom m
    have hqxclosed : qx ∈ closedPoints (PrimeSpectrum (PrincipalWLocalization.algebra R)) := by
      apply mem_closedPoints_iff.mpr
      exact PrimeSpectrum.comap_singleton_isClosed_of_surjective L (evaluation x).toRingHom
        (evaluation_surjective x) m
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal m).mpr inferInstance)
    have hqxbase : PrimeSpectrum.comap
        (algebraMap R (PrincipalWLocalization.algebra R)) qx = x := by
      apply PrimeSpectrum.ext
      ext a
      change evaluation x (algebraMap R (PrincipalWLocalization.algebra R) a) ∈
        IsLocalRing.maximalIdeal L ↔ a ∈ x.asIdeal
      rw [(evaluation x).commutes]
      exact IsLocalization.AtPrime.to_map_mem_maximal_iff L x.asIdeal a
    have hfirst : (e₀ qx).val.1 = x :=
      ((hclosed qx).mp hqxclosed).trans ((hbase qx).symm.trans hqxbase)
    have hqxcomp : qx ∈ connectedComponent q := by
      rw [hcomp q]
      exact hfirst
    have hclopen : IsClopen (PrimeSpectrum.basicOpen (selector E hE) :
        Set (PrimeSpectrum (PrincipalWLocalization.algebra R))) := by
      apply PrimeSpectrum.isClopen_basicOpen_of_mul_add (selector E hE) (1 - selector E hE)
      · rw [mul_sub, mul_one, selector_idempotent E hE, sub_self]
      · rw [← add_sub_assoc, add_sub_cancel_left]
    have hequiv : selector E hE ∉ q.asIdeal ↔ selector E hE ∉ qx.asIdeal := by
      change q ∈ PrimeSpectrum.basicOpen (selector E hE) ↔
        qx ∈ PrimeSpectrum.basicOpen (selector E hE)
      constructor
      · exact fun h ↦ hclopen.connectedComponent_subset h hqxcomp
      · intro h
        by_contra hn
        exact (hclopen.compl.connectedComponent_subset hn hqxcomp) h
    rw [hequiv]
    change evaluation x (selector E hE) ∉ IsLocalRing.maximalIdeal L ↔ x ∈ E
    rw [evaluation_selector]
    by_cases hx : x ∈ E
    · rw [ite_eq_left hx]
      exact iff_of_true
        (fun h ↦ m.isPrime.ne_top (m.asIdeal.eq_top_of_isUnit_mem h isUnit_one)) hx
    · rw [ite_eq_right hx]
      exact iff_of_false (fun h ↦ h (Ideal.zero_mem _)) hx
  let C := PrincipalWLocalization.algebra R
  let B := algebra T hT
  let f : C →+* B := algebraMap C B
  let j := PrimeSpectrum.comap f
  have hj : Topology.IsClosedEmbedding j :=
    PrimeSpectrum.isClosedEmbedding_comap_of_surjective B f (surjective_toRetained T hT)
  have hrange : Set.range j = {q | (e₀ q).val.1 ∈ T} := by
    rw [range_comap_eq_selectors T hT]
    ext q
    change (∀ E : Neighborhood T, selector E.val E.property.1 ∉ q.asIdeal) ↔ _
    simp_rw [hsupp]
    exact mem_iff_neighborhoods T hT _
  have hjT (q : PrimeSpectrum B) : (e₀ (j q)).val.1 ∈ T := by
    have := Set.mem_range_self q (f := j)
    rwa [hrange] at this
  let e : PrimeSpectrum B ≃
      {p : PrimeSpectrum R × PrimeSpectrum R // p.1 ∈ T ∧ p.2.asIdeal ≤ p.1.asIdeal} :=
    Equiv.ofBijective (fun q ↦ ⟨(e₀ (j q)).val, hjT q, (e₀ (j q)).property⟩) (by
      constructor
      · intro a b hab
        have hval : (e₀ (j a)).val = (e₀ (j b)).val :=
          congrArg (fun p ↦ p.val) hab
        exact hj.injective (e₀.injective (Subtype.ext hval))
      · rintro ⟨p, hpT, hple⟩
        have hmem : e₀.symm ⟨p, hple⟩ ∈ Set.range j := by
          rw [hrange]
          change (e₀ (e₀.symm ⟨p, hple⟩)).val.1 ∈ T
          simpa only [Equiv.apply_symm_apply] using hpT
        obtain ⟨q, hq⟩ := hmem
        refine ⟨q, ?_⟩
        apply Subtype.ext
        change (e₀ (j q)).val = p
        rw [hq, Equiv.apply_symm_apply])
  have he (q : PrimeSpectrum B) : (e q).val.2 = PrimeSpectrum.comap (structuralMap T hT) q := by
    change (e₀ (j q)).val.2 = _
    rw [← hbase]
    exact (PrimeSpectrum.comap_comp_apply _ _ q).symm
  have hz := indPrincipalZariski T hT
  have hstalk : (structuralMap T hT).BijectiveOnStalks := by
    let _ := (structuralMap T hT).toAlgebra
    exact bijectiveOnStalks_of_principal hz
  refine ⟨hz, ⟨e, ?_, ?_⟩, ?_⟩
  · intro q
    have hq := congrArg PrimeSpectrum.asIdeal (he q)
    exact ⟨hq, hstalk.localRingHom_of_eq hq⟩
  · intro _
    have := hw
    refine ⟨IsWLocalRing.of_surjective (surjective_toRetained T hT), ?_⟩
    obtain ⟨H, hH⟩ := @closedPoints_homeomorph_of_range
      (PrimeSpectrum R) (PrimeSpectrum B) (PrimeSpectrum C)
      (constructibleTopology (PrimeSpectrum R)) inferInstance inferInstance
      j hj h₀ T (fun q ↦ (e₀ q).val.1)
      (fun x ↦ congrArg Prod.fst (hdiag x)) hrange
    refine ⟨H, ?_⟩
    intro x
    change (e₀ (j (H x).val)).val = (x.val, x.val)
    rw [hH]
    exact hdiag x.val
  · intro hclosedT J hTJ
    exact quotient_bijective_of_pairs (structuralMap T hT) hstalk T e he hclosedT J hTJ

end PrincipalWLocalization.Retained
