/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.RingTheory.Idempotents

/-!
# Henselian local rings: étale retractions and idempotent lifting

Let `(R, 𝔪, κ)` be a local ring. We prove the following characterisations of henselian local
rings (Stacks, Lemma 04GG), following the blueprint.

* If simple roots of monic polynomials lift from `κ` to `R` (Mathlib's `HenselianLocalRing`),
  then every étale `R`-algebra `S` has, through every prime `q` over `𝔪` with trivial residue
  field extension, exactly one `R`-algebra retraction `τ : S →ₐ[R] R` with `τ⁻¹(𝔪) = q`.
* If étale `R`-algebras have such retractions, every finite `R`-algebra is a finite product of
  local rings.
* `R` is henselian (in Mathlib's sense of root lifting) if and only if idempotents of
  `B / 𝔪B` lift uniquely to `B` for every finite `R`-algebra `B`.

## Main results

- `IsLocalRing.existsUnique_algHom_comap_maximalIdeal_eq_of_forall_exists_isRoot`
- `HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_eq`
- `IsLocalRing.exists_algEquiv_pi_isLocalRing_of_forall_exists_algHom`
- `IsLocalRing.forall_existsUnique_isIdempotentElem_iff_forall_exists_isRoot`
- `HenselianLocalRing.iff_forall_existsUnique_isIdempotentElem`

## References

- Stacks Project, Lemma 10.153.3, <https://stacks.math.columbia.edu/tag/04GG>
-/

@[expose] public section

universe u v

open Polynomial IsLocalRing
open scoped TensorProduct

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **Finite algebras over a local ring: maximal ideals lie over the maximal ideal.** If `B` is
a finite `R`-algebra over the local ring `(R, 𝔪)`, every maximal ideal of `B` has preimage `𝔪`
in `R`.

(blueprint: `lem-weil-pbc-finite-algebra-local-radical`) -/
theorem comap_eq_maximalIdeal_of_finite {B : Type v} [CommRing B] [Algebra R B]
    [Module.Finite R B] (n : Ideal B) [n.IsMaximal] :
    n.comap (algebraMap R B) = maximalIdeal R :=
  have := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) n
  IsLocalRing.eq_maximalIdeal this

/-- **Finite algebras over a local ring: `𝔪B` lies in the Jacobson radical.** If `B` is a
finite `R`-algebra over the local ring `(R, 𝔪)`, then `𝔪B` is contained in the Jacobson
radical of `B`.

(blueprint: `lem-weil-pbc-finite-algebra-local-radical`) -/
theorem map_maximalIdeal_le_jacobson_of_finite {B : Type v} [CommRing B] [Algebra R B]
    [Module.Finite R B] :
    (maximalIdeal R).map (algebraMap R B) ≤ Ideal.jacobson ⊥ := by
  refine le_sInf fun n ⟨_, hn⟩ ↦ ?_
  rw [Ideal.map_le_iff_le_comap, comap_eq_maximalIdeal_of_finite n]

/-- **Uniqueness of retractions of unramified algebras over a local ring.** Two `R`-algebra
maps from a formally unramified, essentially of finite type `R`-algebra `S` to the local ring
`R` with the same preimage of the maximal ideal are equal.
(blueprint: `lem-weil-pbc-henselian-etale-retraction-uniqueness`) -/
theorem algHom_ext_of_comap_maximalIdeal_eq {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] {σ₁ σ₂ : S →ₐ[R] R}
    (h : (maximalIdeal R).comap σ₁ = (maximalIdeal R).comap σ₂) : σ₁ = σ₂ := by
  obtain ⟨t, ht, ht1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.mp ‹_›
  have hmod (s : S) : σ₂ s - σ₁ s ∈ maximalIdeal R := by
    have hs : s - algebraMap R S (σ₁ s) ∈ (maximalIdeal R).comap σ₁ := by
      simp [Ideal.mem_comap]
    rwa [h, Ideal.mem_comap, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply] at hs
  let φ : S ⊗[R] S →ₐ[R] R := Algebra.TensorProduct.lift σ₁ σ₂ fun _ _ ↦ Commute.all _ _
  have hφ : (IsScalarTower.toAlgHom R R (ResidueField R)).comp φ =
      ((IsScalarTower.toAlgHom R R (ResidueField R)).comp σ₁).comp
        (Algebra.TensorProduct.lmul' R) := by
    refine Algebra.TensorProduct.ext' fun a b ↦ ?_
    have hb : residue R (σ₂ b) = residue R (σ₁ b) := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hmod b
    simp [φ, ResidueField.algebraMap_eq, hb]
  have hunit : IsUnit (φ t) := by
    rw [← residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq]
    have := congr($hφ t)
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this, ht1, map_one, map_one]
    exact one_ne_zero
  ext s
  have := congr(φ $(ht s))
  rw [map_mul, map_sub, map_zero] at this
  simp only [φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at this
  exact (sub_eq_zero.mp (hunit.mul_left_eq_zero.mp this)).symm

/-- **Sections of étale algebras through residue field points.** Let `(R, 𝔪, κ)` be a local
ring in which simple roots in `κ` of monic polynomials over `R` lift to roots in `R`. Then every
`R`-algebra map `χ : S →ₐ[R] κ` from an étale `R`-algebra `S` is the reduction of an
`R`-algebra map `S →ₐ[R] R`. -/
theorem exists_algHom_comp_eq_of_forall_exists_isRoot
    (H : ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R, aeval a₀ f = 0 →
      aeval a₀ (derivative f) ≠ 0 → ∃ a : R, f.IsRoot a ∧ residue R a = a₀)
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (χ : S →ₐ[R] ResidueField R) :
    ∃ σ : S →ₐ[R] R, (IsScalarTower.toAlgHom R R (ResidueField R)).comp σ = χ := by
  have : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime _
  have : Algebra.IsEtaleAt R (RingHom.ker χ) :=
    inferInstanceAs (Algebra.FormallyEtale R (Localization (RingHom.ker χ).primeCompl))
  obtain ⟨h, hh, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (RingHom.ker χ)
  have hu (y : Submonoid.powers h) : IsUnit (χ y) := by
    obtain ⟨y, n, rfl⟩ := y
    rw [map_pow]
    exact (isUnit_iff_ne_zero.mpr fun e ↦ hh (RingHom.mem_ker.mpr e)).pow n
  let χₗ : Localization.Away h →ₐ[R] ResidueField R :=
    IsLocalization.liftAlgHom (M := Submonoid.powers h) (f := χ) hu
  obtain ⟨Pres⟩ := hstd.nonempty_standardEtalePresentation
  have hx := Pres.hasMap.map χₗ
  obtain ⟨a, ha, hares⟩ := H Pres.P.f Pres.P.monic_f (χₗ Pres.x) hx.1
    hx.isUnit_derivative_f.ne_zero
  have haP : Pres.P.HasMap a := by
    refine ⟨by simpa [aeval_def] using ha, ?_⟩
    rw [← residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq, ← aeval_algebraMap_apply,
      ResidueField.algebraMap_eq, hares]
    exact hx.2.ne_zero
  let σ₀ : Localization.Away h →ₐ[R] R := (Pres.P.lift a haP).comp Pres.equivRing.toAlgHom
  have key : (IsScalarTower.toAlgHom R R (ResidueField R)).comp σ₀ = χₗ := by
    refine Pres.hom_ext ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Pres.equivRing_x, Pres.P.lift_X, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq,
      hares]
  refine ⟨σ₀.comp (IsScalarTower.toAlgHom R S (Localization.Away h)), ?_⟩
  rw [← AlgHom.comp_assoc, key]
  refine AlgHom.ext fun y ↦ ?_
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  exact IsLocalization.lift_eq hu y

/-- **Étale retractions over a local ring in which simple roots lift.** Let `(R, 𝔪, κ)` be a
local ring in which simple roots in `κ` of monic polynomials over `R` lift to roots in `R`, let
`S` be an étale `R`-algebra and `q` a prime of `S` lying over `𝔪` such that `κ → κ(q)` is
bijective. Then there is exactly one `R`-algebra map `τ : S →ₐ[R] R` with `τ⁻¹(𝔪) = q`.

(blueprint: `lem-weil-pbc-root-lifting-etale-retraction`) -/
theorem existsUnique_algHom_comap_maximalIdeal_eq_of_forall_exists_isRoot
    (H : ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R, aeval a₀ f = 0 →
      aeval a₀ (derivative f) ≠ 0 → ∃ a : R, f.IsRoot a ∧ residue R a = a₀)
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
      hq.symm)) :
    ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap τ = q := by
  let e₁ : ResidueField R ≃ₐ[R] (maximalIdeal R).ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ maximalIdeal R) _)
      (maximalIdeal R).bijective_algebraMap_quotient_residueField
  let e₂ := AlgEquiv.ofBijective _ hκ
  let χ : S →ₐ[R] ResidueField R := (e₁.symm.toAlgHom.comp e₂.symm.toAlgHom).comp
    (IsScalarTower.toAlgHom R S q.ResidueField)
  obtain ⟨σ, hσ⟩ := exists_algHom_comp_eq_of_forall_exists_isRoot H χ
  have hσq : (maximalIdeal R).comap σ = q := by
    ext s
    have hs := congr($hσ s)
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq] at hs
    rw [Ideal.mem_comap, ← residue_eq_zero_iff, hs]
    simp [χ]
  exact ⟨σ, hσq, fun σ' hσ' ↦ algHom_ext_of_comap_maximalIdeal_eq (hσ'.trans hσq.symm)⟩

/-- **Quotients by complements of idempotents with a unique maximal ideal are local.** Let `x`
be a nonzero idempotent of a commutative ring `B` such that at most one maximal ideal of `B`
does not contain `x`. Then `B ⧸ (1 - x)` is a local ring. -/
theorem _root_.IsIdempotentElem.isLocalRing_quotient_span_one_sub {B : Type*} [CommRing B]
    {x : B}
    (hx : IsIdempotentElem x) (hx0 : x ≠ 0)
    (H : ∀ M₁ M₂ : Ideal B, M₁.IsMaximal → M₂.IsMaximal → x ∉ M₁ → x ∉ M₂ → M₁ = M₂) :
    IsLocalRing (B ⧸ Ideal.span {1 - x}) := by
  have : Nontrivial (B ⧸ Ideal.span {1 - x}) := by
    refine Ideal.Quotient.nontrivial_iff.mpr fun h ↦ hx0 ?_
    rw [Ideal.span_singleton_eq_top] at h
    simpa using h.mul_left_eq_zero.mp hx.mul_one_sub_self
  refine .of_unique_max_ideal ?_
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (B ⧸ Ideal.span {1 - x})
  have hnot (N : Ideal (B ⧸ Ideal.span {1 - x})) (hN : N.IsMaximal) :
      x ∉ N.comap (Ideal.Quotient.mk _) := by
    intro hxN
    have h1 : 1 - x ∈ N.comap (Ideal.Quotient.mk _) := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
      exact N.zero_mem
    have h2 := add_mem h1 hxN
    rw [sub_add_cancel, Ideal.mem_comap, map_one] at h2
    exact hN.ne_top ((Ideal.eq_top_iff_one N).mpr h2)
  refine ⟨M, hM, fun N hN ↦ Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_⟩
  exact H _ _ (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) (hnot N hN) (hnot M hM)
/-- **Étale retractions give product decompositions of finite algebras.** Let `(R, 𝔪, κ)` be a
local ring such that for every étale `R`-algebra `R'` and every prime `𝔪'` of `R'` over `𝔪`
with `κ → κ(𝔪')` bijective there is an `R`-algebra map `τ : R' →ₐ[R] R` with `τ⁻¹(𝔪) = 𝔪'`.
Then every finite `R`-algebra is isomorphic to a finite product of local rings.

(blueprint: `lem-weil-pbc-etale-retraction-finite-product-local`) -/
theorem exists_algEquiv_pi_isLocalRing_of_forall_exists_algHom
    (H : ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (m' : Ideal R')
      [m'.IsPrime] (hm' : m'.comap (algebraMap R R') = maximalIdeal R),
      Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) m' (Algebra.ofId R R')
        hm'.symm) →
      ∃ τ : R' →ₐ[R] R, (maximalIdeal R).comap τ = m')
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] :
    ∃ (r : ℕ) (B' : Fin r → Type u) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra R (B' i))
      (_ : ∀ i, IsLocalRing (B' i)), Nonempty (B ≃ₐ[R] ∀ i, B' i) := by
  classical
  obtain ⟨R', _, _, _, P, _, hPm, n, e, he, P', _, _, hP, -, hP''⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq (S := B)
      (maximalIdeal R)
  obtain ⟨τ, hτ⟩ := H R' P (P.over_def (maximalIdeal R)).symm hP
  let φ : R' ⊗[R] B →ₐ[R] B :=
    Algebra.TensorProduct.lift ((Algebra.ofId R B).comp τ) (AlgHom.id R B)
      fun _ _ ↦ Commute.all _ _
  have hφs : Function.Surjective φ := fun b ↦ ⟨1 ⊗ₜ b, by simp [φ]⟩
  have hlies (M : Ideal B) [M.IsMaximal] : (M.comap φ).LiesOver P := by
    refine ⟨?_⟩
    rw [← hτ]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, ← comap_eq_maximalIdeal_of_finite M,
      Ideal.mem_comap]
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
  have hkey (i : Fin (n + 1)) (M₁ M₂ : Ideal B) (h₁ : M₁.IsMaximal) (h₂ : M₂.IsMaximal)
      (hM₁ : φ (e i) ∉ M₁) (hM₂ : φ (e i) ∉ M₂) : M₁ = M₂ := by
    have H₁ := hP'' (M₁.comap φ) inferInstance (hlies M₁)
    have H₂ := hP'' (M₂.comap φ) inferInstance (hlies M₂)
    refine Ideal.comap_injective_of_surjective φ hφs ?_
    obtain ⟨j, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · rw [H₁.2 j hM₁, H₂.2 j hM₂]
    · exact absurd H₁.1 hM₁
  let J := {i : Fin (n + 1) // φ (e i) ≠ 0}
  have hJ : CompleteOrthogonalIdempotents fun j : J ↦ φ (e j) := by
    have hfe := he.map φ.toRingHom
    refine ⟨hfe.1.embedding (Function.Embedding.subtype _), ?_⟩
    calc ∑ j : J, φ (e j) = ∑ i ∈ Finset.univ.filter (fun i ↦ φ (e i) ≠ 0), φ (e i) :=
          (Finset.sum_subtype (p := fun i ↦ φ (e i) ≠ 0) _ (fun _ ↦ by simp)
            fun i ↦ φ (e i)).symm
      _ = ∑ i, φ (e i) := Finset.sum_filter_ne_zero _
      _ = 1 := hfe.complete
  let Q (j : J) := B ⧸ Ideal.span {1 - φ (e j)}
  let eJ := Fintype.equivFin J
  refine ⟨Fintype.card J, fun k ↦ Q (eJ.symm k), fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun k ↦ (he.idem _).map φ |>.isLocalRing_quotient_span_one_sub (eJ.symm k).2
      (hkey _), ⟨?_⟩⟩
  exact (AlgEquiv.ofBijective (AlgHom.pi fun j ↦ Ideal.Quotient.mkₐ R _)
    hJ.bijective_pi).trans (AlgEquiv.piCongrLeft R Q eJ.symm).symm

/-- In a local ring, an element which is idempotent modulo an ideal `J` is congruent to `0` or to
`1` modulo `J`. -/
theorem sub_mem_or_sub_one_mem_of_mul_self_sub_mem {A : Type*} [CommRing A] [IsLocalRing A]
    {J : Ideal A} {y : A} (hy : y * y - y ∈ J) : y ∈ J ∨ y - 1 ∈ J := by
  rw [show y * y - y = (y - 1) * y by ring] at hy
  rcases isUnit_or_isUnit_one_sub_self y with h | h
  · exact .inr ((J.mul_unit_mem_iff_mem h).mp hy)
  · refine .inl ((J.mul_unit_mem_iff_mem h.neg).mp ?_)
    rw [show y * -(1 - y) = (y - 1) * y by ring]
    exact hy

/-- An element of a finite product of rings lies in an ideal `K` as soon as each of its
components lies in the image of `K` under the corresponding projection. -/
theorem _root_.Ideal.mem_of_forall_apply_mem_map_evalRingHom {ι : Type*} [Finite ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] (K : Ideal (∀ i, B i)) (z : ∀ i, B i)
    (hz : ∀ i, z i ∈ K.map (Pi.evalRingHom B i)) : z ∈ K := by
  classical
  have := Fintype.ofFinite ι
  have hsum : z = ∑ i, Pi.single i (z i) := by ext; simp
  rw [hsum]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  obtain ⟨w, hw, hwi⟩ :=
    (Ideal.mem_map_iff_of_surjective _ (Function.surjective_eval i)).mp (hz i)
  have : Pi.single i (z i) = Pi.single i 1 * w := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [← hwi]
    · simp [hj]
  rw [this]
  exact K.mul_mem_left _ hw

/-- **Idempotent lifting for finite products of local rings.** If a commutative ring `B` is
isomorphic to a finite product of local rings, then every idempotent of `B / I` lifts to an
idempotent of `B`, for every ideal `I` of `B`. -/
theorem exists_isIdempotentElem_mk_eq_of_ringEquiv_pi {B : Type*} [CommRing B] {ι : Type*}
    [Finite ι] {B' : ι → Type*} [∀ i, CommRing (B' i)] [∀ i, IsLocalRing (B' i)]
    (ψ : B ≃+* ∀ i, B' i) (I : Ideal B) (e : B ⧸ I) (he : IsIdempotentElem e) :
    ∃ e' : B, IsIdempotentElem e' ∧ Ideal.Quotient.mk I e' = e := by
  classical
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hb : b * b - b ∈ I := by
    rw [← Ideal.Quotient.eq, map_mul]
    exact he
  let K : Ideal (∀ i, B' i) := I.map ψ
  let J (i : ι) : Ideal (B' i) := K.map (Pi.evalRingHom B' i)
  have hy (i : ι) : ψ b i * ψ b i - ψ b i ∈ J i := by
    have := Ideal.mem_map_of_mem (Pi.evalRingHom B' i) (Ideal.mem_map_of_mem ψ hb)
    simpa using this
  let ε : ∀ i, B' i := fun i ↦ if ψ b i ∈ J i then 0 else 1
  have hε (i : ι) : ψ b i - ε i ∈ J i := by
    simp only [ε]
    split_ifs with h
    · simpa using h
    · exact (sub_mem_or_sub_one_mem_of_mul_self_sub_mem (hy i)).resolve_left h
  have hεi : IsIdempotentElem ε := by
    ext i
    simp only [Pi.mul_apply, ε]
    split_ifs <;> simp
  refine ⟨ψ.symm ε, hεi.map ψ.symm, ?_⟩
  rw [Ideal.Quotient.eq]
  have hz : ψ b - ε ∈ K :=
    Ideal.mem_of_forall_apply_mem_map_evalRingHom K _ fun i ↦ by simpa using hε i
  obtain ⟨x, hx, hxz⟩ := (Ideal.mem_map_of_equiv ψ _).mp hz
  have : ψ.symm ε - b = -x := by
    apply ψ.injective
    simp [hxz]
  rw [this]
  exact I.neg_mem hx

/-- **Idempotent lifting implies henselian.** Let `(R, 𝔪)` be a local ring such that for every
finite `R`-algebra `B` every idempotent of `B / 𝔪B` lifts to an idempotent of `B`. Then `R` is
henselian.

We apply the hypothesis to `S = R[X]/(f)` and the idempotent of `S / 𝔪S` cutting out the simple
root; the corresponding factor of `S` is isomorphic to `R`, and the image of `X` there is the
desired root. -/
theorem henselianLocalRing_of_forall_exists_isIdempotentElem
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
      (e : B ⧸ (maximalIdeal R).map (algebraMap R B)), IsIdempotentElem e →
        ∃ e' : B, IsIdempotentElem e' ∧ Ideal.Quotient.mk _ e' = e) :
    HenselianLocalRing R := by
  refine ⟨fun f hf b hfb hf'b ↦ ?_⟩
  -- the polynomial algebra computations
  have hfh : f = (X - C b) * (f /ₘ (X - C b)) + C (f.eval b) := by
    rw [← modByMonic_X_sub_C_eq_C_eval, add_comm]
    exact (modByMonic_add_div _ _).symm
  generalize f /ₘ (X - C b) = h at hfh
  have hc : f.derivative.eval b = h.eval b := by
    conv_lhs => rw [hfh]
    simp [derivative_mul]
  have hhq : h = (X - C b) * (h /ₘ (X - C b)) + C (h.eval b) := by
    rw [← modByMonic_X_sub_C_eq_C_eval, add_comm]
    exact (modByMonic_add_div _ _).symm
  generalize h /ₘ (X - C b) = q at hhq
  let u : Rˣ := hf'b.unit
  have hu : (u : R) = h.eval b := hc
  -- the algebra `S = R[X]/(f)`
  have : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  let pb := AdjoinRoot.powerBasis' hf
  let x : AdjoinRoot f := AdjoinRoot.root f
  let I : Ideal (AdjoinRoot f) := (maximalIdeal R).map (algebraMap R (AdjoinRoot f))
  have hfx : aeval x f = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hfbI : algebraMap R (AdjoinRoot f) (f.eval b) ∈ I := Ideal.mem_map_of_mem _ hfb
  have h1 : (x - algebraMap R (AdjoinRoot f) b) * aeval x h =
      -algebraMap R (AdjoinRoot f) (f.eval b) := by
    have := congr(aeval x $hfh)
    simp only [map_add, map_mul, map_sub, aeval_X, aeval_C, hfx] at this
    linear_combination -this
  have h2 : aeval x h =
      (x - algebraMap R (AdjoinRoot f) b) * aeval x q + algebraMap R (AdjoinRoot f) u := by
    have := congr(aeval x $hhq)
    simpa only [map_add, map_mul, map_sub, aeval_X, aeval_C, hu] using this
  have h3 : algebraMap R (AdjoinRoot f) ↑u⁻¹ * algebraMap R (AdjoinRoot f) u = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  let e₀ : AdjoinRoot f := algebraMap R (AdjoinRoot f) ↑u⁻¹ * aeval x h
  have he₀ : e₀ * e₀ - e₀ ∈ I := by
    rw [show e₀ * e₀ - e₀ =
        -(algebraMap R (AdjoinRoot f) ↑u⁻¹ ^ 2 * aeval x q) *
          algebraMap R (AdjoinRoot f) (f.eval b) by
      linear_combination (algebraMap R (AdjoinRoot f) ↑u⁻¹ ^ 2 * aeval x q) * h1 +
        (algebraMap R (AdjoinRoot f) ↑u⁻¹ * aeval x h * algebraMap R (AdjoinRoot f) ↑u⁻¹) * h2 +
        (algebraMap R (AdjoinRoot f) ↑u⁻¹ * aeval x h) * h3]
    exact I.mul_mem_left _ hfbI
  have hxe₀ : (x - algebraMap R (AdjoinRoot f) b) * e₀ ∈ I := by
    rw [show (x - algebraMap R (AdjoinRoot f) b) * e₀ =
        -algebraMap R (AdjoinRoot f) ↑u⁻¹ * algebraMap R (AdjoinRoot f) (f.eval b) by
      linear_combination algebraMap R (AdjoinRoot f) ↑u⁻¹ * h1]
    exact I.mul_mem_left _ hfbI
  -- lift the idempotent
  obtain ⟨e, he, hee₀⟩ := H (AdjoinRoot f) (Ideal.Quotient.mk I e₀) (by
    rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
    exact he₀)
  rw [Ideal.Quotient.eq] at hee₀
  -- `e ∉ 𝔪S`, detected by the evaluation `S → κ` at the residue of `b`
  let φ : (AdjoinRoot f) →+* ResidueField R := AdjoinRoot.lift (residue R) (residue R b) (by
    rw [eval₂_hom, residue_eq_zero_iff]
    exact hfb)
  have hφI : ∀ s ∈ I, φ s = 0 := by
    intro s hs
    refine (Ideal.map_le_iff_le_comap.mpr ?_ hs : s ∈ RingHom.ker φ)
    intro r hr
    simp only [Ideal.mem_comap, RingHom.mem_ker, AdjoinRoot.algebraMap_eq, φ,
      AdjoinRoot.lift_of]
    exact (residue_eq_zero_iff r).mpr hr
  have hφe₀ : φ e₀ = 1 := by
    simp only [e₀, φ, x, AdjoinRoot.aeval_eq, AdjoinRoot.algebraMap_eq, map_mul,
      AdjoinRoot.lift_of, AdjoinRoot.lift_mk, eval₂_hom, ← hu]
    rw [← map_mul, Units.inv_mul, map_one]
  have heI : e ∉ I := by
    intro heI
    have : e₀ ∈ I := by simpa using I.sub_mem heI hee₀
    simpa [hφe₀] using hφI _ this
  -- hence some coordinate of `e` is a unit
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (pb.basis.repr e i) := by
    by_contra! hne
    refine heI ?_
    rw [← pb.basis.sum_repr e]
    refine Ideal.sum_mem _ fun i _ ↦ ?_
    rw [Algebra.smul_def]
    exact I.mul_mem_right _ (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr (hne i)))
  -- the factor `A = S / (1 - e)` of `S`
  let A := (AdjoinRoot f) ⧸ Ideal.span {1 - e}
  let π : (AdjoinRoot f) →ₐ[R] A := Ideal.Quotient.mkₐ R _
  have : Module.Finite R A :=
    Module.Finite.of_surjective π.toLinearMap Ideal.Quotient.mk_surjective
  let IA : Ideal A := (maximalIdeal R).map (algebraMap R A)
  have hπI : ∀ s ∈ I, π s ∈ IA := by
    intro s hs
    refine (Ideal.map_le_iff_le_comap.mpr ?_ hs : s ∈ IA.comap π)
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hr
  have hπe : π e = 1 := by
    rw [← sub_eq_zero, ← map_one π, ← map_sub, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, show e - 1 = -(1 - e) by ring]
    exact neg_mem (Ideal.mem_span_singleton_self _)
  have hxA : π x - algebraMap R A b ∈ IA := by
    have : (x - algebraMap R (AdjoinRoot f) b) * e ∈ I := by
      rw [show (x - algebraMap R (AdjoinRoot f) b) * e = (x - algebraMap R (AdjoinRoot f) b) * e₀ +
        (x - algebraMap R (AdjoinRoot f) b) * (e - e₀) by ring]
      exact I.add_mem hxe₀ (I.mul_mem_left _ hee₀)
    have := hπI _ this
    rwa [map_mul, hπe, mul_one, map_sub, AlgHom.commutes] at this
  have hinj : Function.Injective (algebraMap R A) := by
    refine (injective_iff_map_eq_zero _).mpr fun r hr ↦ ?_
    rw [IsScalarTower.algebraMap_apply R (AdjoinRoot f) A, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hr
    obtain ⟨s, hs⟩ := hr
    have hre : r • e = 0 := by
      rw [Algebra.smul_def, ← hs, mul_assoc, he.one_sub_mul_self, mul_zero]
    have := congr(pb.basis.repr $hre i)
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
    exact hi.mul_left_eq_zero.mp this
  have hsurj : Function.Surjective (algebraMap R A) := by
    let N : Submodule R A := LinearMap.range (Algebra.linearMap R A)
    have htop : (⊤ : Submodule R A) ≤ N ⊔ maximalIdeal R • ⊤ := by
      rintro a -
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective s
      have hpA : Ideal.Quotient.mk _ (AdjoinRoot.mk f p) = aeval (π x) p := by
        rw [← AdjoinRoot.aeval_eq, ← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_algHom_apply]
      rw [hpA]
      have hmem : aeval (π x) p - algebraMap R A (p.eval b) ∈ IA := by
        rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_def, aeval_def, eval₂_eq_eval_map,
          eval₂_eq_eval_map]
        obtain ⟨k, hk⟩ := sub_dvd_eval_sub (π x) (algebraMap R A b) (p.map (algebraMap R A))
        rw [hk]
        exact IA.mul_mem_right _ hxA
      rw [← sub_add_cancel (aeval (π x) p) (algebraMap R A (p.eval b)), add_comm]
      refine Submodule.add_mem_sup ⟨p.eval b, rfl⟩ ?_
      rw [Ideal.smul_top_eq_map]
      exact hmem
    have := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
      (maximalIdeal_le_jacobson ⊥) htop
    exact fun a ↦ this Submodule.mem_top
  -- the root
  obtain ⟨a, ha⟩ := hsurj (π x)
  refine ⟨a, hinj ?_, ?_⟩
  · rw [map_zero, ← aeval_algebraMap_apply_eq_algebraMap_eval, ha, aeval_algHom_apply, hfx,
      map_zero]
  · rw [← Ideal.comap_map_of_bijective _ ⟨hinj, hsurj⟩ (I := maximalIdeal R), Ideal.mem_comap,
      map_sub, ha]
    exact hxA

/-- **Henselian local rings: idempotent lifting versus root lifting.** For a local ring
`(R, 𝔪, κ)` the following are equivalent:
(i) for every finite `R`-algebra `B`, every idempotent of `B / 𝔪B` lifts uniquely to an
idempotent of `B`;
(ii) for every monic `f ∈ R[X]` and every simple root `a₀ ∈ κ` of `f mod 𝔪` there is a root
`a ∈ R` of `f` lifting `a₀`.

(blueprint: `lem-weil-pbc-henselian-local-root-lifting`) -/
theorem forall_existsUnique_isIdempotentElem_iff_forall_exists_isRoot :
    (∀ (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
      (e : B ⧸ (maximalIdeal R).map (algebraMap R B)), IsIdempotentElem e →
        ∃! e' : B, IsIdempotentElem e' ∧ Ideal.Quotient.mk _ e' = e) ↔
    ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R, aeval a₀ f = 0 →
      aeval a₀ (derivative f) ≠ 0 → ∃ a : R, f.IsRoot a ∧ residue R a = a₀ := by
  refine ⟨fun H ↦ ((HenselianLocalRing.TFAE R).out 1 2).mp
    (henselianLocalRing_of_forall_exists_isIdempotentElem fun B _ _ _ e he ↦ (H B e he).exists),
    fun H B _ _ _ e he ↦ ?_⟩
  obtain ⟨r, B', _, _, _, ⟨ψ⟩⟩ := exists_algEquiv_pi_isLocalRing_of_forall_exists_algHom
    (fun R' _ _ _ m' _ hm' hκ ↦
      (existsUnique_algHom_comap_maximalIdeal_eq_of_forall_exists_isRoot H m' hm' hκ).exists) B
  obtain ⟨e', he', rfl⟩ :=
    exists_isIdempotentElem_mk_eq_of_ringEquiv_pi ψ.toRingEquiv _ e he
  refine ⟨e', ⟨he', rfl⟩, fun e'' ⟨he'', h⟩ ↦ he''.eq_of_sub_mem_jacobson_bot he' ?_⟩
  exact map_maximalIdeal_le_jacobson_of_finite (Ideal.Quotient.eq.mp h)

end IsLocalRing

namespace HenselianLocalRing

variable {R : Type u} [CommRing R]

/-- **Étale retractions over a henselian local ring.** Let `(R, 𝔪, κ)` be a henselian local
ring, `S` an étale `R`-algebra and `q` a prime of `S` lying over `𝔪` such that `κ → κ(q)` is
bijective. Then there is exactly one `R`-algebra map `σ : S →ₐ[R] R` with `σ⁻¹(𝔪) = q`.

(blueprint: `lem-weil-pbc-henselian-etale-retraction`) -/
theorem existsUnique_algHom_comap_maximalIdeal_eq [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
      hq.symm)) :
    ∃! σ : S →ₐ[R] R, (maximalIdeal R).comap σ = q :=
  IsLocalRing.existsUnique_algHom_comap_maximalIdeal_eq_of_forall_exists_isRoot
    (((HenselianLocalRing.TFAE R).out 1 2).mp ‹HenselianLocalRing R›) q hq hκ

/-- **Existence of étale retractions over a henselian local ring**: the existence half of
`HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_eq`.
(blueprint: `lem-weil-pbc-henselian-etale-retraction-existence`) -/
theorem exists_algHom_comap_maximalIdeal_eq [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
      hq.symm)) :
    ∃ σ : S →ₐ[R] R, (maximalIdeal R).comap σ = q :=
  (existsUnique_algHom_comap_maximalIdeal_eq q hq hκ).exists

/-- **Henselian local rings lift idempotents.** A local ring `(R, 𝔪)` is henselian (in Mathlib's
sense of lifting simple roots) if and only if for every finite `R`-algebra `B` every idempotent
of `B / 𝔪B` lifts uniquely to an idempotent of `B`.

(blueprint: `lem-weil-pbc-henselian-local-root-lifting`) -/
theorem iff_forall_existsUnique_isIdempotentElem [IsLocalRing R] :
    HenselianLocalRing R ↔
      ∀ (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
        (e : B ⧸ (maximalIdeal R).map (algebraMap R B)), IsIdempotentElem e →
          ∃! e' : B, IsIdempotentElem e' ∧ Ideal.Quotient.mk _ e' = e := by
  rw [IsLocalRing.forall_existsUnique_isIdempotentElem_iff_forall_exists_isRoot]
  exact (HenselianLocalRing.TFAE R).out 1 2

end HenselianLocalRing

namespace IsStrictlyHenselianLocalRing

variable {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]

/-- **Maps from étale algebras into a strictly henselian local ring.** Let `(R, 𝔪)` be a strictly
henselian local ring, `K` a field over `R` with `ker(R → K) = 𝔪` and `S` an étale `R`-algebra.
Every `R`-algebra map `χ : S → K` lifts uniquely to an `R`-algebra map `S → R`.

This is the single-étale-algebra case of the blueprint lemma, with the residue condition
`τ : κ(q) → κ` automatic since `κ` is separably closed.

(blueprint: `lem-weil-pbc-map-into-henselian-colimit`) -/
theorem existsUnique_algHom_comp_eq {K : Type*} [Field K] [Algebra R K]
    (hK : RingHom.ker (algebraMap R K) = maximalIdeal R) {S : Type v} [CommRing S]
    [Algebra R S] [Algebra.Etale R S] (χ : S →ₐ[R] K) :
    ∃! τ : S →ₐ[R] R, (Algebra.ofId R K).comp τ = χ := by
  have : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime _
  have hq : (RingHom.ker χ).comap (algebraMap R S) = maximalIdeal R := by
    ext r
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, ← RingHom.mem_ker, hK]
  have : (RingHom.ker χ).LiesOver (maximalIdeal R) := ⟨hq.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) (RingHom.ker χ)
  have : IsSepClosed (maximalIdeal R).ResidueField := by
    let e : ResidueField R ≃+* (maximalIdeal R).ResidueField :=
      RingEquiv.ofBijective (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
        (maximalIdeal R).bijective_algebraMap_quotient_residueField
    exact IsSepClosed.of_ringEquiv e
  have hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) (RingHom.ker χ)
      (Algebra.ofId R S) hq.symm) :=
    ⟨RingHom.injective _, IsSepClosed.algebraMap_surjective (maximalIdeal R).ResidueField
      (RingHom.ker χ).ResidueField⟩
  obtain ⟨τ, hτ, -⟩ :=
    HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_eq (RingHom.ker χ) hq hκ
  have key : (Algebra.ofId R K).comp τ = χ := by
    ext d
    have : d - algebraMap R S (τ d) ∈ RingHom.ker χ := by
      rw [← hτ, Ideal.mem_comap, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
      exact zero_mem _
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
    simp [this]
  refine ⟨τ, key, fun τ' hτ' ↦ IsLocalRing.algHom_ext_of_comap_maximalIdeal_eq ?_⟩
  ext d
  rw [Ideal.mem_comap, Ideal.mem_comap, ← hK, RingHom.mem_ker, RingHom.mem_ker,
    ← Algebra.ofId_apply, ← Algebra.ofId_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, hτ', key]

end IsStrictlyHenselianLocalRing
