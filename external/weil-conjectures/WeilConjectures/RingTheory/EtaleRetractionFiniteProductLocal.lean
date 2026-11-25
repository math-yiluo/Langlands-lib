/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Finite algebras over a local ring with étale retractions

Source: `literature/stacks-project/algebra.tex`, Lemma Tag 04GG (proof of 8 => 10)
(blueprint: lem-weil-pbc-etale-retraction-finite-product-local).
-/

@[expose] public section

universe u v

/-- The final algebra step of Stacks Project, algebra.tex, Lemma Tag 04GG, (8) => (10).
Discard the zero idempotents. The quotients by `1 - eᵢ` are nonzero, and their maximal
ideals pull back injectively to maximal ideals missing `eᵢ`; hence each quotient is local.
Mathlib's complete-orthogonal-idempotent product map identifies the ring with their product.
The empty family covers the zero ring. -/
private theorem product_local_of_separating_idempotents
    {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
    {I : Type*} [Fintype I] (e : I → B) (he : CompleteOrthogonalIdempotents e)
    (hsep : ∀ i (q₁ q₂ : Ideal B), q₁.IsMaximal → q₂.IsMaximal →
      e i ∉ q₁ → e i ∉ q₂ → q₁ = q₂) :
    ∃ (n : ℕ) (A : Fin n → Type v)
      (comm : ∀ i, CommRing (A i)) (alg : ∀ i, Algebra R (A i))
      (loc : ∀ i, IsLocalRing (A i)),
      letI : ∀ i, CommRing (A i) := comm
      letI : ∀ i, Algebra R (A i) := alg
      letI : ∀ i, IsLocalRing (A i) := loc
      Nonempty (B ≃ₐ[R] ∀ i, A i) := by
  classical
  let J := {i : I // e i ≠ 0}
  let e' : J → B := fun i ↦ e i.1
  have he' : CompleteOrthogonalIdempotents e' := by
    refine ⟨⟨fun i ↦ he.idem i.1, fun i j hij ↦ he.ortho ?_⟩, ?_⟩
    · exact fun h ↦ hij (Subtype.ext h)
    · change (∑ i : J, e i.1) = 1
      rw [← he.complete]
      exact (Finset.sum_subtype (Finset.univ.filter (fun i ↦ e i ≠ 0))
        (by simp) e).symm.trans (Finset.sum_filter_ne_zero _)
  let K : J → Ideal B := fun i ↦ Ideal.span {1 - e' i}
  have hnotmem (i : J) : e' i ∉ K i := by
    intro hi
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hi
    apply i.2
    change e' i = 0
    have hh := he'.idem i
    change e' i * e' i = e' i at hh
    calc
      e' i = e' i * e' i := hh.symm
      _ = e' i * ((1 - e' i) * b) := congrArg (e' i * ·) hb
      _ = 0 := by rw [← mul_assoc, mul_sub, mul_one, hh, sub_self, zero_mul]
  have hK (i : J) : K i ≠ ⊤ := by
    intro hi
    exact hnotmem i (by rw [hi]; trivial)
  let A : J → Type v := fun i ↦ B ⧸ K i
  have hloc (i : J) : IsLocalRing (A i) := by
    have : Nontrivial (A i) := Ideal.Quotient.nontrivial_iff.mpr (hK i)
    have hav (M : Ideal (A i)) [M.IsMaximal] :
        e' i ∉ M.comap (Ideal.Quotient.mk (K i)) := by
      intro hm
      have hc : 1 - e' i ∈ M.comap (Ideal.Quotient.mk (K i)) := by
        change Ideal.Quotient.mk (K i) (1 - e' i) ∈ M
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))]
        exact M.zero_mem
      exact Ideal.IsMaximal.ne_top (I := M) inferInstance ((Ideal.eq_top_iff_one M).mpr (by
        change Ideal.Quotient.mk (K i) 1 ∈ M
        have hs := (M.comap (Ideal.Quotient.mk (K i))).add_mem hc hm
        change Ideal.Quotient.mk (K i) ((1 - e' i) + e' i) ∈ M at hs
        simpa only [sub_add_cancel] using hs))
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := A i)
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨M, hM, fun N hN ↦ ?_⟩
    have := hM
    have := hN
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk (K i))
      Ideal.Quotient.mk_surjective
    exact hsep i.1 _ _
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) (hav N) (hav M)
  let π : B →ₐ[R] ∀ i, A i := AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ R (K i)
  have hπ : Function.Bijective π := he'.bijective_pi
  let E : B ≃ₐ[R] ∀ i, A i := AlgEquiv.ofBijective π hπ
  let E' := AlgEquiv.piCongrLeft' R A (Fintype.equivFin J)
  refine ⟨Fintype.card J, fun i ↦ A ((Fintype.equivFin J).symm i),
    inferInstance, inferInstance, fun i ↦ hloc _, ⟨E.trans E'⟩⟩

/-- Over a local ring for which pointed étale neighborhoods admit retractions, every
finite algebra is a finite product of local rings.

Source: Stacks Project, algebra.tex, Lemma Tag 04GG, proof of (8) => (10).
The proof follows the six steps of the node:

1. Apply `lem-weil-pbc-finite-algebra-etale-idempotent-decomposition` (Tag 00UK,
   finite case Tag 00UL) to `R → B` at the maximal ideal. Obtain an étale `R'`, a
   prime `p` over that ideal with bijective residue-field map, and complete
   orthogonal idempotents `e₁, …, eₙ, e∞` in `C = R' ⊗[R] B`. Every prime over
   `p` contains `e∞`, and at most one such prime misses each `eᵢ`.
2. Apply `hR` to obtain the retraction `τ` with the prescribed maximal-ideal comap.
3. The tensor-product universal property gives the surjection `φ : C → B` sending
   `r' ⊗ b` to `τ(r') • b`. A prime of `B` over the maximal ideal pulls back to a
   prime of `C` over `p`; surjectivity recovers the original prime from its preimage.
4. The images `fᵢ = φ(eᵢ)` and `f∞ = φ(e∞)` are complete orthogonal idempotents.
   Every prime of `B` over the maximal ideal contains `f∞`; at most one misses `fᵢ`.
5. For an idempotent `f`, the factor `fB`, with unit `f`, is a finite quotient of
   `B`. Its primes correspond to primes of `B` missing `f`. By
   `lem-weil-pbc-finite-algebra-local-radical`, every maximal ideal of this finite
   algebra lies over the maximal ideal of `R`. Hence `f∞B = 0`, since otherwise it
   would have a maximal ideal. Each nonzero `fᵢB` has exactly one maximal ideal,
   and is therefore a local ring.
6. Discard the zero `fᵢ`. The remaining orthogonal idempotents sum to `1`, giving
   the algebra isomorphism `b ↦ (fᵢb)`, with inverse the sum of the components.
   If `B` is zero, no factors remain and the product is empty.

(blueprint: lem-weil-pbc-etale-retraction-finite-product-local) -/
theorem finite_algebra_is_product_local_rings
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : ∀ (R' : Type (max u v)) [CommRing R'] [Algebra R R'],
      Algebra.Etale R R' →
        ∀ (p : Ideal R') [p.IsPrime],
          ∀ (hp : p.comap (algebraMap R R') = IsLocalRing.maximalIdeal R),
            Function.Bijective
                (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p
                  (Algebra.ofId R R') hp.symm) →
              ∃ (τ : R' →ₐ[R] R),
                p = (IsLocalRing.maximalIdeal R).comap τ.toRingHom)
    {B : Type v} [CommRing B] [Algebra R B] [Module.Finite R B] :
    ∃ (n : ℕ) (A : Fin n → Type v)
      (comm : ∀ i, CommRing (A i))
      (alg : ∀ i, Algebra R (A i))
      (loc : ∀ i, IsLocalRing (A i)),
      letI : ∀ i, CommRing (A i) := comm
      letI : ∀ i, Algebra R (A i) := alg
      letI : ∀ i, IsLocalRing (A i) := loc
      Nonempty (B ≃ₐ[R] ∀ i, A i) := by
  classical
  obtain ⟨R', cR', aR', et, p, pp, hp, n, e, he, qs, _, _, hres, _, hsep⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq
      (S := B) (IsLocalRing.maximalIdeal R)
  let _ := cR'
  let _ := aR'
  have := et
  have := pp
  have := hp
  -- Lift the neighborhood to the universe quantified over by `hR`.
  let R'' := ULift.{v} R'
  let σ : R'' ≃ₐ[R] R' := ULift.algEquiv
  have : Algebra.Etale R R'' := Algebra.Etale.of_equiv σ.symm
  let p'' : Ideal R'' := p.comap σ.toRingHom
  have hp'' : p''.comap (algebraMap R R'') = IsLocalRing.maximalIdeal R := by
    rw [show p''.comap (algebraMap R R'') = p.comap (algebraMap R R') by
      ext x
      change σ (algebraMap R R'' x) ∈ p ↔ algebraMap R R' x ∈ p
      rw [σ.commutes]]
    exact (p.over_def _).symm
  have hup : p = p''.comap σ.symm.toRingHom := by
    ext x
    change x ∈ p ↔ σ (σ.symm x) ∈ p
    rw [σ.apply_symm_apply]
  let g := Ideal.ResidueField.map p p'' σ.symm.toRingHom hup
  have hg : Function.Bijective g := by
    let g' := Ideal.ResidueField.map p'' p σ.toRingHom rfl
    have h₁ : g'.comp g = RingHom.id _ := by
      apply Ideal.ResidueField.ringHom_ext
      ext x
      simp [g, g', Ideal.ResidueField.map_algebraMap]
    have h₂ : g.comp g' = RingHom.id _ := by
      apply Ideal.ResidueField.ringHom_ext
      ext x
      simp [g, g', Ideal.ResidueField.map_algebraMap]
    exact ⟨Function.LeftInverse.injective (congrArg DFunLike.coe h₁ |> congrFun),
      Function.RightInverse.surjective (congrArg DFunLike.coe h₂ |> congrFun)⟩
  have hres'' : Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p''
        (Algebra.ofId R R'') hp''.symm) := by
    have hcomp : (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p''
        (Algebra.ofId R R'') hp''.symm).toRingHom =
        g.comp (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p
          (Algebra.ofId R R') (p.over_def _)).toRingHom := by
      apply Ideal.ResidueField.ringHom_ext
      ext x
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map_algebraMap,
        Algebra.ofId_apply]
      simp only [g, Ideal.ResidueField.map_algebraMap]
      exact congrArg (algebraMap R'' p''.ResidueField) (σ.symm.commutes x).symm
    change Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p''
        (Algebra.ofId R R'') hp''.symm).toRingHom
    rw [hcomp]
    exact hg.comp hres
  obtain ⟨τ'', hτ''⟩ := hR R'' inferInstance p'' hp'' hres''
  let τ : R' →ₐ[R] R := τ''.comp σ.symm.toAlgHom
  have hτ : p = (IsLocalRing.maximalIdeal R).comap τ.toRingHom := by
    rw [hup, hτ'']
    rfl
  -- Descend the idempotents along the tensor retraction.
  let φ : TensorProduct R R' B →ₐ[R] B :=
    Algebra.TensorProduct.lift ((Algebra.ofId R B).comp τ) (AlgHom.id R B)
      (fun _ _ ↦ Commute.all _ _)
  have hφ : Function.Surjective φ := by
    intro b
    refine ⟨Algebra.TensorProduct.includeRight b, ?_⟩
    simp [φ]
  let f : Fin (n + 1) → B := φ ∘ e
  have hf : CompleteOrthogonalIdempotents f := he.map φ.toRingHom
  have hcomap (q : Ideal B) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)] :
      (q.comap φ.toRingHom).LiesOver p := by
    constructor
    rw [hτ]
    ext x
    change τ x ∈ IsLocalRing.maximalIdeal R ↔
      φ (algebraMap R' (TensorProduct R R' B) x) ∈ q
    rw [Ideal.mem_of_liesOver q (IsLocalRing.maximalIdeal R)]
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
  have hlast (q : Ideal B) [q.IsPrime]
      [q.LiesOver (IsLocalRing.maximalIdeal R)] : f (Fin.last n) ∈ q := by
    have := hcomap q
    exact (hsep (q.comap φ.toRingHom) inferInstance inferInstance).1
  have hunique (i : Fin n) (q₁ q₂ : Ideal B) [q₁.IsPrime] [q₂.IsPrime]
      [q₁.LiesOver (IsLocalRing.maximalIdeal R)]
      [q₂.LiesOver (IsLocalRing.maximalIdeal R)]
      (h₁ : f i.castSucc ∉ q₁) (h₂ : f i.castSucc ∉ q₂) : q₁ = q₂ := by
    have := hcomap q₁
    have := hcomap q₂
    apply Ideal.comap_injective_of_surjective φ.toRingHom hφ
    exact ((hsep (q₁.comap φ.toRingHom) inferInstance inferInstance).2 i h₁).trans
      ((hsep (q₂.comap φ.toRingHom) inferInstance inferInstance).2 i h₂).symm
  -- Finiteness puts every maximal ideal over the closed point of the base.
  apply product_local_of_separating_idempotents f hf
  intro i q₁ q₂ hq₁ hq₂ h₁ h₂
  have := hq₁
  have := hq₂
  have : q₁.LiesOver (IsLocalRing.maximalIdeal R) := by
    constructor
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) q₁)).symm
  have : q₂.LiesOver (IsLocalRing.maximalIdeal R) := by
    constructor
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) q₂)).symm
  induction i using Fin.lastCases with
  | last => exact False.elim (h₁ (hlast q₁))
  | cast i => exact hunique i q₁ q₂ h₁ h₂
