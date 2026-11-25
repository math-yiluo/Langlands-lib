/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Algebra.Polynomial.Lifts
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.StrictHenselization.Triples

/-!
# The colimit over étale triples is strictly henselian

Let `R` be a commutative ring, `p` a prime of `R` and `K` a separable closure of `κ(p)`. The
colimit `C = colim S` over the étale triples `(S, q, φ)` (`EtaleTriple.colim R p K`) is a
strictly henselian local ring: the map `ψ : C → K` induced by the maps `S → κ(q) → K` is
surjective, its kernel is the maximal ideal `pC` of `C`, and simple roots in `K` of monic
polynomials over `C` lift to `C`. This is the strict henselization of `R_p` with respect to
`κ(p) → K`.

## Main results

- `EtaleTriple.isUnit_iff_eval_ne_zero`, `EtaleTriple.instIsLocalRingColim`: `C` is local with
  maximal ideal the kernel of `ψ`.
- `EtaleTriple.maximalIdeal_colim_eq_map`: the maximal ideal of `C` is `pC`.
- `EtaleTriple.exists_isRoot_and_eval_eq`: simple roots in `K` lift.
- `EtaleTriple.eval_surjective`: `ψ` is surjective.
- `EtaleTriple.isStrictlyHenselianLocalRing_colim`: `C` is strictly henselian.

## References

- Stacks Project, Lemmas 10.155.5 and 10.155.10, <https://stacks.math.columbia.edu/tag/04GW>,
  <https://stacks.math.columbia.edu/tag/04GP>
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial IsLocalRing

namespace EtaleTriple

variable {R : Type u} [CommRing R] {p : Ideal R} [p.IsPrime] {K : Type u} [Field K] [Algebra R K]
  [Algebra p.ResidueField K] [IsScalarTower R p.ResidueField K]

/-- The étale triple `(S[1/s], qS[1/s], φ)` of an étale triple `(S, q, φ)` and an element
`s ∉ q`. -/
noncomputable def away (t : EtaleTriple R p K) (s : t.S) (hs : t.toAlgHom s ≠ 0) :
    EtaleTriple R p K :=
  ofAlgHom (ker_algebraMap R p K) (Localization.Away s)
    (IsLocalization.liftAlgHom (M := Submonoid.powers s) (f := t.toAlgHom)
      (by rintro ⟨_, n, rfl⟩; simpa using (isUnit_iff_ne_zero.mpr hs).pow n))

lemma toAlgHom_away (t : EtaleTriple R p K) (s : t.S) (hs : t.toAlgHom s ≠ 0) :
    (t.away s hs).toAlgHom = IsLocalization.liftAlgHom (M := Submonoid.powers s)
      (S := Localization.Away s) (f := t.toAlgHom)
      (by rintro ⟨_, n, rfl⟩; simpa using (isUnit_iff_ne_zero.mpr hs).pow n) :=
  toAlgHom_ofAlgHom _ _ _

/-- The localization map `S → S[1/s]`, as a morphism of étale triples. -/
noncomputable def toAway (t : EtaleTriple R p K) (s : t.S) (hs : t.toAlgHom s ≠ 0) :
    t ⟶ t.away s hs :=
  homMk (t' := t.away s hs) (IsScalarTower.toAlgHom R t.S (Localization.Away s)) <| by
    rw [toAlgHom_away]
    ext x
    exact IsLocalization.lift_eq (S := Localization.Away s) _ x

lemma ι_away_algebraMap (t : EtaleTriple R p K) (s : t.S) (hs : t.toAlgHom s ≠ 0) (x : t.S) :
    ι R p K (t.away s hs) (algebraMap t.S (Localization.Away s) x) = ι R p K t x :=
  congr($(ι_comp_β R p K (t.toAway s hs)) x)

/-- An element `ι(s)` of the colimit with `s ↦ ψ(s) ≠ 0` is a unit. -/
lemma isUnit_ι_of_toAlgHom_ne_zero (t : EtaleTriple R p K) (s : t.S) (hs : t.toAlgHom s ≠ 0) :
    IsUnit (ι R p K t s) := by
  rw [← ι_away_algebraMap t s hs]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s).map
    (ι R p K (t.away s hs))

/-- An element of the colimit `C` is a unit if and only if its image under `ψ : C → K` is
nonzero. -/
lemma isUnit_iff_eval_ne_zero (x : colim R p K) : IsUnit x ↔ eval R p K x ≠ 0 := by
  refine ⟨fun h ↦ (h.map (eval R p K)).ne_zero, fun h ↦ ?_⟩
  obtain ⟨t, s, rfl⟩ := exists_ι_eq R p K x
  rw [eval_ι] at h
  exact isUnit_ι_of_toAlgHom_ne_zero t s h

instance : Nontrivial (colim R p K) :=
  ⟨⟨0, 1, fun h ↦ by simpa using congr(eval R p K $h)⟩⟩

/-- The colimit `C` over the étale triples is a local ring.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
instance instIsLocalRingColim : IsLocalRing (colim R p K) :=
  .of_nonunits_add fun a b ha hb ↦ by
    rw [mem_nonunits_iff, isUnit_iff_eval_ne_zero, not_not] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]

/-- The maximal ideal of `C` is the kernel of `ψ : C → K`.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
lemma maximalIdeal_colim_eq_ker : maximalIdeal (colim R p K) = RingHom.ker (eval R p K) := by
  ext x
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_eval_ne_zero, not_not, RingHom.mem_ker]

/-- The preimage of the maximal ideal of `C` in `R` is `p`.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
lemma comap_maximalIdeal_colim :
    (maximalIdeal (colim R p K)).comap (algebraMap R (colim R p K)) = p := by
  ext r
  rw [Ideal.mem_comap, maximalIdeal_colim_eq_ker, RingHom.mem_ker, AlgHom.commutes,
    ← RingHom.mem_ker, ker_algebraMap R p K]

omit [Algebra p.ResidueField K] [IsScalarTower R p.ResidueField K] in
/-- For an étale algebra the prime below generates the maximal ideal at a prime: if `s ∈ q`,
some `u ∉ q` has `us ∈ pS`. This is `Algebra.isUnramifiedAt_iff_map_eq`
(blueprint: `lem-weil-pbc-etale-prime-generates-maximal`) made elementwise. -/
lemma exists_mul_mem_map_of_mem (t : EtaleTriple R p K) {s : t.S} (hs : s ∈ t.q) :
    ∃ u ∉ t.q, u * s ∈ p.map (algebraMap R t.S) := by
  have : t.q.LiesOver p := ⟨t.comap_eq.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p t.q
  have h := ((Algebra.isUnramifiedAt_iff_map_eq R p t.q).mp inferInstance).2
  have hs' : algebraMap t.S (Localization.AtPrime t.q) s ∈
      (p.map (algebraMap R t.S)).map (algebraMap t.S (Localization.AtPrime t.q)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, h,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hs
  obtain ⟨⟨y, ⟨m, hm⟩⟩, hy⟩ :=
    (IsLocalization.mem_map_algebraMap_iff t.q.primeCompl _).mp hs'
  dsimp only at hy
  rw [← map_mul, IsLocalization.eq_iff_exists t.q.primeCompl] at hy
  obtain ⟨⟨c, hc⟩, hc'⟩ := hy
  refine ⟨c * m, fun h ↦ (t.q.primeCompl.mul_mem hc hm) h, ?_⟩
  dsimp only at hc'
  rw [mul_assoc, mul_comm m, hc']
  exact Ideal.mul_mem_left _ _ y.2

/-- **The maximal ideal of the colimit is `pC`.**

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
lemma maximalIdeal_colim_eq_map :
    maximalIdeal (colim R p K) = p.map (algebraMap R (colim R p K)) := by
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.map_le_iff_le_comap.mpr comap_maximalIdeal_colim.ge)
  rw [maximalIdeal_colim_eq_ker, RingHom.mem_ker] at hx
  obtain ⟨t, s, rfl⟩ := exists_ι_eq R p K x
  rw [eval_ι] at hx
  have hs : s ∈ t.q := by rw [← ker_toAlgHom]; exact hx
  obtain ⟨u, hu, hus⟩ := exists_mul_mem_map_of_mem t hs
  have hu' : t.toAlgHom u ≠ 0 := fun h ↦ hu (by rw [← ker_toAlgHom]; exact h)
  rw [← ι_away_algebraMap t u hu']
  have hmem : algebraMap t.S (Localization.Away u) s ∈
      p.map (algebraMap R (Localization.Away u)) := by
    have h1 : algebraMap t.S (Localization.Away u) (u * s) ∈
        p.map (algebraMap R (Localization.Away u)) := by
      rw [IsScalarTower.algebraMap_eq R t.S (Localization.Away u), ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ hus
    obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away u) u
    have : algebraMap t.S (Localization.Away u) s =
        ↑v⁻¹ * algebraMap t.S (Localization.Away u) (u * s) := by
      rw [map_mul, ← hv, Units.inv_mul_cancel_left]
    rw [this]
    exact Ideal.mul_mem_left _ _ h1
  have := Ideal.mem_map_of_mem (ι R p K (t.away u hu')).toRingHom hmem
  have h2 : ((ι R p K (t.away u hu')).toRingHom).comp (algebraMap R (Localization.Away u)) =
      algebraMap R (colim R p K) :=
    RingHom.ext fun r ↦ (ι R p K (t.away u hu')).commutes r
  rwa [Ideal.map_map, h2] at this

/-- A monic polynomial over the colimit `C` is the image of a monic polynomial over the algebra of
some étale triple. -/
lemma exists_monic_map_eq (P : (colim R p K)[X]) (hP : P.Monic) :
    ∃ (t : EtaleTriple R p K) (Q : t.S[X]), Q.Monic ∧ Q.map (ι R p K t).toRingHom = P := by
  classical
  choose t s hs using fun i : Fin P.natDegree ↦ exists_ι_eq R p K (P.coeff i)
  let c := IsFiltered.cocone (Discrete.functor t)
  let Q : c.pt.S[X] :=
    X ^ P.natDegree + ∑ i : Fin P.natDegree, C ((c.ι.app ⟨i⟩).β (s i)) * X ^ (i : ℕ)
  refine ⟨c.pt, Q, monic_X_pow_add (degree_sum_fin_lt _), ?_⟩
  conv_rhs => rw [hP.as_sum]
  simp only [Q, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
    Polynomial.map_mul]
  congr 1
  rw [Finset.sum_range (fun i ↦ C (P.coeff i) * X ^ i)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [Polynomial.map_C]
  rw [← hs i]
  congr 2
  exact congr($(ι_comp_β R p K (c.ι.app ⟨i⟩)) (s i))

/-- **Simple roots in `K` lift to the colimit.** If `P` is a monic polynomial over `C` whose image
under `ψ : C → K` has a simple root `a₀ ∈ K`, then `P` has a root `a ∈ C` with `ψ(a) = a₀`: the
root `X` of the standard étale algebra `S[X][1/Q']/(Q)` of a lift `Q` of `P`.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
theorem exists_isRoot_and_eval_eq (P : (colim R p K)[X]) (hP : P.Monic) (a₀ : K)
    (h₁ : P.eval₂ (eval R p K).toRingHom a₀ = 0)
    (h₂ : (derivative P).eval₂ (eval R p K).toRingHom a₀ ≠ 0) :
    ∃ a, P.IsRoot a ∧ eval R p K a = a₀ := by
  obtain ⟨t, Q, hQ, rfl⟩ := exists_monic_map_eq P hP
  have hev : (eval R p K).toRingHom.comp (ι R p K t).toRingHom = t.toAlgHom.toRingHom :=
    RingHom.ext fun s ↦ eval_ι R p K t s
  rw [eval₂_map, hev] at h₁
  rw [derivative_map, eval₂_map, hev] at h₂
  let SP : StandardEtalePair t.S := ⟨Q, hQ, derivative Q, ⟨1, 0, 1, by ring⟩⟩
  let : Algebra R SP.Ring := ((algebraMap t.S SP.Ring).comp (algebraMap R t.S)).toAlgebra
  have : IsScalarTower R t.S SP.Ring := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale R SP.Ring := Algebra.Etale.comp R t.S SP.Ring
  let : Algebra t.S K := t.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower R t.S K :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (t.toAlgHom.commutes r).symm
  have hmap : SP.HasMap a₀ := ⟨h₁, isUnit_iff_ne_zero.mpr h₂⟩
  let χ : SP.Ring →ₐ[t.S] K := SP.lift a₀ hmap
  let t' := ofAlgHom (ker_algebraMap R p K) SP.Ring (χ.restrictScalars R)
  let f : t ⟶ t' := homMk (t' := t') (IsScalarTower.toAlgHom R t.S SP.Ring) <| by
    rw [toAlgHom_ofAlgHom]
    ext s
    exact χ.commutes s
  have key : (ι R p K t).toRingHom =
      (ι R p K t').toRingHom.comp (algebraMap t.S SP.Ring) :=
    RingHom.ext fun s ↦ congr($(ι_comp_β R p K f) s).symm
  refine ⟨ι R p K t' SP.X, ?_, ?_⟩
  · rw [IsRoot, eval_map, key]
    change eval₂ ((ι R p K t').toRingHom.comp (algebraMap t.S SP.Ring))
      ((ι R p K t').toRingHom SP.X) Q = 0
    rw [← hom_eval₂]
    change (ι R p K t').toRingHom (aeval SP.X SP.f) = 0
    rw [SP.hasMap_X.1, map_zero]
  · rw [eval_ι, toAlgHom_ofAlgHom]
    exact SP.lift_X a₀ hmap

instance : IsLocalHom (eval R p K).toRingHom :=
  ⟨fun x hx ↦ (isUnit_iff_eval_ne_zero x).mpr hx.ne_zero⟩

/-- The image of `κ(p)` in `K` lies in the image of `ψ : C → K`. -/
lemma algebraMap_mem_range_eval (x : p.ResidueField) :
    algebraMap p.ResidueField K x ∈ Set.range (eval R p K) := by
  obtain ⟨⟨a, b, hb⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (R ⧸ p)) x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hs : algebraMap R K s ≠ 0 := by
    intro h
    rw [← RingHom.mem_ker, ker_algebraMap R p K] at h
    exact nonZeroDivisors.ne_zero hb (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hu : IsUnit (algebraMap R (colim R p K) s) :=
    (isUnit_iff_eval_ne_zero _).mpr (by rwa [AlgHom.commutes])
  refine ⟨algebraMap R _ r * ↑hu.unit⁻¹, ?_⟩
  dsimp only
  have hR (r : R) : algebraMap p.ResidueField K
      (algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r)) = algebraMap R K r := by
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply R (R ⧸ p),
      ← IsScalarTower.algebraMap_apply R p.ResidueField K]
  rw [map_mul, AlgHom.commutes, IsFractionRing.mk'_eq_div, map_div₀, hR, hR, div_eq_mul_inv]
  congr 1
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← AlgHom.commutes (eval R p K), ← map_mul, IsUnit.val_inv_mul, map_one]

variable [Algebra.IsSeparable p.ResidueField K]

/-- **The map `ψ : C → K` is surjective** when `K` is separable algebraic over `κ(p)`: every
element of `K` is a simple root of its minimal polynomial over `κ(p)`, which lifts to a monic
polynomial over `C`.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
theorem eval_surjective : Function.Surjective (eval R p K) := by
  intro α
  have hsep : IsSeparable p.ResidueField α := Algebra.IsSeparable.isSeparable _ α
  have hg : (minpoly p.ResidueField α).map (algebraMap p.ResidueField K) ∈
      Polynomial.lifts (eval R p K).toRingHom := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_map]
    exact algebraMap_mem_range_eval _
  obtain ⟨P, hP, -, hPm⟩ := lifts_and_natDegree_eq_and_monic hg
    ((minpoly.monic hsep.isIntegral).map _)
  obtain ⟨a, -, ha⟩ := exists_isRoot_and_eval_eq P hPm α
    (by rw [eval₂_eq_eval_map, hP, eval_map, ← aeval_def, minpoly.aeval])
    (by
      rw [eval₂_eq_eval_map, ← derivative_map, hP, derivative_map, eval_map, ← aeval_def]
      exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _))
  exact ⟨a, ha⟩

/-- The residue field of `C` is `K`: the isomorphism induced by `ψ : C → K`.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
noncomputable def residueFieldEquiv : ResidueField (colim R p K) ≃+* K :=
  RingEquiv.ofBijective (ResidueField.lift (eval R p K).toRingHom)
    ⟨(ResidueField.lift _).injective, fun α ↦ by
      obtain ⟨a, rfl⟩ := eval_surjective (R := R) (p := p) α
      exact ⟨residue _ a, rfl⟩⟩

@[simp]
lemma residueFieldEquiv_residue (x : colim R p K) :
    residueFieldEquiv (residue _ x) = eval R p K x :=
  rfl

/-- **The colimit over étale triples is henselian**: a simple root in the residue field `K` of a
monic polynomial over `C` lifts (`EtaleTriple.exists_isRoot_and_eval_eq`).

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
instance henselianLocalRing_colim : HenselianLocalRing (colim R p K) := by
  refine ((HenselianLocalRing.TFAE _).out 2 1).mp fun f hf a₀ h₁ h₂ ↦ ?_
  let e : ResidueField (colim R p K) ≃+* K := residueFieldEquiv
  have he : (e : ResidueField (colim R p K) →+* K).comp (residue _) = (eval R p K).toRingHom :=
    RingHom.ext fun _ ↦ rfl
  have key (g : (colim R p K)[X]) :
      g.eval₂ (eval R p K).toRingHom (e a₀) = e (aeval a₀ g) := by
    change _ = (e : ResidueField (colim R p K) →+* K) (eval₂ (algebraMap _ _) a₀ g)
    rw [hom_eval₂, ResidueField.algebraMap_eq, he]
    rfl
  obtain ⟨a, ha, hae⟩ := exists_isRoot_and_eval_eq f hf (e a₀)
    (by rw [key, h₁, map_zero]) (by rw [key]; exact (map_ne_zero e).mpr h₂)
  exact ⟨a, ha, e.injective ((residueFieldEquiv_residue a).trans hae)⟩

/-- **The colimit over étale triples is strictly henselian** when `K` is a separable closure of
`κ(p)`: it is henselian with residue field `K`.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
instance isStrictlyHenselianLocalRing_colim [IsSepClosed K] :
    IsStrictlyHenselianLocalRing (colim R p K) where
  isSepClosed_residueField := IsSepClosed.of_ringEquiv (residueFieldEquiv).symm

end EtaleTriple
