/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.KrullDimension.LocalRing

/-!
# Discrete valuation rings dominating noetherian local domains

Every noetherian local domain `O` which is not a field is dominated by a discrete valuation
ring: there is an injective local homomorphism from `O` to a discrete valuation ring
(Stacks `00PH`). In the one-dimensional case, every valuation ring of the fraction field of `O`
dominating `O` is discrete, by a length estimate in the spirit of the Krull–Akizuki theorem. The
general case reduces to the one-dimensional case by an affine blowup of the maximal ideal.

Geometrically, a specialisation `x' ⤳ x` of points of a locally noetherian scheme is the image of
the specialisation of the generic point to the closed point of the spectrum of a discrete
valuation ring (Stacks `054F`).

## Main statements

- `ValuationSubring.isDiscreteValuationRing_of_ringKrullDim_eq_one`: a valuation ring of the
  fraction field of a one-dimensional noetherian local domain `O` dominating `O` is discrete.
- `IsLocalRing.exists_isDiscreteValuationRing`: a noetherian local domain which is not a field is
  dominated by a discrete valuation ring.
- `Ideal.exists_isDiscreteValuationRing_of_lt`: for primes `p < q` of a noetherian ring `B` there
  is a homomorphism from `B` to a discrete valuation ring with kernel `p` under which the maximal
  ideal pulls back to `q`.

## References

- Stacks Project, Tags `00PH`, `054F`
-/

@[expose] public section

universe u

open IsLocalRing Pointwise

/-- If `f 0 < f 1 < ⋯ < f m`, then the coheight of `f 0` is at least `m` plus the coheight of
`f m`. -/
lemma Order.coheight_add_le_of_lt_succ {α : Type*} [Preorder α] {f : ℕ → α} (m : ℕ)
    (hf : ∀ i < m, f i < f (i + 1)) : Order.coheight (f m) + m ≤ Order.coheight (f 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc Order.coheight (f (m + 1)) + (m + 1 : ℕ) = (Order.coheight (f (m + 1)) + 1) + m := by
          push_cast
          ring
      _ ≤ Order.coheight (f m) + m := by
          gcongr
          exact Order.coheight_add_one_le (hf m (Nat.lt_succ_self m))
      _ ≤ _ := ih fun i hi ↦ hf i (by omega)

/-- For a nonzero divisor `a` and an ideal `I`, the coheight of `a • I` (i.e. the length of
`R ⧸ a • I`) is the coheight of `I` plus the order of vanishing of `a`. -/
lemma Ideal.coheight_smul {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R)
    (I : Ideal R) : Order.coheight (a • I) = Order.coheight I + Ring.ord R a := by
  rw [← Module.length_quotient, ← Module.length_quotient, Ring.ord,
    Module.length_eq_add_of_exact _ _ (Ideal.mulQuot_injective I ha)
      (Ideal.quotOfMul_surjective I) (Ideal.exact_mulQuot_quotOfMul I)]

/-- Let `O` be a noetherian domain of dimension at most one with fraction field `K`, and `V` a
valuation ring of `K` containing `O`. A strictly increasing chain of ideals `f 0 < ⋯ < f m` of `V`
with `0 ≠ a ∈ f 0` for some `a ∈ O` has length at most the length of `O ⧸ a O`. -/
lemma ValuationSubring.coe_le_ord_of_strictMono {O K : Type*} [CommRing O] [IsDomain O]
    [IsNoetherianRing O] [Ring.KrullDimLE 1 O] [Field K] [Algebra O K] [IsFractionRing O K]
    (V : ValuationSubring K) (hV : ∀ x : O, algebraMap O K x ∈ V) {f : ℕ → Ideal V}
    (hf : StrictMono f) {a : O} (ha : a ≠ 0)
    (haf : (algebraMap O K).codRestrict V hV a ∈ f 0) (m : ℕ) :
    (m : ℕ∞) ≤ Ring.ord O a := by
  set φ : O →+* V := (algebraMap O K).codRestrict V hV
  have hφ : Function.Injective φ := fun x y h ↦
    IsFractionRing.injective O K (congrArg Subtype.val h)
  have hx (i : ℕ) : ∃ x : V, x ∈ f (i + 1) ∧ x ∉ f i :=
    IsConcreteLE.exists_of_lt (hf i.lt_succ_self)
  choose x hx₁ hx₂ using hx
  obtain ⟨⟨c, hc⟩, hcx⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.range m) (fun i ↦ (x i : K))
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hφc : φ c ≠ 0 := by simpa [map_eq_zero_iff φ hφ] using hc0
  set Q : ℕ → Ideal O := fun i ↦ (Ideal.span {φ c} * f i).comap φ
  have hQ : ∀ i < m, Q i < Q (i + 1) := by
    intro i hi
    obtain ⟨y, hy⟩ := hcx i (Finset.mem_range.2 hi)
    have hy' : φ y = φ c * x i := Subtype.ext (by simpa [φ, Algebra.smul_def] using hy)
    refine lt_of_le_of_ne (Ideal.comap_mono (Ideal.mul_mono_right (hf.monotone i.le_succ)))
      fun h ↦ hx₂ i ?_
    have : y ∈ Q i := h ▸ Ideal.mem_comap.2 (Ideal.mem_span_singleton_mul.2 ⟨x i, hx₁ i, hy'.symm⟩)
    obtain ⟨z, hz, hzy⟩ := Ideal.mem_span_singleton_mul.1 (Ideal.mem_comap.1 this)
    rwa [← mul_left_cancel₀ hφc (hzy.trans hy')]
  have hsmul : a • Q m ≤ Q 0 := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, -, hzy⟩ := Ideal.mem_span_singleton_mul.1 (Ideal.mem_comap.1 hy)
    refine Ideal.mem_comap.2 (Ideal.mem_span_singleton_mul.2 ⟨φ a * z, ?_, ?_⟩)
    · exact Ideal.mul_mem_right _ _ haf
    · simp [← hzy]
      ring
  have hfin : Order.coheight (Q m) ≠ ⊤ := by
    have hca : c * a ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hc0 ha)
    have := Ring.ord_ne_top (R := O) hca
    rw [Ring.ord, Module.length_quotient] at this
    refine ne_top_of_le_ne_top this (Order.coheight_anti ((Ideal.span_singleton_le_iff_mem
      (I := Q m)).2 ?_))
    refine Ideal.comap_mono (Ideal.mul_mono_right (hf.monotone (Nat.zero_le m))) ?_
    exact Ideal.mem_comap.2 (Ideal.mem_span_singleton_mul.2 ⟨φ a, haf, by simp⟩)
  have key := (Order.coheight_add_le_of_lt_succ m hQ).trans (Order.coheight_anti hsmul)
  rw [Ideal.coheight_smul (mem_nonZeroDivisors_of_ne_zero ha)] at key
  exact (WithTop.add_le_add_iff_left hfin).1 key

/-- **Valuation rings dominating a one-dimensional noetherian local domain are discrete.** Let
`O` be a noetherian local domain of dimension one with fraction field `K`, and `V` a valuation
ring of `K` dominating `O`. Then `V` is a discrete valuation ring.

For `0 ≠ r ∈ O`, every strict chain of ideals of `V` containing `r` has length at most the length
of `O ⧸ r O` (`ValuationSubring.coe_le_ord_of_strictMono`): clearing denominators turns it into a
strict chain of ideals of `O`. Hence `V` is noetherian, so it is a discrete valuation ring. -/
theorem ValuationSubring.isDiscreteValuationRing_of_ringKrullDim_eq_one {O K : Type*}
    [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (hdim : ringKrullDim O = 1) (V : ValuationSubring K)
    (hV : ∀ x : O, algebraMap O K x ∈ V)
    (hloc : ∀ x ∈ maximalIdeal O, V.valuation (algebraMap O K x) < 1) :
    IsDiscreteValuationRing V := by
  have : Ring.KrullDimLE 1 O := Ring.krullDimLE_iff.2 hdim.le
  set φ : O →+* V := (algebraMap O K).codRestrict V hV
  have hφ : Function.Injective φ := fun x y h ↦
    IsFractionRing.injective O K (congrArg Subtype.val h)
  have : IsNoetherianRing V := by
    rw [IsNoetherianRing, isNoetherian_iff, WellFoundedGT,
      RelEmbedding.wellFounded_iff_isEmpty]
    refine ⟨fun f ↦ ?_⟩
    have hf : StrictMono f := fun i j h ↦ f.map_rel_iff.2 h
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ne_bot_of_gt (hf zero_lt_one))
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) (b : K)
    have hr : φ r = b * φ s := Subtype.ext (by simp [φ, ← hrs])
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp [hb0, map_eq_zero_iff φ hφ, nonZeroDivisors.ne_zero s.2] at hr
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
      (Ring.ord_ne_top (R := O) (mem_nonZeroDivisors_of_ne_zero hr0))
    have := ValuationSubring.coe_le_ord_of_strictMono V hV (f := fun n ↦ f (n + 1))
      (hf.comp (strictMono_id.add_const 1)) hr0 (hr ▸ Ideal.mul_mem_right _ _ hb) (n + 1)
    rw [← hn] at this
    norm_cast at this
    omega
  have hnf : ¬IsField V := by
    have hO : ¬IsField O := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hdim).1
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      ((isField_iff_maximalIdeal_eq).not.1 hO)
    rw [isField_iff_maximalIdeal_eq]
    intro h
    have := (valuation_lt_one_iff V (φ x)).2 (hloc x hx)
    rw [h, Ideal.mem_bot, map_eq_zero_iff φ hφ] at this
    exact hx0 this
  have h := (IsDiscreteValuationRing.TFAE V hnf).out 1 2
  exact h.2 inferInstance

/-- A one-dimensional noetherian local domain is dominated by a discrete valuation ring. -/
lemma IsLocalRing.exists_isDiscreteValuationRing_of_ringKrullDim_eq_one {O : Type u}
    [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] (hdim : ringKrullDim O = 1) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : O →+* R), Function.Injective f ∧ IsLocalHom f := by
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap O (FractionRing O))
  refine ⟨V, inferInstance, inferInstance,
    V.isDiscreteValuationRing_of_ringKrullDim_eq_one hdim hV fun x hx ↦
      (ValuationSubring.valuation_lt_one_iff V _).1
        ((map_mem_nonunits_iff ((algebraMap O _).codRestrict V.toSubring hV) x).2 hx),
    _, fun x y h ↦ IsFractionRing.injective O _ (congrArg Subtype.val h), hloc⟩

/-- A noetherian local domain `O` which is not a field is dominated by a one-dimensional
noetherian local domain. It is obtained by localising the affine blowup `O[m / a]` at a minimal
prime over `a`, where `a` is a generator of `m` of maximal value for a valuation ring dominating
`O`. -/
lemma IsLocalRing.exists_ringKrullDim_eq_one {O : Type u} [CommRing O] [IsDomain O]
    [IsLocalRing O] [IsNoetherianRing O] (hO : ¬IsField O) :
    ∃ (O' : Type u) (_ : CommRing O') (_ : IsDomain O') (_ : IsLocalRing O')
      (_ : IsNoetherianRing O'), ringKrullDim O' = 1 ∧
      ∃ f : O →+* O', Function.Injective f ∧ IsLocalHom f := by
  classical
  let K := FractionRing O
  obtain ⟨W, hW, hWloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap O K)
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal O) : (maximalIdeal O).FG)
  have hm : maximalIdeal O ≠ ⊥ := (isField_iff_maximalIdeal_eq).not.1 hO
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp only [Finset.coe_empty, Submodule.span_empty] at hs
    exact hm hs.symm
  obtain ⟨a, has, hamax⟩ := s.exists_max_image (fun x ↦ W.valuation (algebraMap O K x)) hsne
  have ha0 : a ≠ 0 := by
    rintro rfl
    refine hm (hs ▸ (Submodule.span_eq_bot.2 fun x hx ↦ ?_))
    simpa using hamax x hx
  have hai : algebraMap O K a ≠ 0 := by simpa using ha0
  let g : O → K := fun x ↦ algebraMap O K x / algebraMap O K a
  let O' := Algebra.adjoin O (↑(s.image g) : Set K)
  have hO'W (y : K) (hy : y ∈ O') : y ∈ W := by
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      refine W.mem_of_valuation_le_one _ ?_
      rw [map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hai)]
      exact hamax j hj
    | algebraMap r => exact hW r
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hO'N : IsNoetherianRing O' := Algebra.FiniteType.isNoetherianRing O O'
    (h := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset _))
  let ι : O' →+* W := O'.val.toRingHom.codRestrict W fun y ↦ hO'W y y.2
  let a' : O' := algebraMap O O' a
  have ha'0 : a' ≠ 0 := fun h ↦ hai (congrArg Subtype.val h)
  have ha'P' : a' ∈ (maximalIdeal W).comap ι := Ideal.mem_comap.2 ((mem_maximalIdeal _).2
    ((map_mem_nonunits_iff ((algebraMap O K).codRestrict W.toSubring hW) a).2
      ((mem_maximalIdeal a).1 (hs ▸ Ideal.subset_span has))))
  obtain ⟨P, hP, hPP'⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).2 ha'P')
  have := hP.1.1
  have ha'P : a' ∈ P := (Ideal.span_singleton_le_iff_mem _).1 hP.1.2
  refine ⟨Localization.AtPrime P, inferInstance, inferInstance, inferInstance,
    IsLocalization.isNoetherianRing P.primeCompl _ hO'N, ?_,
    (algebraMap O' (Localization.AtPrime P)).comp (algebraMap O O'), ?_, ⟨fun x hx ↦ ?_⟩⟩
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height P]
    refine congrArg _ (le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)
      (Order.one_le_iff_ne_zero.2 (Ideal.height_eq_zero_iff_eq_bot.not.2 ?_)))
    exact fun h ↦ ha'0 (by simpa [h] using ha'P)
  · exact (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors).comp
      fun x y h ↦ IsFractionRing.injective O K (congrArg Subtype.val h)
  · by_contra hxu
    have hle : (maximalIdeal O).map (algebraMap O O') ≤ Ideal.span {a'} := by
      rw [← hs, Ideal.submodule_span_eq, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨j, hj, rfl⟩
      refine Ideal.mem_span_singleton'.2
        ⟨⟨g j, Algebra.subset_adjoin (Finset.mem_image_of_mem g hj)⟩, Subtype.ext ?_⟩
      simp [g, a', div_mul_cancel₀ _ hai]
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2
      (hP.1.2 (hle (Ideal.mem_map_of_mem _ ((mem_maximalIdeal x).2 hxu)))) hx

/-- **Noetherian local domains are dominated by discrete valuation rings** (Stacks `00PH`). A
noetherian local domain `O` which is not a field admits an injective local homomorphism to a
discrete valuation ring. -/
theorem IsLocalRing.exists_isDiscreteValuationRing {O : Type u} [CommRing O] [IsDomain O]
    [IsLocalRing O] [IsNoetherianRing O] (hO : ¬IsField O) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : O →+* R), Function.Injective f ∧ IsLocalHom f := by
  obtain ⟨O', _, _, _, _, hdim, f, hf, hfloc⟩ := exists_ringKrullDim_eq_one hO
  obtain ⟨R, _, _, _, g, hg, hgloc⟩ := exists_isDiscreteValuationRing_of_ringKrullDim_eq_one hdim
  exact ⟨R, inferInstance, inferInstance, inferInstance, g.comp f, hg.comp hf,
    RingHom.isLocalHom_comp g f⟩

/-- **Specialisations are traced by discrete valuation rings** (Stacks `054F`). For primes
`p < q` of a noetherian ring `B` there is a homomorphism `φ` from `B` to a discrete valuation
ring with kernel `p` such that the maximal ideal pulls back to `q`. -/
theorem Ideal.exists_isDiscreteValuationRing_of_lt {B : Type u} [CommRing B] [IsNoetherianRing B]
    {p q : Ideal B} [p.IsPrime] [q.IsPrime] (hpq : p < q) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (φ : B →+* R), RingHom.ker φ = p ∧ (maximalIdeal R).comap φ = q := by
  let q' := q.map (Ideal.Quotient.mk p)
  have : q'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa using hpq.le)
  let O := Localization.AtPrime q'
  have hcomap : q'.comap (Ideal.Quotient.mk p) = q := Ideal.comap_map_mk hpq.le
  have hO : ¬IsField O := by
    rw [isField_iff_maximalIdeal_eq]
    intro h
    obtain ⟨b, hbq, hbp⟩ := IsConcreteLE.exists_of_lt hpq
    have hb : algebraMap _ O (Ideal.Quotient.mk p b) ∈ maximalIdeal O :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff O q' _).2 (Ideal.mem_map_of_mem _ hbq)
    rw [h, Ideal.mem_bot, map_eq_zero_iff _ (IsLocalization.injective O
      q'.primeCompl_le_nonZeroDivisors), Ideal.Quotient.eq_zero_iff_mem] at hb
    exact hbp hb
  obtain ⟨R, _, _, _, f, hf, hfloc⟩ := IsLocalRing.exists_isDiscreteValuationRing hO
  refine ⟨R, inferInstance, inferInstance, inferInstance,
    f.comp ((algebraMap _ O).comp (Ideal.Quotient.mk p)), ?_, ?_⟩
  · rw [RingHom.ker_comp_of_injective _ hf, RingHom.ker_comp_of_injective _
      (IsLocalization.injective O q'.primeCompl_le_nonZeroDivisors), Ideal.mk_ker]
  · rw [← Ideal.comap_comap, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap,
      ← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal O q', hcomap]
