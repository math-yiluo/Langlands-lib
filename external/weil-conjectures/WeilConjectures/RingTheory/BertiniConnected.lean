/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.GenericConnectedness
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.IntegralClosure.GoingDown

/-!
# Connectedness of generic members of a linear system on a finite cover

Let `k` be an algebraically closed field, `A` a finitely generated `k`-domain of dimension `≥ 2`
and `B` a domain which is a finite torsion-free `A`-algebra. Let `v₁, …, v_M ∈ A` cut out a
finite nonempty set `S` of closed points. Then for a generic choice of `b ∈ k^M` the hypersurface
section `Spec (B ⧸ (∑ bᵢ vᵢ))` of `Spec B` is connected.

The proof considers the universal member of the linear system: over the parameter space
`R = k[X₁, …, X_M]` the ring `D = B[X₁, …, X_M] ⧸ (∑ vᵢ Xᵢ)`, whose fibre over the `k`-point
`b` is `B ⧸ (∑ bᵢ vᵢ)`. The ring `D` has a unique minimal prime: away from the base locus it is
a polynomial ring over a localisation of `B`, and by Krull's principal ideal theorem no
component of `Spec D` lies over the base locus, which has codimension `≥ 2`. Hence the generic
fibre of `Spec D → Spec R` is irreducible, and a point of the base locus gives a section, so
generic connectedness of fibres (`exists_ne_zero_forall_connectedSpace_fiber`) applies.

## Main statements

- `Ideal.ringKrullDim_le_height_of_isMaximal`: in a domain finitely generated over a field,
  maximal ideals have height at least the Krull dimension.
- `exists_ne_zero_forall_connectedSpace_quotient`: generic members of a linear system with
  finite base locus cut a finite cover in a connected scheme.

## Blueprint

- `lemma-curve-preserving-finite-cover--1`: the Bertini lemma for finite covers.
-/

@[expose] public section

universe u

open MvPolynomial TensorProduct

/-- In a domain `B` finitely generated over a field `k`, every maximal ideal has height at least
the Krull dimension of `B`: by Noether normalization `B` is finite over a polynomial ring, which is
normal, so going down holds, and maximal ideals of a polynomial ring in `n` variables have
height `n`. -/
theorem Ideal.ringKrullDim_le_height_of_isMaximal (k : Type*) {B : Type*} [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : Ideal B) [q.IsMaximal] :
    ringKrullDim B ≤ q.height := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim B = n := by
    have h := ringKrullDim_ne_top_of_finiteType k B
    have h' : (0 : WithBot ℕ∞) ≤ ringKrullDim B := ringKrullDim_nonneg_of_nontrivial
    rcases hk : ringKrullDim B with _ | _ | d
    · rw [hk] at h'
      exact absurd h' (WithBot.not_coe_le_bot 0)
    · exact absurd hk h
    · exact ⟨d, rfl⟩
  obtain ⟨g, hg, hfin⟩ := exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq k B n hn
  algebraize [g.toRingHom]
  have : Module.Finite (MvPolynomial (Fin n) k) B := hfin
  have : FaithfulSMul (MvPolynomial (Fin n) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : (q.under (MvPolynomial (Fin n) k)).IsMaximal := Ideal.IsMaximal.under _ q
  rw [hn, Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (q.under (MvPolynomial (Fin n) k)) q,
    MvPolynomial.height_eq_of_isMaximal]
  exact_mod_cast le_self_add

namespace BertiniConnected

variable {B : Type*} [CommRing B] {M : ℕ}

/-- The linear form `∑ᵢ wᵢ Xᵢ` with coefficients `w`. -/
noncomputable def linearForm (w : Fin M → B) : MvPolynomial (Fin M) B := ∑ i, C (w i) * X i

/-- The universal member `B[X₁, …, X_M] ⧸ (∑ᵢ wᵢ Xᵢ)` of the linear system spanned by `w`. -/
abbrev Universal (w : Fin M → B) : Type _ := MvPolynomial (Fin M) B ⧸ Ideal.span {linearForm w}

/-- The image of `b ∈ B` in the universal member. -/
noncomputable abbrev ofBase (w : Fin M → B) (b : B) : Universal w :=
  Ideal.Quotient.mk _ (C b)

/-- Solving the equation `∑ⱼ wⱼ Xⱼ = 0` for `Xᵢ` after inverting `wᵢ`: the substitution
`Xᵢ ↦ Xᵢ - wᵢ⁻¹ ∑ⱼ wⱼ Xⱼ`, `Xⱼ ↦ Xⱼ` for `j ≠ i`. -/
noncomputable def substHom (w : Fin M → B) (i : Fin M) :
    MvPolynomial (Fin M) B →+* MvPolynomial (Fin M) (Localization.Away (w i)) :=
  eval₂Hom (C.comp (algebraMap B _)) fun j ↦ if j = i then
    X j - C (IsLocalization.Away.invSelf (w i)) *
      MvPolynomial.map (algebraMap B _) (linearForm w) else X j

set_option backward.isDefEq.respectTransparency true in
/-- The substitution `substHom w i` kills the linear form `∑ⱼ wⱼ Xⱼ`. -/
lemma substHom_linearForm (w : Fin M → B) (i : Fin M) : substHom w i (linearForm w) = 0 := by
  set u := IsLocalization.Away.invSelf (S := Localization.Away (w i)) (w i)
  set F' := MvPolynomial.map (algebraMap B (Localization.Away (w i))) (linearForm w)
  have hF' : F' = ∑ j, C (algebraMap B _ (w j)) * X j := by simp [F', linearForm]
  have hX (j : Fin M) : substHom w i (X j) = if j = i then X j - C u * F' else X j := by
    simp [substHom, u, F']
  have hC (c : B) : substHom w i (C c) = C (algebraMap B _ c) := by
    simp [substHom]
  have h (j : Fin M) : C (algebraMap B (Localization.Away (w i)) (w j)) *
      (if j = i then X j - C u * F' else X j) = C (algebraMap B _ (w j)) * X j -
        if j = i then C (algebraMap B _ (w i) * u) * F' else 0 := by
    split_ifs with hj
    · subst hj
      rw [map_mul]
      ring
    · ring
  rw [linearForm]
  simp only [map_sum, map_mul, hX, hC]
  rw [Finset.sum_congr rfl fun j _ ↦ h j, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_univ _), IsLocalization.Away.mul_invSelf, map_one, one_mul,
    hF', sub_self]

set_option backward.isDefEq.respectTransparency true in
/-- After inverting `wᵢ`, the universal member embeds into a polynomial ring over `B[1/wᵢ]`. -/
lemma exists_injective_away (w : Fin M → B) (i : Fin M) :
    ∃ α : Localization.Away (ofBase w (w i)) →+* MvPolynomial (Fin M) (Localization.Away (w i)),
      Function.Injective α ∧
        ∀ b : B, α (algebraMap _ _ (ofBase w b)) = C (algebraMap B _ b) := by
  classical
  have hθ : ∀ a ∈ Ideal.span {linearForm w}, substHom w i a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, substHom_linearForm, mul_zero]
  let θ := Ideal.Quotient.lift _ (substHom w i) hθ
  have hθC (b : B) : θ (ofBase w b) = C (algebraMap B _ b) := by
    simp [θ, ofBase, substHom]
  have hu : IsUnit (θ (ofBase w (w i))) := by
    rw [hθC]
    exact (IsLocalization.Away.algebraMap_isUnit (w i)).map C
  let α := IsLocalization.Away.lift (S := Localization.Away (ofBase w (w i))) _ hu
  have hα (b : B) : α (algebraMap _ _ (ofBase w b)) = C (algebraMap B _ b) := by
    rw [IsLocalization.Away.lift_eq, hθC]
  let g : B →+* Localization.Away (ofBase w (w i)) :=
    (algebraMap _ _).comp ((Ideal.Quotient.mk (Ideal.span {linearForm w})).comp C)
  have hg : IsUnit (g (w i)) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (ofBase w (w i))) (ofBase w (w i))
  let β : MvPolynomial (Fin M) (Localization.Away (w i)) →+*
      Localization.Away (ofBase w (w i)) :=
    eval₂Hom (IsLocalization.Away.lift (S := Localization.Away (w i)) (w i) hg) fun j ↦
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {linearForm w}) (X j))
  have hβmap : β.comp (MvPolynomial.map (algebraMap B _)) =
      (algebraMap _ _).comp (Ideal.Quotient.mk (Ideal.span {linearForm w})) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [β, g, IsLocalization.Away.lift_eq]
    · intro j
      simp [β]
  have hβF : β (MvPolynomial.map (algebraMap B _) (linearForm w)) = 0 := by
    rw [← RingHom.comp_apply, hβmap, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  have hβα : β.comp α = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (ofBase w (w i)))
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [hα]
      simp [β, g, IsLocalization.Away.lift_eq]
    · intro j
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [IsLocalization.Away.lift_eq]
      by_cases hj : j = i
      · subst hj
        have hθX : θ (Ideal.Quotient.mk _ (X j)) = X j - C (IsLocalization.Away.invSelf (w j)) *
            MvPolynomial.map (algebraMap B _) (linearForm w) := by
          simp [θ, substHom]
        rw [hθX, map_sub, map_mul, hβF, mul_zero, sub_zero]
        simp [β]
      · simp [θ, substHom, β, hj]
  exact ⟨α, Function.LeftInverse.injective (g := β) fun x ↦ congr($hβα x), hα⟩

/-- After inverting a nonzero `wᵢ`, the universal member becomes a domain. -/
lemma isDomain_away [IsDomain B] (w : Fin M → B) {i : Fin M} (hi : w i ≠ 0) :
    IsDomain (Localization.Away (ofBase w (w i))) := by
  obtain ⟨α, hα, -⟩ := exists_injective_away w i
  have : IsDomain (Localization.Away (w i)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hi)
  exact hα.isDomain α

/-- After inverting a nonzero `wᵢ`, the image of a nonzero `wⱼ` in the universal member stays
nonzero. -/
lemma algebraMap_ofBase_ne_zero [IsDomain B] (w : Fin M → B) {i j : Fin M} (hi : w i ≠ 0)
    (hj : w j ≠ 0) : algebraMap _ (Localization.Away (ofBase w (w i))) (ofBase w (w j)) ≠ 0 := by
  obtain ⟨α, -, hα⟩ := exists_injective_away w i
  have hinj : Function.Injective (algebraMap B (Localization.Away (w i))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hi)
  intro h
  have := hα (w j)
  rw [h, map_zero, eq_comm, C_eq_zero, map_eq_zero_iff _ hinj] at this
  exact hj this

/-- The kernel of the localisation of a ring at `x` lies in every prime not containing `x`. -/
lemma ker_algebraMap_away_le {D : Type*} [CommRing D] (x : D) (P : Ideal D) [P.IsPrime]
    (hP : x ∉ P) : RingHom.ker (algebraMap D (Localization.Away x)) ≤ P := by
  intro y hy
  obtain ⟨⟨_, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers x) _ y).mp hy
  exact ((‹P.IsPrime›.mem_or_mem (hm ▸ P.zero_mem)).resolve_left
    fun h ↦ hP (‹P.IsPrime›.mem_of_pow_mem n h))

/-- **Krull's principal ideal theorem** applied to the universal member: if every prime of `B`
containing all `wᵢ` has height `≥ 2`, then no minimal prime of the universal member contains all
`wᵢ`. -/
lemma exists_notMem_of_mem_minimalPrimes [IsNoetherianRing B] (w : Fin M → B)
    (h2 : ∀ q : Ideal B, q.IsPrime → (∀ i, w i ∈ q) → 2 ≤ q.height)
    {P : Ideal (Universal w)} (hP : P ∈ minimalPrimes (Universal w)) :
    ∃ i, ofBase w (w i) ∉ P := by
  by_contra! h
  set P₁ := P.comap (Ideal.Quotient.mk (Ideal.span {linearForm w}))
  have hP₁ : P₁ ∈ (Ideal.span {linearForm w}).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨P, hP, rfl⟩
  have := hP₁.1.1
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP₁
  have hq := h2 (P₁.under B) inferInstance fun i ↦ h i
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P₁.under B) P₁] at hle
  have := hq.trans (le_self_add.trans hle)
  exact absurd this (by norm_num)

/-- The universal member has a prime contained in all its primes, provided it has some prime and
every prime of `B` containing all `wᵢ` has height `≥ 2`. -/
lemma exists_isPrime_forall_le [IsDomain B] [IsNoetherianRing B] (w : Fin M → B)
    (h2 : ∀ q : Ideal B, q.IsPrime → (∀ i, w i ∈ q) → 2 ≤ q.height)
    (P₀ : Ideal (Universal w)) [P₀.IsPrime] :
    ∃ Q : Ideal (Universal w), Q.IsPrime ∧ ∀ P : Ideal (Universal w), P.IsPrime → Q ≤ P := by
  have hne {P : Ideal (Universal w)} {i : Fin M} (hi : ofBase w (w i) ∉ P) : w i ≠ 0 := by
    rintro h
    rw [h, ofBase, map_zero, map_zero] at hi
    exact hi P.zero_mem
  obtain ⟨P₁, hP₁, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ P₀)
  obtain ⟨i, hi⟩ := exists_notMem_of_mem_minimalPrimes w h2 hP₁
  have := isDomain_away w (hne hi)
  refine ⟨_, RingHom.ker_isPrime (algebraMap _ (Localization.Away (ofBase w (w i)))),
    fun P hP ↦ ?_⟩
  obtain ⟨P₂, hP₂, hle⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ P)
  obtain ⟨j, hj⟩ := exists_notMem_of_mem_minimalPrimes w h2 hP₂
  have := isDomain_away w (hne hj)
  have := hP₂.1.1
  have := RingHom.ker_isPrime (algebraMap (Universal w) (Localization.Away (ofBase w (w j))))
  refine (ker_algebraMap_away_le (ofBase w (w i)) _ fun h ↦ ?_).trans
    ((ker_algebraMap_away_le _ _ hj).trans hle)
  exact algebraMap_ofBase_ne_zero w (hne hj) (hne hi) h

end BertiniConnected

/-- Let `D` be an algebra over a domain `R` with fraction field `K`. If `D` has a prime `Q`
contained in every prime of `D` and lying over `0`, then the generic fibre `Spec (K ⊗[R] D)` is
irreducible. -/
lemma irreducibleSpace_tensor_of_forall_le {R D : Type*} [CommRing R] [IsDomain R] [CommRing D]
    [Algebra R D] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (Q : Ideal D)
    [Q.IsPrime] (hQ : ∀ P : Ideal D, P.IsPrime → Q ≤ P) (hQ0 : Q.comap (algebraMap R D) = ⊥) :
    IrreducibleSpace (PrimeSpectrum (K ⊗[R] D)) := by
  let : Algebra D (K ⊗[R] D) := Algebra.TensorProduct.rightAlgebra
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid D (nonZeroDivisors R) : Set D) Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    have : r ∈ Q.comap (algebraMap R D) := hrQ
    rw [hQ0, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hr this
  have hQ' : (Q.map (algebraMap D (K ⊗[R] D))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Algebra.algebraMapSubmonoid D (nonZeroDivisors R))
      _ Q ‹_› hdisj
  have huniv : closure {(⟨_, hQ'⟩ : PrimeSpectrum (K ⊗[R] D))} = Set.univ := by
    rw [PrimeSpectrum.closure_singleton]
    refine Set.eq_univ_of_forall fun P ↦ ?_
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    exact Ideal.map_le_iff_le_comap.mpr (hQ _ (Ideal.IsPrime.comap _))
  rw [irreducibleSpace_def, Set.top_eq_univ, ← huniv]
  exact isIrreducible_singleton.closure

attribute [local instance] MvPolynomial.algebraMvPolynomial in
open BertiniConnected in
set_option backward.isDefEq.respectTransparency true in
/-- The fibre of the universal member over the `k`-point `b` of the parameter space surjects on
spectra onto `Spec (B ⧸ (∑ bᵢ wᵢ))`; in particular connectedness of the fibre passes to this
hypersurface section. -/
lemma BertiniConnected.connectedSpace_quotient_of_fiber {k B : Type*} [Field k] [CommRing B]
    [Algebra k B] {M : ℕ} (w : Fin M → B) (b : Fin M → k)
    (p : PrimeSpectrum (MvPolynomial (Fin M) k))
    (hp : p.asIdeal = RingHom.ker (MvPolynomial.eval b))
    (h : ConnectedSpace (PrimeSpectrum
      (p.asIdeal.ResidueField ⊗[MvPolynomial (Fin M) k] Universal w))) :
    ConnectedSpace (PrimeSpectrum (B ⧸ Ideal.span {∑ i, b i • w i})) := by
  classical
  let : Algebra (MvPolynomial (Fin M) k) B :=
    ((algebraMap k B).comp (MvPolynomial.eval b)).toAlgebra
  have hRB (r : MvPolynomial (Fin M) k) :
      algebraMap (MvPolynomial (Fin M) k) B r = algebraMap k B (MvPolynomial.eval b r) := rfl
  have hcomm (r : MvPolynomial (Fin M) k) :
      MvPolynomial.eval (fun i ↦ algebraMap k B (b i)) (algebraMap _ (MvPolynomial (Fin M) B) r) =
        algebraMap (MvPolynomial (Fin M) k) B r := by
    rw [MvPolynomial.algebraMap_def, MvPolynomial.eval_map, hRB]
    induction r using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [eval₂_add, hp, hq]
    | mul_X p i hp => simp [hp]
  let g₀ : MvPolynomial (Fin M) B →ₐ[MvPolynomial (Fin M) k] B :=
    { MvPolynomial.eval (fun i ↦ algebraMap k B (b i)) with commutes' := hcomm }
  have hg₀ : ∀ a ∈ Ideal.span {linearForm w},
      Ideal.Quotient.mkₐ (MvPolynomial (Fin M) k) (Ideal.span {∑ i, b i • w i}) (g₀ a) = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_mul]
    refine mul_eq_zero_of_right _ (Ideal.Quotient.eq_zero_iff_mem.mpr ?_)
    convert Ideal.mem_span_singleton_self (∑ i, b i • w i) using 1
    simp [g₀, linearForm, Algebra.smul_def, mul_comm]
  let g : Universal w →ₐ[MvPolynomial (Fin M) k] B ⧸ Ideal.span {∑ i, b i • w i} :=
    Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ _ _).comp g₀) hg₀
  let fκ : p.asIdeal.ResidueField →ₐ[MvPolynomial (Fin M) k]
      B ⧸ Ideal.span {∑ i, b i • w i} :=
    Ideal.ResidueField.liftₐ p.asIdeal (Algebra.ofId _ _)
      (fun x hx ↦ by
        rw [hp, RingHom.mem_ker] at hx
        rw [RingHom.mem_ker, Algebra.ofId_apply, ← Ideal.Quotient.mk_algebraMap, hRB, hx, map_zero,
          map_zero])
      (fun x hx ↦ by
        have hx' : MvPolynomial.eval b x ≠ 0 := by
          rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
            SetLike.mem_coe, hp, RingHom.mem_ker] at hx
          exact hx
        exact (Ne.isUnit hx').map (algebraMap k (B ⧸ Ideal.span {∑ i, b i • w i})))
  let ψ := Algebra.TensorProduct.lift fκ g fun _ _ ↦ Commute.all _ _
  have key : (C (∑ i, b i • w i) : MvPolynomial (Fin M) B) = linearForm w +
      ∑ i, algebraMap (MvPolynomial (Fin M) k) _ (C (b i) - X i) * C (w i) := by
    simp only [linearForm, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [Algebra.smul_def]
    ring
  have hφ : ∀ a ∈ Ideal.span {∑ i, b i • w i}, (Algebra.TensorProduct.includeRight :
      Universal w →ₐ[MvPolynomial (Fin M) k] p.asIdeal.ResidueField ⊗[MvPolynomial (Fin M) k]
        Universal w) (ofBase w a) = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [ofBase, map_mul, map_mul, map_mul, key, map_add, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero, zero_add,
      map_sum, map_sum]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ ↦ ?_)
    rw [map_mul, map_mul, Ideal.Quotient.mk_algebraMap, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply,
      (Ideal.algebraMap_residueField_eq_zero (I := p.asIdeal)).mpr (by simp [hp]), zero_tmul,
      zero_mul]
  let φ : B ⧸ Ideal.span {∑ i, b i • w i} →+*
      p.asIdeal.ResidueField ⊗[MvPolynomial (Fin M) k] Universal w :=
    Ideal.Quotient.lift _ ((Algebra.TensorProduct.includeRight : Universal w →ₐ[MvPolynomial
      (Fin M) k] p.asIdeal.ResidueField ⊗[MvPolynomial (Fin M) k] Universal w).toRingHom.comp
        ((Ideal.Quotient.mk _).comp C)) hφ
  have hψφ : ψ.toRingHom.comp φ = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    set_option backward.isDefEq.respectTransparency false in
      simp [ψ, φ, g, g₀]
  have hsurj : Function.Surjective (PrimeSpectrum.comap φ) := fun x ↦
    ⟨PrimeSpectrum.comap ψ.toRingHom x, by
      rw [← PrimeSpectrum.comap_comp_apply, hψφ, PrimeSpectrum.comap_id]⟩
  exact hsurj.connectedSpace (PrimeSpectrum.continuous_comap φ)

attribute [local instance] MvPolynomial.algebraMvPolynomial in
open BertiniConnected in
set_option backward.isDefEq.respectTransparency true in
/-- **Generic members of a linear system on a finite cover are connected.** Let `k` be an
algebraically closed field, `A` a finitely generated `k`-domain of Krull dimension `≥ 2` and `B`
a domain which is a finite torsion-free `A`-algebra. Let `v₁, …, v_M ∈ A` have common zero locus
a finite nonempty set `S` of closed points of `Spec A`. Then there is a nonzero polynomial `a` in
the parameters such that `Spec (B ⧸ (∑ bᵢ vᵢ))` is connected whenever `a(b) ≠ 0`.

This is an input of the Bertini lemma for finite covers
(blueprint: `lemma-curve-preserving-finite-cover--1`). The universal member
`D = B[X₁, …, X_M] ⧸ (∑ vᵢ Xᵢ)` over `k[X₁, …, X_M]` has a unique minimal prime
(`BertiniConnected.exists_isPrime_forall_le`), since the base locus has codimension `≥ 2` in
`Spec B`; so its generic fibre is irreducible, a point of `S` provides a section, and generic
connectedness of fibres (`exists_ne_zero_forall_connectedSpace_fiber`) concludes. -/
theorem exists_ne_zero_forall_connectedSpace_quotient {k A B : Type u} [Field k]
    [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra k B] [IsScalarTower k A B] (hA : 2 ≤ ringKrullDim A) {M : ℕ} (v : Fin M → A)
    (S : Set (Ideal A)) (_hS : S.Finite) (hSmax : ∀ m ∈ S, m.IsMaximal) (hSne : S.Nonempty)
    (hvS : ∀ m ∈ S, ∀ i, v i ∈ m)
    (hbase : ∀ p : Ideal A, p.IsPrime → (∀ i, v i ∈ p) → p ∈ S) :
    ∃ a : MvPolynomial (Fin M) k, a ≠ 0 ∧ ∀ b : Fin M → k, MvPolynomial.eval b a ≠ 0 →
      ConnectedSpace (PrimeSpectrum (B ⧸ Ideal.span {algebraMap A B (∑ i, b i • v i)})) := by
  classical
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hinj : Function.Injective (algebraMap A B) := by
    refine (injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_
    have h1 : a • (1 : B) = 0 := by rw [Algebra.smul_def, ha, zero_mul]
    simpa using h1
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have hdim : ringKrullDim B = ringKrullDim A := ringKrullDim_eq_of_isIntegral A B
  set w : Fin M → B := fun i ↦ algebraMap A B (v i)
  have h2 (q : Ideal B) (hq : q.IsPrime) (hwq : ∀ i, w i ∈ q) : 2 ≤ q.height := by
    have : (q.under A).IsMaximal := hSmax _ (hbase _ (Ideal.IsPrime.under A q) hwq)
    have : q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under q this
    have h := Ideal.ringKrullDim_le_height_of_isMaximal k q
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp (hA.trans h)
  -- a point of the base locus gives a section of the universal member
  obtain ⟨m, hmS⟩ := hSne
  have := hSmax m hmS
  obtain ⟨n, hn, hnm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) m
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq_of_isMaximal k B n
  have hφw (i : Fin M) : φ (w i) = 0 := by
    rw [← RingHom.mem_ker, hφ]
    change v i ∈ n.under A
    rw [hnm]
    exact hvS m hmS i
  let s₀ : MvPolynomial (Fin M) B →ₐ[MvPolynomial (Fin M) k] MvPolynomial (Fin M) k :=
    { MvPolynomial.map (φ : B →+* k) with
      commutes' := fun r ↦ by simp [MvPolynomial.map_map, MvPolynomial.map_id] }
  have hs₀ : ∀ a ∈ Ideal.span {linearForm w}, s₀ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [s₀, linearForm, hφw]
  let s : Universal w →ₐ[MvPolynomial (Fin M) k] MvPolynomial (Fin M) k :=
    Ideal.Quotient.liftₐ _ s₀ hs₀
  -- the generic fibre of the universal member is irreducible
  have : (RingHom.ker s).IsPrime := RingHom.ker_isPrime s
  obtain ⟨Q, hQ, hQle⟩ := exists_isPrime_forall_le w h2 (RingHom.ker s)
  have hQ0 : Q.comap (algebraMap (MvPolynomial (Fin M) k) (Universal w)) = ⊥ := by
    refine eq_bot_iff.mpr fun r hr ↦ ?_
    have := hQle (RingHom.ker s) inferInstance hr
    rw [RingHom.mem_ker, AlgHom.commutes] at this
    exact this
  have hgen := irreducibleSpace_tensor_of_forall_le (FractionRing (MvPolynomial (Fin M) k)) Q
    hQle hQ0
  have : Algebra.FiniteType k (MvPolynomial (Fin M) B) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have : Algebra.FiniteType (MvPolynomial (Fin M) k) (MvPolynomial (Fin M) B) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  obtain ⟨a, ha, H⟩ := exists_ne_zero_forall_connectedSpace_fiber
    (FractionRing (MvPolynomial (Fin M) k)) s
    (@IrreducibleSpace.connectedSpace _ _ hgen)
  refine ⟨a, ha, fun b hb ↦ ?_⟩
  have hf : algebraMap A B (∑ i, b i • v i) = ∑ i, b i • w i := by
    simp [w, map_sum, Algebra.smul_def, IsScalarTower.algebraMap_apply k A B]
  rw [hf]
  exact connectedSpace_quotient_of_fiber w b ⟨_, RingHom.ker_isPrime (MvPolynomial.eval b)⟩ rfl
    (H _ hb)
