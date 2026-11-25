/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.CohomologicalDimension
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Continuous cohomology of groups with an `ℓ`-adic procyclic quotient

Let `G` be a compact group and `ℓ` a prime. Suppose given a continuous homomorphism
`χ : G → ℤ_ℓ` (written multiplicatively) and `τ ∈ G` with `χ τ = 1`, such that the kernel
`K = ker χ` has all its finite quotients of order prime to `ℓ`: for every open subgroup `U` of
`G`, the index `[K : K ∩ U]` is prime to `ℓ`. Then for every `ℓ`-primary discrete `G`-module
`M` the continuous cohomology is computed by the two-term complex `[Mᴷ --τ-1--> Mᴷ]`:

* `H⁰(G, M) = ker(τ - 1 : Mᴷ → Mᴷ)`;
* `H¹(G, M) ≃ Mᴷ / (τ - 1) Mᴷ`;
* `Hᵠ(G, M) = 0` for `q ≥ 2`.

The functor `M ↦ Mᴷ` is exact on `ℓ`-primary modules, by averaging over the finite quotients
of `K`. An invariant of `Mᴷ` under `τ` is invariant under `G`, as every open subgroup containing
`K` and `τ` is `G`. Finally `τ - 1` is surjective on the `K`-invariant smooth functions
`G → M`, by summation along the powers of `τ`; this computes `H¹` through the embedding of `M`
into its coinduced module, and shows the vanishing of `H²`.

The case `G = ℤ_ℓ`, `χ = id`, `K = 1` is blueprint `lem-exc-procyclic-two-term`.

## Main definitions and statements

- `DiscreteModule.IsEllAdicQuotient`: the hypotheses on `(G, χ, τ)`.
- `DiscreteModule.IsEllAdicQuotient.subsingleton_H`: the vanishing above degree one.
- `DiscreteModule.IsEllAdicQuotient.HOneAddEquiv`: the computation of `H¹`.
- `DiscreteModule.subsingleton_H_padicInt`, `DiscreteModule.HOnePadicIntAddEquiv`: the case of
  `ℤ_ℓ`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Action

/-- A periodic sequence sums to a multiple of the sum over one period. -/
lemma _root_.Finset.sum_range_mul_of_periodic {A : Type*} [AddCommGroup A] (F : ℕ → A) (a : ℕ)
    (hF : ∀ m i, F (a * m + i) = F i) (m : ℕ) :
    ∑ i ∈ Finset.range (a * m), F i = m • ∑ i ∈ Finset.range a, F i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [mul_add, mul_one, Finset.sum_range_add, ih, succ_nsmul]
    simp only [hF]

instance (ℓ : ℕ) [Fact ℓ.Prime] : CompactSpace (Multiplicative ℤ_[ℓ]) :=
  inferInstanceAs (CompactSpace ℤ_[ℓ])

namespace DiscreteModule

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

section averaging

/-- **Exactness of invariants under a subgroup with finite quotients prime to `ℓ`.** Let `K` be
a subgroup of the compact group `G` such that `[K : K ∩ U]` is prime to `ℓ` for every open
subgroup `U`. Then `K`-invariant elements of an `ℓ`-primary discrete module lift along
surjections to `K`-invariant elements: average an arbitrary lift over the finite quotient
`K / (K ∩ U)` by which it is acted upon. -/
lemma exists_fixed_lift {ℓ : ℕ} [Fact ℓ.Prime] (K : Subgroup G)
    (hK : ∀ U : Subgroup G, IsOpen (U : Set G) → ¬ ℓ ∣ U.relIndex K)
    {Y Z : DiscreteModule.{w} G} (p : Y ⟶ Z) (hp : Function.Surjective p.hom.hom.hom)
    (hZ : IsPrimary ℓ Z) (z : Z.obj.V) (hz : ∀ k ∈ K, (Z.obj.ρ k).asHom.hom z = z) :
    ∃ y, (∀ k ∈ K, (Y.obj.ρ k).asHom.hom y = y) ∧ p.hom.hom.hom y = z := by
  classical
  obtain ⟨y₀, rfl⟩ := hp z
  let U := Y.obj.stabilizer y₀
  have hU : IsOpen (U : Set G) := Y.isOpen_stabilizer y₀
  have := Subgroup.quotient_finite_of_isOpen U hU
  have : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let S := U.subgroupOf K
  have : Finite (K ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (K ⧸ S)
  let s : Y.obj.V := ∑ c : K ⧸ S, (Y.obj.ρ ((Quotient.out c : K) : G)).asHom.hom y₀
  have hs : ∀ k ∈ K, (Y.obj.ρ k).asHom.hom s = s := by
    intro k hk
    simp only [s, map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun c ↦ ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul S (⟨k, hk⟩ * Quotient.out c)
    have hc : (MulAction.toPerm (⟨k, hk⟩ : K) c : K ⧸ S) =
        QuotientGroup.mk (⟨k, hk⟩ * Quotient.out c) := by
      conv_lhs => rw [← QuotientGroup.out_eq' c]
      rfl
    rw [hc, hu]
    have hu' : ((u : K) : G) ∈ U := u.2
    simp only [Subgroup.coe_mul, ρ_mul_apply, mem_stabilizer.1 hu']
  have hps : p.hom.hom.hom s = (Fintype.card (K ⧸ S)) • p.hom.hom.hom y₀ := by
    simp only [s, map_sum, hom_comm_apply p.hom]
    rw [Finset.sum_congr rfl fun (c : K ⧸ S) _ ↦ hz _ (Quotient.out c).2, Finset.sum_const,
      Finset.card_univ]
  obtain ⟨j, hj⟩ := hZ (p.hom.hom.hom y₀)
  have hcard : Fintype.card (K ⧸ S) = U.relIndex K := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have hcop : IsCoprime ((U.relIndex K : ℕ) : ℤ) ((ℓ ^ j : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    rcases Nat.coprime_or_dvd_of_prime (Fact.out : ℓ.Prime) (U.relIndex K) with h | h
    · exact (Nat.Coprime.pow_right j h.symm)
    · exact absurd h (hK U hU)
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a • s, fun k hk ↦ by rw [map_zsmul, hs k hk], ?_⟩
  have hj' : ((ℓ ^ j : ℕ) : ℤ) • p.hom.hom.hom y₀ = 0 := by rw [natCast_zsmul, hj]
  rw [map_zsmul, hps, hcard, ← natCast_zsmul, smul_smul]
  calc (a * (U.relIndex K : ℤ)) • p.hom.hom.hom y₀
      = (a * (U.relIndex K : ℤ) + b * ((ℓ ^ j : ℕ) : ℤ)) • p.hom.hom.hom y₀ := by
        rw [add_smul, mul_smul b, hj', smul_zero, add_zero]
    _ = p.hom.hom.hom y₀ := by rw [hab, one_smul]

end averaging
section padic

variable {ℓ : ℕ} [Fact ℓ.Prime]

omit [IsTopologicalGroup G] in
/-- If an open set `U` contains the kernel of a continuous homomorphism `χ : G → ℤ_ℓ` on a
compact group, then it contains the inverse image of `ℓ ^ r ℤ_ℓ` for some `r`. -/
lemma exists_toZModPow_eq_zero_imp_mem (χ : G →ₜ* Multiplicative ℤ_[ℓ]) {U : Set G}
    (hU : IsOpen U) (hker : ∀ g, χ g = 1 → g ∈ U) :
    ∃ r : ℕ, ∀ g, PadicInt.toZModPow r (χ g).toAdd = 0 → g ∈ U := by
  by_contra! h
  let t : ℕ → Set G := fun r ↦ {g | PadicInt.toZModPow r (χ g).toAdd = 0} ∩ Uᶜ
  have hc (r : ℕ) : Continuous fun g ↦ PadicInt.toZModPow (p := ℓ) r (χ g).toAdd :=
    (PadicInt.continuous_toZModPow r).comp (continuous_toAdd.comp χ.continuous)
  have hcl (r : ℕ) : IsClosed (t r) :=
    ((isClosed_discrete {0}).preimage (hc r)).inter hU.isClosed_compl
  have hanti : Antitone t := by
    refine antitone_nat_of_succ_le fun r g hg ↦ ⟨?_, hg.2⟩
    have := hg.1
    simp only [Set.mem_ofPred_eq] at this ⊢
    rw [← PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r), this, ZMod.cast_zero]
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    hanti.directed_ge (fun r ↦ by obtain ⟨g, hg, hgU⟩ := h r; exact ⟨g, hg, hgU⟩)
    (fun r ↦ (hcl r).isCompact) hcl
  simp only [Set.mem_iInter] at hg
  refine (hg 0).2 (hker g ?_)
  have : (χ g).toAdd = 0 := PadicInt.ext_of_toZModPow.mp fun n ↦ by rw [(hg n).1, map_zero]
  rw [← ofAdd_toAdd (χ g), this, ofAdd_zero]

/-- The data of an `ℓ`-adic procyclic quotient of a compact group `G`: a continuous
homomorphism `χ : G → ℤ_ℓ` (written multiplicatively) and an element `τ` with `χ τ = 1`, such
that the finite quotients of the kernel `ker χ` have order prime to `ℓ`, i.e. the index
`[ker χ : ker χ ∩ U]` is prime to `ℓ` for every open subgroup `U` of `G`. -/
structure IsEllAdicQuotient (ℓ : ℕ) [Fact ℓ.Prime] (χ : G →ₜ* Multiplicative ℤ_[ℓ]) (τ : G) :
    Prop where
  map_τ : χ τ = Multiplicative.ofAdd 1
  not_dvd_relIndex : ∀ U : Subgroup G, IsOpen (U : Set G) → ¬ ℓ ∣ U.relIndex χ.toMonoidHom.ker

namespace IsEllAdicQuotient

variable {χ : G →ₜ* Multiplicative ℤ_[ℓ]} {τ : G} (hχ : IsEllAdicQuotient ℓ χ τ)
include hχ

omit [IsTopologicalGroup G] [CompactSpace G] in
lemma toAdd_map_pow (i : ℕ) : (χ (τ ^ i)).toAdd = i := by
  rw [map_pow, toAdd_pow, hχ.map_τ, toAdd_ofAdd, nsmul_one]

omit [IsTopologicalGroup G] in
/-- An open subgroup containing `ker χ` and `τ` is everything: `τ` generates a dense subgroup
of `G / ker χ ≃ ℤ_ℓ`. -/
lemma eq_top_of_le {U : Subgroup G} (hU : IsOpen (U : Set G)) (hK : χ.toMonoidHom.ker ≤ U)
    (hτ : τ ∈ U) : U = ⊤ := by
  obtain ⟨r, hr⟩ := exists_toZModPow_eq_zero_imp_mem χ hU fun g hg ↦ hK hg
  refine eq_top_iff.2 fun g _ ↦ ?_
  let m := (χ g).toAdd.appr r
  have hm : PadicInt.toZModPow r ((χ g).toAdd - (m : ℤ_[ℓ])) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact PadicInt.appr_spec r _
  have h1 : g * (τ ^ m)⁻¹ ∈ U := hr _ (by
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hχ.toAdd_map_pow, ← sub_eq_add_neg]
    exact hm)
  simpa using U.mul_mem h1 (U.pow_mem hτ m)

/-- **Summation along `τ`.** Let `f : G → A` be a smooth function invariant under right
translation by `ker χ`, with `ℓ`-primary values. Then `f = (τ - 1) h` for a smooth function `h`
invariant under right translation by `ker χ`: put `h x = ∑_{i < a(x)} f(τ ^ i)`, where `a(x)`
is the residue of `χ x` modulo `ℓ ^ N` for `N` large; the periodicity of `f(τ ^ i)` and the
`ℓ`-primary values make the full sum over a period vanish. -/
lemma exists_mul_sub_eq {A : Type*} [AddCommGroup A] (f : G → A)
    (hf : IsOpen (rightStab G f : Set G)) (hfK : χ.toMonoidHom.ker ≤ rightStab G f)
    (hA : ∀ x, ∃ j : ℕ, ℓ ^ j • f x = 0) :
    ∃ h : G → A, IsOpen (rightStab G h : Set G) ∧ χ.toMonoidHom.ker ≤ rightStab G h ∧
      ∀ x, h (x * τ) - h x = f x := by
  obtain ⟨r, hr⟩ := exists_toZModPow_eq_zero_imp_mem χ hf fun g hg ↦ hfK hg
  obtain ⟨s, hs⟩ := exists_pow_nsmul_eq_zero_of_finite ℓ
    (finite_range_of_forall_mul_eq f _ hf fun x u hu ↦ hu x) (by rintro _ ⟨x, rfl⟩; exact hA x)
  have hℓ := (Fact.out : ℓ.Prime).one_lt
  let N := r + (s + 1)
  have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow (by omega) hℓ⟩
  -- `f x` only depends on `χ x` modulo `ℓ ^ r`
  have key₀ (x y : G) (hxy : PadicInt.toZModPow r (χ x).toAdd = PadicInt.toZModPow r (χ y).toAdd) :
      f x = f y := by
    have : x⁻¹ * y ∈ rightStab G f := hr _ (by
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, map_add, map_neg, hxy, neg_add_cancel])
    simpa using (mem_rightStab.1 this x).symm
  let idx : G → ℕ := fun x ↦ (PadicInt.toZModPow N (χ x).toAdd).val
  let F : ℕ → A := fun i ↦ f (τ ^ i)
  have hcast (a : ℤ_[ℓ]) :
      (((PadicInt.toZModPow N a).val : ℕ) : ZMod (ℓ ^ r)) = PadicInt.toZModPow r a := by
    rw [ZMod.natCast_val, PadicInt.cast_toZModPow r N (by omega)]
  have key₁ (x : G) : f x = F (idx x) := key₀ _ _ (by rw [hχ.toAdd_map_pow, map_natCast, hcast])
  have key₂ (m i : ℕ) : F (ℓ ^ r * m + i) = F i := key₀ _ _ (by
    rw [hχ.toAdd_map_pow, hχ.toAdd_map_pow, map_natCast, map_natCast, Nat.cast_add,
      Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add])
  have hsum : ∑ i ∈ Finset.range (ℓ ^ N), F i = 0 := by
    rw [show ℓ ^ N = ℓ ^ r * ℓ ^ (s + 1) by rw [pow_add],
      Finset.sum_range_mul_of_periodic F _ key₂, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [pow_succ, mul_comm, mul_smul, hs _ ⟨_, rfl⟩, smul_zero]
  let V : Subgroup G := ((PadicInt.toZModPowContinuousMonoidHom N).comp χ).toMonoidHom.ker
  have hV (k : G) : k ∈ V ↔ PadicInt.toZModPow N (χ k).toAdd = 0 := by
    simp only [V, MonoidHom.mem_ker]
    exact ⟨fun h ↦ congrArg Multiplicative.toAdd h, fun h ↦ congrArg Multiplicative.ofAdd h⟩
  have hVo : IsOpen (V : Set G) :=
    (isOpen_discrete {1}).preimage ((PadicInt.toZModPowContinuousMonoidHom N).comp χ).continuous
  have hidx (x k : G) (hk : k ∈ V) : idx (x * k) = idx x := by
    simp only [idx, map_mul, toAdd_mul, map_add, (hV k).1 hk, add_zero]
  refine ⟨fun x ↦ ∑ i ∈ Finset.range (idx x), F i, ?_, ?_, fun x ↦ ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := V) (fun k hk x ↦ ?_) hVo
    simp only [hidx x k hk]
  · intro k hk x
    have hk' : k ∈ V := by
      rw [hV, show χ k = 1 from hk]
      simp
    simp only [hidx x k hk']
  · have hidxτ : idx (x * τ) = (idx x + 1) % ℓ ^ N := by
      simp only [idx, map_mul, toAdd_mul, hχ.map_τ, toAdd_ofAdd, map_add, map_one]
      rw [ZMod.val_add, ZMod.val_one]
    have hlt : idx x < ℓ ^ N := ZMod.val_lt _
    simp only
    rcases Nat.lt_or_ge (idx x + 1) (ℓ ^ N) with h | h
    · rw [hidxτ, Nat.mod_eq_of_lt h, Finset.sum_range_succ, add_sub_cancel_left, key₁ x]
    · have h' : idx x + 1 = ℓ ^ N := by omega
      rw [← h', Finset.sum_range_succ, ← key₁ x] at hsum
      rw [hidxτ, h', Nat.mod_self, Finset.sum_range_zero, zero_sub, neg_eq_iff_eq_neg]
      exact eq_neg_of_add_eq_zero_left hsum

omit [Fact ℓ.Prime] hχ in
/-- The coinduced module of an `ℓ`-primary module is `ℓ`-primary. -/
lemma _root_.DiscreteModule.isPrimary_coind₁ {X : DiscreteModule.{w} G} (hX : IsPrimary ℓ X) :
    IsPrimary ℓ ((coind₁ G).obj X.obj.V) := fun f ↦ by
  obtain ⟨J, hJ⟩ := exists_pow_nsmul_eq_zero_of_finite ℓ (finite_range_smoothFunctions f)
    (by rintro _ ⟨x, rfl⟩; exact hX _)
  exact ⟨J, Subtype.ext (funext fun x ↦ hJ _ ⟨x, rfl⟩)⟩


omit [IsTopologicalGroup G] [CompactSpace G] hχ in
lemma ρ_mul_conj_apply {X : DiscreteModule.{w} G} {y : X.obj.V}
    (hy : ∀ k ∈ χ.toMonoidHom.ker, (X.obj.ρ k).asHom.hom y = y) {k : G}
    (hk : k ∈ χ.toMonoidHom.ker) :
    (X.obj.ρ k).asHom.hom ((X.obj.ρ τ).asHom.hom y) = (X.obj.ρ τ).asHom.hom y := by
  have : τ⁻¹ * k * τ ∈ χ.toMonoidHom.ker := by
    simpa using (MonoidHom.normal_ker χ.toMonoidHom).conj_mem k hk τ⁻¹
  rw [← ρ_mul_apply, show k * τ = τ * (τ⁻¹ * k * τ) by group, ρ_mul_apply, hy _ this]

/-- **Vanishing of `H¹`.** If `τ - 1` is surjective on the `ker χ`-invariants of an `ℓ`-primary
discrete module `X`, then `H¹(G, X) = 0`. -/
lemma subsingleton_H_one (X : DiscreteModule.{w} G) (hX : IsPrimary ℓ X)
    (hsurj : ∀ x : X.obj.V, (∀ k ∈ χ.toMonoidHom.ker, (X.obj.ρ k).asHom.hom x = x) →
      ∃ y : X.obj.V, (∀ k ∈ χ.toMonoidHom.ker, (X.obj.ρ k).asHom.hom y = y) ∧
        (X.obj.ρ τ).asHom.hom y - y = x) :
    Subsingleton (H G X 1) := by
  change Subsingleton (Abelian.Ext (intTrivial G) (shortComplex₁ X).X₁ 1)
  rw [subsingleton_ext_one_iff (shortExact₁ X) (subsingleton_H_coind₁ _ 0),
    forall_exists_comp_eq_iff]
  intro z hz
  obtain ⟨f, hfK, rfl⟩ := exists_fixed_lift _ hχ.not_dvd_relIndex (coker₁π X)
    QuotientAddGroup.mk_surjective (isPrimary_coker₁ hX) z fun k _ ↦ hz k
  have hτf : (((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom f - f ∈ toCoind₁Range X := by
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    exact hz τ
  obtain ⟨x, hx⟩ := hτf
  have hxK : ∀ k ∈ χ.toMonoidHom.ker, (X.obj.ρ k).asHom.hom x = x := by
    intro k hk
    apply injective_toCoind₁ X
    rw [hom_comm_apply, hx, map_sub, hfK k hk, ρ_mul_conj_apply hfK hk]
  obtain ⟨y, hyK, hy⟩ := hsurj x hxK
  let f' : ((coind₁ G).obj X.obj.V).obj.V := f - (toCoind₁ X).hom.hom.hom y
  have hf'K : ∀ k ∈ χ.toMonoidHom.ker, (((coind₁ G).obj X.obj.V).obj.ρ k).asHom.hom f' = f' := by
    intro k hk
    simp only [f', map_sub, hfK k hk, ← hom_comm_apply, hyK k hk]
  have hf'τ : (((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom f' = f' := by
    have h1 : (((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom f = f + (toCoind₁ X).hom.hom.hom x := by
      rw [hx]; abel
    simp only [f', map_sub, h1, ← hom_comm_apply, ← hy, map_sub]
    abel
  have htop := hχ.eq_top_of_le (U := ((coind₁ G).obj X.obj.V).obj.stabilizer f')
    (((coind₁ G).obj X.obj.V).isOpen_stabilizer f') hf'K hf'τ
  refine ⟨f', fun g ↦ ?_, ?_⟩
  · have : g ∈ ((coind₁ G).obj X.obj.V).obj.stabilizer f' := htop ▸ Subgroup.mem_top g
    exact this
  · have h0 : (QuotientAddGroup.mk ((toCoind₁ X).hom.hom.hom y) : (coker₁ X).obj.V) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 ⟨y, rfl⟩
    simp only [shortComplex₁, coker₁π_apply, f', QuotientAddGroup.mk_sub, h0, sub_zero]

/-- `τ - 1` is surjective on the `ker χ`-invariants of `C^sm(G, X) / X` for `ℓ`-primary `X`. -/
lemma exists_coker₁_sub_eq (X : DiscreteModule.{w} G) (hX : IsPrimary ℓ X)
    (z : (coker₁ X).obj.V) (hz : ∀ k ∈ χ.toMonoidHom.ker, ((coker₁ X).obj.ρ k).asHom.hom z = z) :
    ∃ y : (coker₁ X).obj.V, (∀ k ∈ χ.toMonoidHom.ker, ((coker₁ X).obj.ρ k).asHom.hom y = y) ∧
      ((coker₁ X).obj.ρ τ).asHom.hom y - y = z := by
  obtain ⟨f, hfK, rfl⟩ := exists_fixed_lift _ hχ.not_dvd_relIndex (coker₁π X)
    QuotientAddGroup.mk_surjective (isPrimary_coker₁ hX) z hz
  have hfK' : χ.toMonoidHom.ker ≤ rightStab G f.1 := fun k hk x ↦
    congr_fun (congrArg Subtype.val (hfK k hk)) x
  obtain ⟨h, hho, hhK, hh⟩ := hχ.exists_mul_sub_eq f.1 f.2 hfK' fun x ↦ hX _
  let h' : ((coind₁ G).obj X.obj.V).obj.V := ⟨h, hho⟩
  refine ⟨QuotientAddGroup.mk h', fun k hk ↦ ?_, ?_⟩
  · rw [coker₁_ρ_mk]
    congr 1
    exact Subtype.ext (funext fun x ↦ hhK hk x)
  · rw [coker₁_ρ_mk, ← QuotientAddGroup.mk_sub, coker₁π_apply]
    congr 1
    exact Subtype.ext (funext fun x ↦ hh x)

/-- **Vanishing of `H²`.** `H²(G, X) = 0` for every `ℓ`-primary discrete module `X`. -/
lemma subsingleton_H_two (X : DiscreteModule.{w} G) (hX : IsPrimary ℓ X) :
    Subsingleton (H G X 2) :=
  subsingleton_ext_succ_of_shortExact (shortExact₁ X) (subsingleton_H_coind₁ _ 1)
    (hχ.subsingleton_H_one (coker₁ X) (isPrimary_coker₁ hX) (hχ.exists_coker₁_sub_eq X hX))

/-- **Cohomological dimension one.** `Hᵠ(G, X) = 0` for every `q ≥ 2` and every `ℓ`-primary
discrete module `X`. -/
theorem subsingleton_H (X : DiscreteModule.{w} G) (hX : IsPrimary ℓ X) {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (H G X q) := by
  induction q, hq using Nat.le_induction generalizing X with
  | base => exact hχ.subsingleton_H_two X hX
  | succ n hn ih =>
    exact subsingleton_ext_succ_of_shortExact (shortExact₁ X) (subsingleton_H_coind₁ _ n)
      (ih _ (isPrimary_coker₁ hX))

end IsEllAdicQuotient

section HOne

omit [IsTopologicalGroup G] [CompactSpace G] [Fact ℓ.Prime] in
/-- The elements of a discrete module fixed by a subgroup `K`. -/
def fixedAddSubgroup (X : DiscreteModule.{w} G) (K : Subgroup G) : AddSubgroup X.obj.V where
  carrier := {x | ∀ k ∈ K, (X.obj.ρ k).asHom.hom x = x}
  zero_mem' _ _ := map_zero _
  add_mem' hx hy k hk := by simp [hx k hk, hy k hk]
  neg_mem' hx k hk := by simp [hx k hk]

omit [IsTopologicalGroup G] [CompactSpace G] [Fact ℓ.Prime] in
@[simp]
lemma mem_fixedAddSubgroup {X : DiscreteModule.{w} G} {K : Subgroup G} {x : X.obj.V} :
    x ∈ fixedAddSubgroup X K ↔ ∀ k ∈ K, (X.obj.ρ k).asHom.hom x = x :=
  Iff.rfl

omit [IsTopologicalGroup G] [CompactSpace G] [Fact ℓ.Prime] in
lemma ofInjective_symm_apply {A B : Type*} [AddGroup A] [AddGroup B] {φ : A →+ B}
    (hφ : Function.Injective φ) (y : φ.range) : φ ((AddMonoidHom.ofInjective hφ).symm y) = y := by
  conv_rhs => rw [← (AddMonoidHom.ofInjective hφ).apply_symm_apply y]
  rfl

variable (χ : G →ₜ* Multiplicative ℤ_[ℓ]) (τ : G) (X : DiscreteModule.{w} G)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The endomorphism `τ - 1` of the `ker χ`-invariants of a discrete module. -/
noncomputable def tauSubOne :
    fixedAddSubgroup X χ.toMonoidHom.ker →+ fixedAddSubgroup X χ.toMonoidHom.ker :=
  (((X.obj.ρ τ).asHom.hom - AddMonoidHom.id _).comp (fixedAddSubgroup X _).subtype).codRestrict _
    fun x k hk ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
        AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub,
        IsEllAdicQuotient.ρ_mul_conj_apply x.2 hk, x.2 k hk]

omit [IsTopologicalGroup G] [CompactSpace G] in
@[simp]
lemma coe_tauSubOne_apply (x : fixedAddSubgroup X χ.toMonoidHom.ker) :
    (tauSubOne χ τ X x : X.obj.V) = (X.obj.ρ τ).asHom.hom x - x :=
  rfl

/-- The smooth functions `f : G → X`, invariant under `ker χ`, with `(τ - 1) f ∈ X`. -/
noncomputable def coindFixed : AddSubgroup ((coind₁ G).obj X.obj.V).obj.V :=
  fixedAddSubgroup _ χ.toMonoidHom.ker ⊓
    (toCoind₁Range X).comap ((((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom - AddMonoidHom.id _)

omit [CompactSpace G] in
lemma mem_coindFixed {f : ((coind₁ G).obj X.obj.V).obj.V} :
    f ∈ coindFixed χ τ X ↔
      (∀ k ∈ χ.toMonoidHom.ker, (((coind₁ G).obj X.obj.V).obj.ρ k).asHom.hom f = f) ∧
      (((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom f - f ∈ toCoind₁Range X :=
  Iff.rfl

/-- The map `f ↦ (τ - 1) f` from `coindFixed` to `Xᴷ`. -/
noncomputable def coindFixedToFixed :
    coindFixed χ τ X →+ fixedAddSubgroup X χ.toMonoidHom.ker where
  toFun f := ⟨(AddMonoidHom.ofInjective (injective_toCoind₁ X)).symm
      ⟨(((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom f - f, ((mem_coindFixed χ τ X).1 f.2).2⟩,
      fun k hk ↦ by
    apply injective_toCoind₁ X
    rw [hom_comm_apply, ofInjective_symm_apply]
    simp only [map_sub,
      ((mem_coindFixed χ τ X).1 f.2).1 k hk,
      IsEllAdicQuotient.ρ_mul_conj_apply ((mem_coindFixed χ τ X).1 f.2).1 hk]⟩
  map_zero' := Subtype.ext <| injective_toCoind₁ X <| by
    rw [ofInjective_symm_apply]
    change (((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom 0 - 0 = (toCoind₁ X).hom.hom.hom 0
    simp
  map_add' f f' := Subtype.ext <| injective_toCoind₁ X <| by
    simp only [AddSubgroup.coe_add, map_add, ofInjective_symm_apply]
    abel

omit [CompactSpace G] in
lemma toCoind₁_coindFixedToFixed (f : coindFixed χ τ X) :
    (toCoind₁ X).hom.hom.hom (coindFixedToFixed χ τ X f) =
      (((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom f - f :=
  ofInjective_symm_apply _ _

/-- The connecting map `(C^sm(G, X) / X)ᴳ → H¹(G, X)`. -/
noncomputable def HOneδ : (invariants G).obj (coker₁ X) →+ H G X 1 :=
  ((shortExact₁ X).extClass.postcomp (intTrivial G) (zero_add 1)).comp
    ((homIntTrivialEquiv (coker₁ X)).symm.trans Abelian.Ext.addEquiv₀.symm).toAddMonoidHom

omit [CompactSpace G] in
lemma HOneδ_apply (z : (invariants G).obj (coker₁ X)) :
    HOneδ X z = (Abelian.Ext.mk₀ ((homIntTrivialEquiv (coker₁ X)).symm z)).comp
      (shortExact₁ X).extClass (zero_add 1) :=
  rfl

omit [CompactSpace G] in
lemma surjective_HOneδ : Function.Surjective (HOneδ X) := by
  intro x
  have : Subsingleton (Abelian.Ext (intTrivial G) (shortComplex₁ X).X₂ 1) :=
    subsingleton_H_coind₁ (G := G) X.obj.V 0
  obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ (intTrivial G) (shortExact₁ X) x
    (Subsingleton.elim _ _) (zero_add 1)
  obtain ⟨φ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x₃
  refine ⟨homIntTrivialEquiv _ φ, ?_⟩
  rw [HOneδ_apply, AddEquiv.symm_apply_apply]
  exact hx₃

omit [CompactSpace G] in
lemma HOneδ_eq_zero_iff (z : (invariants G).obj (coker₁ X)) :
    HOneδ X z = 0 ↔ ∃ c : ((coind₁ G).obj X.obj.V).obj.V,
      (∀ g, (((coind₁ G).obj X.obj.V).obj.ρ g).asHom.hom c = c) ∧
        (QuotientAddGroup.mk c : (coker₁ X).obj.V) = z.1 := by
  constructor
  · intro hz
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ (intTrivial G) (shortExact₁ X)
      (Abelian.Ext.mk₀ ((homIntTrivialEquiv (coker₁ X)).symm z)) (zero_add 1) hz
    obtain ⟨ψ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x₂
    rw [Abelian.Ext.mk₀_comp_mk₀] at hx₂
    have hψ := (Abelian.Ext.mk₀_bijective _ _).1 hx₂
    refine ⟨(homIntTrivialEquiv _ ψ).1, (homIntTrivialEquiv _ ψ).2, ?_⟩
    have := congrArg (fun φ ↦ (homIntTrivialEquiv (coker₁ X) φ).1) hψ
    simp only [AddEquiv.apply_symm_apply] at this
    exact this
  · rintro ⟨c, hc, hcz⟩
    have : (homIntTrivialEquiv (coker₁ X)).symm z =
        (homIntTrivialEquiv _).symm ⟨c, hc⟩ ≫ (shortComplex₁ X).g := by
      apply (homIntTrivialEquiv (coker₁ X)).injective
      rw [AddEquiv.apply_symm_apply]
      refine Subtype.ext (hcz.symm.trans ?_)
      change _ = QuotientAddGroup.mk
        ((homIntTrivialEquiv _ ((homIntTrivialEquiv _).symm ⟨c, hc⟩)).1)
      rw [AddEquiv.apply_symm_apply]
    rw [HOneδ_apply, this, ← Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.comp_assoc_of_second_deg_zero, (shortExact₁ X).comp_extClass,
      Abelian.Ext.comp_zero]

end HOne

namespace IsEllAdicQuotient

variable {χ : G →ₜ* Multiplicative ℤ_[ℓ]} {τ : G} (hχ : IsEllAdicQuotient ℓ χ τ)
  (X : DiscreteModule.{w} G)
include hχ

omit [IsTopologicalGroup G] in
/-- An element fixed by `ker χ` and by `τ` is fixed by `G`. -/
lemma forall_ρ_eq {x : X.obj.V} (hxK : ∀ k ∈ χ.toMonoidHom.ker, (X.obj.ρ k).asHom.hom x = x)
    (hxτ : (X.obj.ρ τ).asHom.hom x = x) (g : G) : (X.obj.ρ g).asHom.hom x = x := by
  have := hχ.eq_top_of_le (U := X.obj.stabilizer x) (X.isOpen_stabilizer x) hxK hxτ
  exact (this ▸ Subgroup.mem_top g : g ∈ X.obj.stabilizer x)

/-- `H⁰(G, X)` is the kernel of `τ - 1` on the `ker χ`-invariants. -/
noncomputable def HZeroAddEquiv : H G X 0 ≃+ (tauSubOne χ τ X).ker :=
  (H_zero_addEquiv X).trans
    { toFun x := ⟨⟨x.1, fun k _ ↦ x.2 k⟩, Subtype.ext (by
        rw [coe_tauSubOne_apply]
        exact sub_eq_zero.2 (x.2 τ))⟩
      invFun x := ⟨x.1.1, hχ.forall_ρ_eq X x.1.2 (by
        have h := congrArg Subtype.val (AddMonoidHom.mem_ker.1 x.2)
        rw [coe_tauSubOne_apply, ZeroMemClass.coe_zero, sub_eq_zero] at h
        exact h)⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }

/-- The projection of `coindFixed` to the invariants of `C^sm(G, X) / X`. -/
noncomputable def coindFixedToInvariants :
    coindFixed χ τ X →+ (invariants G).obj (coker₁ X) :=
  ((QuotientAddGroup.mk' (toCoind₁Range X)).comp (coindFixed χ τ X).subtype).codRestrict _
    fun f ↦ hχ.forall_ρ_eq (coker₁ X) (fun k hk ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
        QuotientAddGroup.mk'_apply]
      rw [coker₁_ρ_mk, ((mem_coindFixed χ τ X).1 f.2).1 k hk]) (by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
        QuotientAddGroup.mk'_apply]
      rw [coker₁_ρ_mk, QuotientAddGroup.eq_iff_sub_mem]
      exact ((mem_coindFixed χ τ X).1 f.2).2)

lemma coe_coindFixedToInvariants_apply (f : coindFixed χ τ X) :
    (hχ.coindFixedToInvariants X f).1 = (QuotientAddGroup.mk f.1 : (coker₁ X).obj.V) :=
  rfl

variable {X}

lemma surjective_coindFixedToInvariants (hX : IsPrimary ℓ X) :
    Function.Surjective (hχ.coindFixedToInvariants X) := by
  intro z
  obtain ⟨f, hfK, hf⟩ := exists_fixed_lift _ hχ.not_dvd_relIndex (coker₁π X)
    QuotientAddGroup.mk_surjective (isPrimary_coker₁ hX) z.1 fun k _ ↦ z.2 k
  have hτ : (((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom f - f ∈ toCoind₁Range X := by
    rw [← QuotientAddGroup.eq_iff_sub_mem, ← coker₁_ρ_mk]
    simp only [coker₁π_apply] at hf
    rw [hf]
    exact z.2 τ
  exact ⟨⟨f, hfK, hτ⟩, Subtype.ext hf⟩

lemma surjective_coindFixedToFixed (hX : IsPrimary ℓ X) :
    Function.Surjective (coindFixedToFixed χ τ X) := by
  intro x
  let F := (toCoind₁ X).hom.hom.hom x
  obtain ⟨h, hho, hhK, hh⟩ := hχ.exists_mul_sub_eq F.1 F.2
    (fun k hk y ↦ by simp [F, x.2 k hk]) fun y ↦ hX _
  let h' : ((coind₁ G).obj X.obj.V).obj.V := ⟨h, hho⟩
  have hτ : (((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom h' - h' = F :=
    Subtype.ext (funext fun y ↦ hh y)
  have hmem : h' ∈ coindFixed χ τ X :=
    ⟨fun k hk ↦ Subtype.ext (funext fun y ↦ hhK hk y),
      show (((coind₁ G).obj X.obj.V).obj.ρ τ).asHom.hom h' - h' ∈ toCoind₁Range X by
        rw [hτ]; exact ⟨x, rfl⟩⟩
  refine ⟨⟨h', hmem⟩, Subtype.ext (injective_toCoind₁ X ?_)⟩
  rw [toCoind₁_coindFixedToFixed]
  exact hτ

lemma HOneδ_coindFixedToInvariants_eq_zero_iff (f : coindFixed χ τ X) :
    HOneδ X (hχ.coindFixedToInvariants X f) = 0 ↔
      coindFixedToFixed χ τ X f ∈ (tauSubOne χ τ X).range := by
  have hf := (mem_coindFixed χ τ X).1 f.2
  rw [HOneδ_eq_zero_iff, coe_coindFixedToInvariants_apply]
  constructor
  · rintro ⟨c, hc, hcf⟩
    rw [eq_comm, QuotientAddGroup.eq_iff_sub_mem] at hcf
    obtain ⟨x', hx'⟩ := hcf
    have hx'K : x' ∈ fixedAddSubgroup X χ.toMonoidHom.ker := fun k hk ↦
      injective_toCoind₁ X (by rw [hom_comm_apply, hx', map_sub, hf.1 k hk, hc k])
    refine ⟨⟨x', hx'K⟩, Subtype.ext (injective_toCoind₁ X ?_)⟩
    rw [toCoind₁_coindFixedToFixed, coe_tauSubOne_apply, map_sub, hom_comm_apply, hx',
      map_sub, hc τ]
    abel
  · rintro ⟨x', hx'⟩
    have h1 := toCoind₁_coindFixedToFixed χ τ X f
    rw [← hx', coe_tauSubOne_apply, map_sub, hom_comm_apply] at h1
    refine ⟨f.1 - (toCoind₁ X).hom.hom.hom x', fun g ↦ ?_, ?_⟩
    · refine hχ.forall_ρ_eq _ (fun k hk ↦ ?_) ?_ g
      · rw [map_sub, hf.1 k hk, ← hom_comm_apply, x'.2 k hk]
      · rw [map_sub, ← hom_comm_apply, hom_comm_apply]
        rw [eq_sub_iff_add_eq] at h1
        rw [← h1]
        abel
    · have h0 : (QuotientAddGroup.mk ((toCoind₁ X).hom.hom.hom x') : (coker₁ X).obj.V) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).2 ⟨x', rfl⟩
      rw [QuotientAddGroup.mk_sub, h0, sub_zero]

/-- **Computation of `H¹`.** For an `ℓ`-primary discrete module `X`,
`H¹(G, X) ≃ Xᴷ / (τ - 1) Xᴷ` with `K = ker χ`. -/
noncomputable def HOneAddEquiv (hX : IsPrimary ℓ X) :
    H G X 1 ≃+ fixedAddSubgroup X χ.toMonoidHom.ker ⧸ (tauSubOne χ τ X).range :=
  (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_HOneδ X)).symm.trans <|
  (QuotientAddGroup.quotientKerEquivOfSurjective
    ((QuotientAddGroup.mk' (HOneδ X).ker).comp (hχ.coindFixedToInvariants X))
    ((QuotientAddGroup.mk'_surjective _).comp
      (hχ.surjective_coindFixedToInvariants hX))).symm.trans <|
  (QuotientAddGroup.quotientAddEquivOfEq (by
    ext f
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
      QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact hχ.HOneδ_coindFixedToInvariants_eq_zero_iff f)).trans <|
  QuotientAddGroup.quotientKerEquivOfSurjective
    ((QuotientAddGroup.mk' _).comp (coindFixedToFixed χ τ X))
    ((QuotientAddGroup.mk'_surjective _).comp (hχ.surjective_coindFixedToFixed hX))

end IsEllAdicQuotient

section padicInt

variable (ℓ)

lemma isEllAdicQuotient_id :
    IsEllAdicQuotient ℓ (ContinuousMonoidHom.id (Multiplicative ℤ_[ℓ])) (.ofAdd 1) where
  map_τ := rfl
  not_dvd_relIndex U _ := by
    have : (ContinuousMonoidHom.id (Multiplicative ℤ_[ℓ])).toMonoidHom.ker = ⊥ := by
      ext k
      simp [MonoidHom.mem_ker]
    rw [this, Subgroup.relIndex_bot_right]
    exact (Fact.out : ℓ.Prime).not_dvd_one

variable {ℓ} (M : DiscreteModule.{w} (Multiplicative ℤ_[ℓ]))

/-- The endomorphism `τ - 1` of a discrete `ℤ_ℓ`-module, `τ = 1` the topological generator. -/
noncomputable abbrev padicIntTauSubOne : M.obj.V →+ M.obj.V :=
  (M.obj.ρ (.ofAdd 1)).asHom.hom - AddMonoidHom.id _

/-- Blueprint `lem-exc-procyclic-two-term`: A two-term computation for a procyclic group,
vanishing part.

Let `M` be an `ℓ`-primary (e.g. killed by `ℓ ^ s`) discrete continuous module over
`G = ℤ_ℓ` (written multiplicatively), with topological generator `τ = 1`. Its continuous
cohomology is computed by the two-term complex `[M --τ-1--> M]` in degrees `0, 1`:
`H⁰(G, M) = ker(τ - 1)` (`DiscreteModule.HZeroPadicIntAddEquiv`),
`H¹(G, M) ≃ coker(τ - 1)` (`DiscreteModule.HOnePadicIntAddEquiv`), and `Hᵠ(G, M) = 0` for
`q ≥ 2` (this statement). This is the case `χ = id` of
`DiscreteModule.IsEllAdicQuotient.subsingleton_H`. -/
theorem subsingleton_H_padicInt (hM : IsPrimary ℓ M) {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (H (Multiplicative ℤ_[ℓ]) M q) :=
  (isEllAdicQuotient_id ℓ).subsingleton_H M hM hq


lemma mem_ker_id_iff {k : Multiplicative ℤ_[ℓ]} :
    k ∈ (ContinuousMonoidHom.id (Multiplicative ℤ_[ℓ])).toMonoidHom.ker ↔ k = 1 := by
  simp [MonoidHom.mem_ker]

/-- Blueprint `lem-exc-procyclic-two-term`: A two-term computation for a procyclic group,
degree zero: `H⁰(ℤ_ℓ, M) = ker(τ - 1)`. -/
noncomputable def HZeroPadicIntAddEquiv :
    H (Multiplicative ℤ_[ℓ]) M 0 ≃+ (padicIntTauSubOne M).ker :=
  (H_zero_addEquiv M).trans
    { toFun x := ⟨x.1, by simp [x.2 (.ofAdd 1)]⟩
      invFun x := ⟨x.1, (isEllAdicQuotient_id ℓ).forall_ρ_eq M
        (fun k hk ↦ by rw [mem_ker_id_iff.1 hk, ρ_one_apply])
        (sub_eq_zero.1 (AddMonoidHom.mem_ker.1 x.2))⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }

/-- The `ker id`-invariants of a discrete `ℤ_ℓ`-module are everything. -/
noncomputable def fixedAddSubgroupIdAddEquiv :
    fixedAddSubgroup M (ContinuousMonoidHom.id (Multiplicative ℤ_[ℓ])).toMonoidHom.ker ≃+
      M.obj.V where
  toFun x := x.1
  invFun x := ⟨x, fun k hk ↦ by rw [mem_ker_id_iff.1 hk, ρ_one_apply]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Blueprint `lem-exc-procyclic-two-term`: A two-term computation for a procyclic group,
degree one: `H¹(ℤ_ℓ, M) ≃ M / (τ - 1) M` for `ℓ`-primary `M`. -/
noncomputable def HOnePadicIntAddEquiv (hM : IsPrimary ℓ M) :
    H (Multiplicative ℤ_[ℓ]) M 1 ≃+ M.obj.V ⧸ (padicIntTauSubOne M).range :=
  ((isEllAdicQuotient_id ℓ).HOneAddEquiv hM).trans <|
    QuotientAddGroup.congr _ _ (fixedAddSubgroupIdAddEquiv M) (by
      ext y
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x.1, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨_, ⟨(fixedAddSubgroupIdAddEquiv M).symm x, rfl⟩, rfl⟩)

end padicInt

end padic

end DiscreteModule
