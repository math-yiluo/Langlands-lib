/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGalois
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTameSylow
public import WeilConjectures.Mathlib.FieldTheory.Galois.Profinite
public import WeilConjectures.Mathlib.FieldTheory.PurelyInseparable.Basic

/-!

# The pro-`p` kernel `P'` is divisible by integers prime to `p`

Let `F = k'((t))`, `F_K = K((t))` with `K` algebraically closed, `Ω_K = F_K^alg`,
`L' = F_K·F^sep ⊆ Ω_K` (`AlgebraicGeometry.traitGenericSepCompositum`) and `L'^sep ⊆ Ω_K` the
separable closure of `L'` in `Ω_K`.

The group `P'` of generic automorphisms (`NearbyCyclesModel.GenericAut`), the automorphisms of
`Ω_K` over `F_K` fixing the image of `Ω = F^alg`, is the absolute Galois group of `L'`
(`NearbyCyclesModel.GenericAut.mulEquivGal`):

* `P'` is the automorphism group of `Ω_K / L'`
  (`NearbyCyclesModel.GenericAut.mulEquivAlgEquiv`): an automorphism of `Ω_K` over `L'` fixes
  `Ω`, which is purely inseparable over `F^sep`;
* restriction `Aut(Ω_K / L') → Gal(L'^sep / L')` is bijective, as `Ω_K / L'^sep` is purely
  inseparable (`separableClosure.autMulEquiv`).

Every finite Galois extension of `L'` has `p`-power degree
(`AlgebraicGeometry.isPGroup_traitGenericSepCompositum_of_dvd`), so every element of `P'` is an
`n`-th power for `n` invertible in `k'` (`NearbyCyclesModel.GenericAut.exists_pow_eq`). This is
the divisibility of `P'` by powers of `ℓ ≠ p` used for the finiteness of its action on
`ℚ̄_ℓ`-nearby cycles (SGA 4½, [Th. finitude], §3.7;
`NearbyCyclesModel.autAction_baseChangeAut_eq_id_of_distinguished_of_separated`).

-/

@[expose] public section

universe u

open IntermediateField

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- `Ω_K` is normal over `L' = F_K·F^sep`. -/
instance : Normal (traitGenericSepCompositum k' K) (traitGenericField K) :=
  Normal.tower_top_of_normal (FractionRing (PowerSeries K)) _ _

/-- **The finite Galois extensions of `L'` have degree prime to `n`**, for `n` invertible in
`k'`: their degree is a power of the characteristic of `k'`, and is `1` in characteristic `0`. -/
theorem coprime_finrank_traitGenericSepCompositum [IsAlgClosed K] {n : ℕ} (hn : (n : k') ≠ 0)
    (M : IntermediateField (traitGenericSepCompositum k' K) (traitGenericField K))
    [FiniteDimensional (traitGenericSepCompositum k' K) M]
    [IsGalois (traitGenericSepCompositum k' K) M] :
    (Module.finrank (traitGenericSepCompositum k' K) M).Coprime n := by
  -- a prime `p` with `p ∤ n` such that `M` has `p`-power degree: the characteristic of `k'` if it
  -- is positive, and any prime `p > n` in characteristic `0`
  obtain ⟨p, hp, hpk, hpn⟩ : ∃ p : ℕ, p.Prime ∧ (∀ m : ℕ, (m : k') = 0 → p ∣ m) ∧ ¬ p ∣ n := by
    rcases CharP.char_is_prime_or_zero k' (ringChar k') with h | h
    · exact ⟨ringChar k', h, fun m hm ↦ (ringChar.spec k' m).1 hm,
        fun hd ↦ hn ((ringChar.spec k' n).2 hd)⟩
    · have hn₀ : n ≠ 0 := by
        rintro rfl
        exact hn Nat.cast_zero
      obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
      refine ⟨p, hp, fun m hm ↦ ?_, fun hd ↦ ?_⟩
      · have hm₀ := (ringChar.spec k' m).1 hm
        rw [h, zero_dvd_iff] at hm₀
        exact hm₀ ▸ dvd_zero p
      · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn₀) hd
        omega
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_traitGenericSepCompositum_of_dvd hp hpk M)
  rw [← IsGalois.card_aut_eq_finrank, hk]
  exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- Generic automorphisms fix `L' = F_K·F^sep`. -/
lemma toAlgEquiv_apply_of_mem_traitGenericSepCompositum (σ : GenericAut k' K)
    {x : traitGenericField K} (hx : x ∈ traitGenericSepCompositum k' K) :
    toAlgEquiv σ x = x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨y, -, rfl⟩ := hx
    exact toRingAut_traitGenericFieldMap σ y
  | algebraMap x => exact (toAlgEquiv σ).commutes x
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

/-- Automorphisms of `Ω_K` over `L' = F_K·F^sep` fix the image of `Ω`: the two embeddings
`Ω → Ω_K` agree on `F^sep`, over which `Ω` is purely inseparable. -/
lemma algEquiv_traitGenericFieldMap
    (e : traitGenericField K ≃ₐ[traitGenericSepCompositum k' K] traitGenericField K)
    (y : traitGenericField k') : e (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y := by
  let S := separableClosure (FractionRing (PowerSeries k')) (traitGenericField k')
  have h : ((e : traitGenericField K →+* traitGenericField K).comp
      (traitGenericFieldMap k' K)).comp (algebraMap S (traitGenericField k')) =
      (traitGenericFieldMap k' K).comp (algebraMap S (traitGenericField k')) := by
    ext s
    exact e.commutes ⟨_, subset_adjoin _ _ ⟨s, s.2, rfl⟩⟩
  exact RingHom.congr_fun
    (IsPurelyInseparable.injective_comp_algebraMap S (traitGenericField k') _ h) y

/-- A generic automorphism as an automorphism of `Ω_K` over `L' = F_K·F^sep`. -/
noncomputable def toAlgEquivTraitGenericSepCompositum (σ : GenericAut k' K) :
    traitGenericField K ≃ₐ[traitGenericSepCompositum k' K] traitGenericField K where
  toRingEquiv := (toAlgEquiv σ).toRingEquiv
  commutes' x := toAlgEquiv_apply_of_mem_traitGenericSepCompositum σ x.2

@[simp]
lemma toAlgEquivTraitGenericSepCompositum_apply (σ : GenericAut k' K)
    (x : traitGenericField K) : toAlgEquivTraitGenericSepCompositum σ x = toAlgEquiv σ x :=
  rfl

/-- **`P'` is the automorphism group of `Ω_K` over `L' = F_K·F^sep`.** -/
noncomputable def mulEquivAlgEquiv : GenericAut k' K ≃*
    (traitGenericField K ≃ₐ[traitGenericSepCompositum k' K] traitGenericField K) where
  toFun := toAlgEquivTraitGenericSepCompositum
  invFun e := ofAlgEquiv (e.restrictScalars (FractionRing (PowerSeries K)))
    (algEquiv_traitGenericFieldMap e)
  left_inv σ := toAlgEquiv_injective <| AlgEquiv.ext fun x ↦ by
    rw [toAlgEquiv_ofAlgEquiv, AlgEquiv.restrictScalars_apply,
      toAlgEquivTraitGenericSepCompositum_apply]
  right_inv e := AlgEquiv.ext fun x ↦ by
    rw [toAlgEquivTraitGenericSepCompositum_apply, toAlgEquiv_ofAlgEquiv,
      AlgEquiv.restrictScalars_apply]
  map_mul' σ τ := AlgEquiv.ext fun x ↦ by
    rw [AlgEquiv.mul_apply, toAlgEquivTraitGenericSepCompositum_apply,
      toAlgEquivTraitGenericSepCompositum_apply, toAlgEquivTraitGenericSepCompositum_apply,
      map_mul, AlgEquiv.mul_apply]

/-- **`P'` is the absolute Galois group of `L' = F_K·F^sep`**: restriction to the separable
closure `L'^sep` of `L'` in `Ω_K` identifies `P'` with `Gal(L'^sep / L')`. -/
noncomputable def mulEquivGal : GenericAut k' K ≃*
    Gal(separableClosure (traitGenericSepCompositum k' K) (traitGenericField K) /
      traitGenericSepCompositum k' K) :=
  mulEquivAlgEquiv.trans (separableClosure.autMulEquiv _ _)

variable [IsAlgClosed K]

/-- **The pro-`p` kernel `P'` is divisible by integers prime to `p`**: every generic
automorphism is an `n`-th power for `n` invertible in `k'`. -/
theorem exists_pow_eq {n : ℕ} (hn : (n : k') ≠ 0) (σ : GenericAut k' K) : ∃ τ, τ ^ n = σ := by
  obtain ⟨τ, hτ⟩ := IsGalois.exists_pow_eq_separableClosure (F := traitGenericSepCompositum k' K)
    (E := traitGenericField K) (fun M _ _ ↦ coprime_finrank_traitGenericSepCompositum hn M)
    (mulEquivGal σ)
  exact ⟨mulEquivGal.symm τ, by rw [← map_pow, hτ, MulEquiv.symm_apply_apply]⟩

/-- Every generic automorphism is an `ℓ ^ m`-th power, for `ℓ` invertible in `k'`. -/
theorem exists_pow_ell_pow_eq {ℓ : ℕ} (hℓ : (ℓ : k') ≠ 0) (m : ℕ) (σ : GenericAut k' K) :
    ∃ τ, τ ^ ℓ ^ m = σ :=
  exists_pow_eq (by simpa using pow_ne_zero m hℓ) σ

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut
