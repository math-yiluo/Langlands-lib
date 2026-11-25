/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-!
# Generic freeness and the rank at the generic point

We record two facts about the rank `Module.rankAtStalk` of a module at a prime.

## Main statements

- `Module.rankAtStalk_comap_ringEquiv`: the rank at a prime is invariant under a ring isomorphism
  together with a compatible additive isomorphism of modules.
- `Module.Finite.exists_free_localizedModule_powers_of_isDomain`: *generic freeness*. A finite
  module `M` over a domain `A` becomes free after inverting a suitable nonzero `r ∈ A`, of rank the
  rank of `M` at the generic point `(0)` of `Spec A`.
- `Module.exists_free_localizedModule_powers_of_flat`: a finitely presented flat module becomes
  free of finite rank after inverting a suitable element outside any given prime.
- `Module.exists_flat_localizedModule_powers`: *generic flatness* (Stacks, Tag 051R). A finite
  module over a finite type algebra over a noetherian domain `R` becomes flat over `R` after
  inverting a suitable nonzero element of `R`.
-/

@[expose] public section

namespace Module

/-- **The rank at a prime is invariant under ring isomorphisms.** Let `i : R ≃+* R'` and let
`j : M ≃+ M'` be an additive isomorphism from an `R`-module to an `R'`-module with
`j (r • m) = i r • j m`. Then the rank of `M` at the prime `i⁻¹ p` is the rank of `M'` at `p`. -/
theorem rankAtStalk_comap_ringEquiv {R R' M M' : Type*} [CommRing R] [CommRing R']
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (i : R ≃+* R') (j : M ≃+ M')
    (hj : ∀ (r : R) (m : M), j (r • m) = i r • j m) (p : PrimeSpectrum R') :
    rankAtStalk M (p.comap (i : R →+* R')) = rankAtStalk M' p := by
  set q := p.comap (i : R →+* R')
  have hS : q.asIdeal.primeCompl.map i.toMonoidHom = p.asIdeal.primeCompl := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨i.symm x, show i (i.symm x) ∉ p.asIdeal by simpa using hx, by simp⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact hy
  have hmem (s : q.asIdeal.primeCompl) : i s ∈ p.asIdeal.primeCompl := s.2
  have hmem' (s : p.asIdeal.primeCompl) : i.symm s ∈ q.asIdeal.primeCompl := by
    change i (i.symm s) ∉ p.asIdeal
    rw [RingEquiv.apply_symm_apply]
    exact s.2
  let e := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime p.asIdeal) i hS
  let F : LocalizedModule q.asIdeal.primeCompl M → LocalizedModule p.asIdeal.primeCompl M' :=
    fun x ↦ x.liftOn (fun ms ↦ LocalizedModule.mk (j ms.1) ⟨i ms.2, hmem ms.2⟩) (by
      rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨i u, hmem u⟩, ?_⟩
      simp only [Submonoid.smul_def] at hu ⊢
      rw [← hj, ← hj, ← hj, ← hj, hu])
  let G : LocalizedModule p.asIdeal.primeCompl M' → LocalizedModule q.asIdeal.primeCompl M :=
    fun x ↦ x.liftOn (fun ms ↦ LocalizedModule.mk (j.symm ms.1) ⟨i.symm ms.2, hmem' ms.2⟩) (by
      rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨i.symm u, hmem' u⟩, ?_⟩
      simp only [Submonoid.smul_def] at hu ⊢
      apply j.injective
      simp only [hj, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hu])
  have hF (m : M) (s) : F (LocalizedModule.mk m s) = LocalizedModule.mk (j m) ⟨i s, hmem s⟩ :=
    rfl
  have hG (m : M') (s) : G (LocalizedModule.mk m s) =
      LocalizedModule.mk (j.symm m) ⟨i.symm s, hmem' s⟩ :=
    rfl
  let J : LocalizedModule q.asIdeal.primeCompl M ≃+ LocalizedModule p.asIdeal.primeCompl M' :=
    { toFun := F
      invFun := G
      left_inv x := by
        induction x using LocalizedModule.induction_on with
        | h m s => simp [hF, hG]
      right_inv x := by
        induction x using LocalizedModule.induction_on with
        | h m s => simp [hF, hG]
      map_add' x y := by
        induction x using LocalizedModule.induction_on with
        | h m s =>
        induction y using LocalizedModule.induction_on with
        | h m' s' =>
          rw [LocalizedModule.mk_add_mk, hF, hF, hF, LocalizedModule.mk_add_mk]
          congr 1
          · simp [map_add, Submonoid.smul_def, hj]
          · ext
            simp }
  have hJ (x) : J x = F x := rfl
  have he (r : R) (t) : e (Localization.mk r t) = Localization.mk (i r) ⟨i t, hmem t⟩ := by
    simp [e, IsLocalization.ringEquivOfRingEquiv_apply, Localization.mk_eq_mk',
      IsLocalization.map_mk']
  have := _root_.lift_rank_eq_of_equiv_equiv e J e.bijective fun r x ↦ by
    induction r using Localization.induction_on with
    | H rs =>
    induction x using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨r, t⟩ := rs
      rw [LocalizedModule.mk_smul_mk, he]
      rw [hJ, hJ, hF, hF, LocalizedModule.mk_smul_mk, hj]
      congr 1
      ext
      simp
  simpa [rankAtStalk, Module.finrank] using congr_arg Cardinal.toNat this

section IsDomain

variable {A M : Type*} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]

/-- **Generic freeness.** Let `M` be a finite module over a domain `A`. Then there is a nonzero
`r ∈ A` such that `M_r` is a free `A_r`-module, of rank the rank of `M` at the generic point `(0)`.
A basis of `M ⊗ Frac(A)` chosen inside `M` gives an injective map `l : A^d → M` whose cokernel is
torsion, hence killed by some nonzero `r` since it is finitely generated; then `l` becomes an
isomorphism after inverting `r`. -/
theorem Finite.exists_free_localizedModule_powers_of_isDomain [Module.Finite A M] :
    ∃ r : A, r ≠ 0 ∧ Module.Free (Localization (.powers r)) (LocalizedModule.Away r M) ∧
      Module.finrank (Localization (.powers r)) (LocalizedModule.Away r M) =
        Module.rankAtStalk (R := A) M ⟨⊥, Ideal.isPrime_bot⟩ := by
  classical
  let K := FractionRing A
  let f := LocalizedModule.mkLinearMap (nonZeroDivisors A) M
  have : Module.Finite K (LocalizedModule (nonZeroDivisors A) M) :=
    Module.Finite.of_isLocalizedModule (nonZeroDivisors A) (Rₚ := K) f
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range f)
  have : Finite b := hli.finite
  have hm (i : b) : ∃ x, f x = i := hb i.2
  choose m hm using hm
  let l := Finsupp.linearCombination A m
  have hl : Function.Injective l := by
    refine LinearIndependent.of_comp f ?_
    have : f ∘ m = ((↑) : b → _) := funext hm
    rw [this]
    exact hli.restrict_scalars' A
  -- every element of `M` has a nonzero multiple in the range of `l`
  have hrange (x : M) : ∃ s ∈ nonZeroDivisors A, s • x ∈ LinearMap.range l := by
    have hx : f x ∈ (Submodule.span A (Set.range m)).localized' K (nonZeroDivisors A) f := by
      rw [Submodule.localized'_span, ← Set.range_comp]
      have : f ∘ m = ((↑) : b → _) := funext hm
      rw [this, Subtype.range_coe, hspan]
      exact Submodule.subset_span ⟨x, rfl⟩
    obtain ⟨y, hy, s, hys⟩ := (Submodule.mem_localized' _ _ _ _ _).mp hx
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hys
    obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors A) hys
    refine ⟨u * s, mul_mem u.2 s.2, ?_⟩
    rw [Finsupp.range_linearCombination, mul_smul, ← Submonoid.smul_def, ← hu]
    exact Submodule.smul_of_tower_mem _ _ hy
  -- a single nonzero `r` with `r • M ⊆ range l`
  choose s hs hsl using hrange
  obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := A) (M := M)
  let r := ∏ x ∈ σ, s x
  have hr : r ∈ nonZeroDivisors A := prod_mem fun x _ ↦ hs x
  have hrl (x : M) : r • x ∈ LinearMap.range l := by
    have : (σ : Set M) ⊆ (LinearMap.range l).comap (r • LinearMap.id) := by
      intro x hx
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_coe,
        id_eq, r, ← Finset.prod_erase_mul σ s hx, mul_smul]
      exact Submodule.smul_mem _ _ (hsl x)
    have := Submodule.span_le.mpr this
    rw [hσ] at this
    exact this trivial
  have key (T : Submonoid A) (hrT : r ∈ T) (hT : T ≤ nonZeroDivisors A) :
      Module.Free (Localization T) (LocalizedModule T M) ∧
        Module.finrank (Localization T) (LocalizedModule T M) = Nat.card b := by
    have : IsDomain (Localization T) := IsLocalization.isDomain_localization hT
    have hbij : Function.Bijective (LocalizedModule.map T l) := by
      refine ⟨LocalizedModule.map_injective T l hl, fun y ↦ ?_⟩
      induction y using LocalizedModule.induction_on with
      | h x t =>
        obtain ⟨z, hz⟩ := hrl x
        refine ⟨LocalizedModule.mk z (⟨r, hrT⟩ * t), ?_⟩
        rw [LocalizedModule.map_mk, hz, LocalizedModule.mk_eq]
        exact ⟨1, by simp [mul_smul, Submonoid.smul_def, smul_comm (t : A) r x]⟩
    let B := (Finsupp.basisSingleOne.ofIsLocalizedModule (Localization T) T
      (LocalizedModule.mkLinearMap T (b →₀ A))).map (LinearEquiv.ofBijective _ hbij)
    exact ⟨.of_basis B, Module.finrank_eq_nat_card_basis B⟩
  refine ⟨r, nonZeroDivisors.ne_zero hr, (key _ (Submonoid.mem_powers r) ?_).1, ?_⟩
  · exact (powers_le_nonZeroDivisors_of_noZeroDivisors (nonZeroDivisors.ne_zero hr))
  · rw [(key _ (Submonoid.mem_powers r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (nonZeroDivisors.ne_zero hr))).2,
      Module.rankAtStalk, (key (Ideal.primeCompl ⊥) (nonZeroDivisors.ne_zero hr)
        fun x hx ↦ mem_nonZeroDivisors_of_ne_zero hx).2]

end IsDomain

section GenericFlatness

open TensorProduct

variable {R : Type*} [CommRing R]

/-- `M` is flat after inverting `a`, phrased through the kernels of the maps `M ⊗ J → M`: every
element of such a kernel is killed by a power of `a`. See `Module.flatAway_iff`. -/
def FlatAway (a : R) (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (J : Ideal R) (x : M ⊗[R] J), J.subtype.lTensor M x = 0 → ∃ n : ℕ, a ^ n • x = 0

variable {M : Type*} [AddCommGroup M] [Module R M]

lemma flatAway_iff (a : R) :
    FlatAway a M ↔ Flat R (LocalizedModule (Submonoid.powers a) M) := by
  set L := LocalizedModule (Submonoid.powers a) M
  set ℓ := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  have hloc (J : Ideal R) : IsLocalizedModule (Submonoid.powers a) (ℓ.rTensor J) :=
    IsLocalizedModule.rTensor (A := R) (Submonoid.powers a) ℓ
  have hlocR : IsLocalizedModule (Submonoid.powers a) (ℓ.rTensor R) :=
    IsLocalizedModule.rTensor (A := R) (Submonoid.powers a) ℓ
  have hsq (J : Ideal R) : (J.subtype.lTensor L) ∘ₗ (ℓ.rTensor J) =
      (ℓ.rTensor R) ∘ₗ (J.subtype.lTensor M) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  constructor
  · intro h
    rw [Flat.iff_lTensor_injective']
    intro J
    have := hloc J
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨⟨x, c⟩, hc⟩ := IsLocalizedModule.surj (Submonoid.powers a) (ℓ.rTensor J) w
    simp only at hc
    have h1 : (ℓ.rTensor R) (J.subtype.lTensor M x) = 0 := by
      rw [← LinearMap.comp_apply, ← hsq, LinearMap.comp_apply, ← hc, Submonoid.smul_def,
        map_smul, hw, smul_zero]
    obtain ⟨c', hc'⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a)
      (f := ℓ.rTensor R)).mp h1
    rw [Submonoid.smul_def, ← map_smul] at hc'
    obtain ⟨n, hn⟩ := h J _ hc'
    have h2 : (ℓ.rTensor J) x = 0 := by
      rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers a)]
      refine ⟨⟨a ^ n * c', mul_mem (pow_mem (Submonoid.mem_powers a) n) c'.2⟩, ?_⟩
      rw [Submonoid.smul_def, mul_smul, hn]
    rw [h2, Submonoid.smul_def] at hc
    have hu := IsLocalizedModule.map_units (ℓ.rTensor J) c
    have : (algebraMap R (Module.End R _) c) w = (algebraMap R (Module.End R _) c) 0 := by
      rw [map_zero, Module.algebraMap_end_apply, hc]
    exact (Module.End.isUnit_iff _).mp hu |>.1 this
  · intro h J x hx
    have := hloc J
    have h1 : (ℓ.rTensor J) x = 0 := by
      apply Flat.lTensor_preserves_injective_linearMap J.subtype Subtype.val_injective
      rw [← LinearMap.comp_apply, hsq, LinearMap.comp_apply, hx, map_zero, map_zero]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a)
      (f := ℓ.rTensor J)).mp h1
    exact ⟨n, hn⟩

lemma FlatAway.of_dvd {a b : R} (h : FlatAway a M) (hab : a ∣ b) : FlatAway b M := by
  obtain ⟨c, rfl⟩ := hab
  intro J x hx
  obtain ⟨n, hn⟩ := h J x hx
  exact ⟨n, by rw [mul_pow, mul_comm, mul_smul, hn, smul_zero]⟩

lemma FlatAway.of_pow {a : R} {k : ℕ} (h : FlatAway (a ^ k) M) : FlatAway a M := by
  intro J x hx
  obtain ⟨n, hn⟩ := h J x hx
  exact ⟨k * n, by rwa [pow_mul]⟩

lemma FlatAway.of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] {a : R}
    (h : FlatAway a M) (e : M ≃ₗ[R] N) : FlatAway a N := by
  intro J x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective J e.surjective x
  have key : e.toLinearMap.rTensor R (J.subtype.lTensor M y) =
      J.subtype.lTensor N (e.toLinearMap.rTensor J y) := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply]
  have : J.subtype.lTensor M y = 0 := by
    apply Flat.rTensor_preserves_injective_linearMap (M := R) e.toLinearMap e.injective
    rw [key, hx, map_zero]
  obtain ⟨n, hn⟩ := h J y this
  exact ⟨n, by rw [← map_smul, hn, map_zero]⟩

/-- Extensions of modules that are flat after inverting `a` and `b` are flat after inverting
`a * b`. -/
lemma FlatAway.of_exact {A B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] {i : A →ₗ[R] M} {p : M →ₗ[R] B} (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) {a b : R} (hA : FlatAway a A)
    (hB : FlatAway b B) : FlatAway (a * b) M := by
  intro J x hx
  have h1 : J.subtype.lTensor B (p.rTensor J x) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply, hx, map_zero]
  obtain ⟨n, hn⟩ := hB J _ h1
  rw [← map_smul] at hn
  obtain ⟨y, hy⟩ := ((_root_.rTensor_exact J hex hp) _).1 hn
  have hinj : Function.Injective (i.rTensor R) :=
    Flat.rTensor_preserves_injective_linearMap i hi
  have h2 : J.subtype.lTensor A y = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hy, map_smul, hx, smul_zero]
  obtain ⟨m, hm⟩ := hA J y h2
  refine ⟨m + n, ?_⟩
  have : (a * b) ^ (m + n) = (a ^ n * b ^ m) * a ^ m * b ^ n := by ring
  rw [this, mul_smul, ← hy, ← map_smul, mul_smul, hm, smul_zero, map_zero]

/-- A module which is the increasing union of submodules that are flat after inverting `a` is
flat after inverting `a`. -/
lemma FlatAway.of_iSup {a : R} (N : ℕ → Submodule R M) (hN : Monotone N)
    (htop : ∀ m : M, ∃ i, m ∈ N i) (h : ∀ i, FlatAway a (N i)) : FlatAway a M := by
  have hfin (σ : Finset M) : ∃ i, Submodule.span R (σ : Set M) ≤ N i := by
    classical
    induction σ using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert m σ _ ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, hj⟩ := htop m
      refine ⟨max i j, ?_⟩
      rw [Finset.coe_insert, Submodule.span_insert, sup_le_iff, Submodule.span_singleton_le_iff_mem]
      exact ⟨hN (le_max_right i j) hj, hi.trans (hN (le_max_left i j))⟩
  intro J x hx
  obtain ⟨P, ⟨σ, rfl⟩, y, rfl⟩ := TensorProduct.exists_of_fg x
  have := hfin σ
  obtain ⟨i, hi⟩ := this
  set z := (Submodule.inclusion hi).rTensor J y
  have hz : (N i).subtype.rTensor J z = (Submodule.span R (σ : Set M)).subtype.rTensor J y := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    rfl
  have hinj : Function.Injective ((N i).subtype.rTensor R) :=
    Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  have h2 : J.subtype.lTensor (N i) z = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hz, hx]
  obtain ⟨n, hn⟩ := h i J z h2
  exact ⟨n, by rw [← hz, ← map_smul, hn, map_zero]⟩

universe uA uM in
/-- Generic flatness for finite modules over a polynomial ring in `n` variables, by induction on
`n` (Stacks, Tag 051R). -/
private lemma exists_flatAway_of_mvPolynomial [IsNoetherianRing R] [IsDomain R] (n : ℕ) :
    ∀ (A : Type uA) [CommRing A] [Algebra R A], Nonempty (MvPolynomial (Fin n) R ≃ₐ[R] A) →
      ∀ (M : Type uM) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
        [Module.Finite A M], ∃ a : R, a ≠ 0 ∧ FlatAway a M := by
  induction n with
  | zero =>
    intro A _ _ ⟨e⟩ M _ _ _ _ _
    have e' : R ≃ₐ[R] A := (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.trans e
    have : Module.Finite R A := Module.Finite.equiv e'.toLinearEquiv
    have : Module.Finite R M := Module.Finite.trans A M
    obtain ⟨a, ha, hfree, -⟩ := Module.Finite.exists_free_localizedModule_powers_of_isDomain
      (A := R) (M := M)
    refine ⟨a, ha, (flatAway_iff a).2 ?_⟩
    exact Flat.trans R (Localization (Submonoid.powers a)) _
  | succ n ih =>
    intro A _ _ ⟨e⟩ M _ _ _ _ _
    have : IsNoetherianRing A := isNoetherianRing_of_ringEquiv _ e.toRingEquiv
    -- The subalgebra `T` generated by the first `n` variables, and the last variable `x`.
    let ι : MvPolynomial (Fin n) R →ₐ[R] A :=
      e.toAlgHom.comp (MvPolynomial.rename Fin.castSucc)
    have hι : Function.Injective ι :=
      e.injective.comp (MvPolynomial.rename_injective _ (Fin.castSucc_injective n))
    let T : Subalgebra R A := ι.range
    have eT : MvPolynomial (Fin n) R ≃ₐ[R] T := AlgEquiv.ofInjective ι hι
    have : IsNoetherianRing T := isNoetherianRing_of_ringEquiv _ eT.toRingEquiv
    let x : A := e (MvPolynomial.X (Fin.last n))
    have hT (i : Fin n) : e (MvPolynomial.X i.castSucc) ∈ T :=
      ⟨MvPolynomial.X i, by simp [ι]⟩
    have hgen : ∀ y : A, y ∈ Algebra.adjoin T {x} := by
      intro y
      obtain ⟨p, rfl⟩ := e.surjective y
      induction p using MvPolynomial.induction_on with
      | C r =>
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, IsScalarTower.algebraMap_apply R T A]
        exact Subalgebra.algebraMap_mem _ _
      | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
      | mul_X p i hp =>
        rw [map_mul]
        refine Subalgebra.mul_mem _ hp ?_
        induction i using Fin.lastCases with
        | last => exact Algebra.subset_adjoin rfl
        | cast i => exact Subalgebra.algebraMap_mem (Algebra.adjoin T {x}) (⟨_, hT i⟩ : T)
    -- The filtration `M i = span_T {x^j m | j ≤ i, m ∈ σ}`.
    obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := A) (M := M)
    classical
    let gens (i : ℕ) : Finset M :=
      (Finset.range (i + 1) ×ˢ σ).image fun jm ↦ x ^ jm.1 • jm.2
    let N (i : ℕ) : Submodule T M := Submodule.span T (gens i)
    have hgens_mono : Monotone gens := by
      intro i j hij
      apply Finset.image_subset_image
      apply Finset.product_subset_product_left
      exact Finset.range_subset_range.mpr (by omega)
    have hN : Monotone N := fun i j hij ↦ Submodule.span_mono (by exact_mod_cast hgens_mono hij)
    have hxN (i : ℕ) : ∀ y ∈ N i, x • y ∈ N (i + 1) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨⟨j, m⟩, hjm, rfl⟩ := Finset.mem_image.mp hy
        simp only [Finset.mem_product, Finset.mem_range] at hjm
        apply Submodule.subset_span
        refine Finset.mem_image.mpr ⟨(j + 1, m), ?_, ?_⟩
        · simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hjm.2⟩
        · simp [pow_succ', mul_smul]
      | zero => simp
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul t y _ hy =>
        rw [smul_comm]
        exact Submodule.smul_mem _ t hy
    have htop : ∀ m : M, ∃ i, m ∈ N i := by
      have hU : ∀ y : A, ∀ m : M, (∃ i, m ∈ N i) → ∃ i, y • m ∈ N i := by
        intro y
        induction hgen y using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Set.mem_singleton_iff] at hy
          subst hy
          rintro m ⟨i, hi⟩
          exact ⟨i + 1, hxN i m hi⟩
        | algebraMap t =>
          rintro m ⟨i, hi⟩
          exact ⟨i, by rw [algebraMap_smul]; exact Submodule.smul_mem _ t hi⟩
        | add y z _ _ hy hz =>
          intro m hm
          obtain ⟨i, hi⟩ := hy m hm
          obtain ⟨j, hj⟩ := hz m hm
          exact ⟨max i j, by
            rw [add_smul]
            exact Submodule.add_mem _ (hN (le_max_left i j) hi) (hN (le_max_right i j) hj)⟩
        | mul y z _ _ hy hz =>
          intro m hm
          obtain ⟨i, hi⟩ := hz m hm
          rw [mul_smul]
          exact hy _ ⟨i, hi⟩
      intro m
      have hm : m ∈ Submodule.span A (σ : Set M) := hσ ▸ trivial
      induction hm using Submodule.span_induction with
      | mem m hm =>
        exact ⟨0, Submodule.subset_span (Finset.mem_image.mpr
          ⟨(0, m), Finset.mem_product.mpr ⟨by simp, hm⟩, by simp⟩)⟩
      | zero => exact ⟨0, zero_mem _⟩
      | add y z _ _ hy hz =>
        obtain ⟨i, hi⟩ := hy
        obtain ⟨j, hj⟩ := hz
        exact ⟨max i j, Submodule.add_mem _ (hN (le_max_left i j) hi) (hN (le_max_right i j) hj)⟩
      | smul y m _ hm => exact hU y m hm
    -- Multiplication by `x ^ k` raises the filtration degree by `k`.
    let μ (k : ℕ) : M →ₗ[T] M := (LinearMap.lsmul A M (x ^ k)).restrictScalars T
    have hμ (k : ℕ) : ∀ i, ∀ y ∈ N i, μ k y ∈ N (i + k) := by
      induction k with
      | zero => intro i y hy; simpa [μ] using hy
      | succ k ih' =>
        intro i y hy
        have := hxN _ _ (ih' i y hy)
        simpa [μ, pow_succ', mul_smul, ← add_assoc] using this
    -- The graded pieces `Q i = N (i + 1) ⧸ N i` are quotients of `Q 0` via `x ^ i`.
    let Q (i : ℕ) := ↥(N (i + 1)) ⧸ (N i).comap (N (i + 1)).subtype
    let ψ (i : ℕ) : ↥(N 1) →ₗ[T] Q i :=
      ((N i).comap (N (i + 1)).subtype).mkQ ∘ₗ
        (μ i).restrict (p := N 1) (q := N (i + 1)) fun y hy ↦ by
          simpa [add_comm] using hμ i 1 y hy
    have hψ (i : ℕ) : (N 0).comap (N 1).subtype ≤ LinearMap.ker (ψ i) := by
      intro y hy
      rw [LinearMap.mem_ker]
      erw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simpa [Submodule.mem_comap] using hμ i 0 y hy
    let Θ (i : ℕ) : Q 0 →ₗ[T] Q i := ((N 0).comap (N 1).subtype).liftQ (ψ i) (hψ i)
    have hΘ (i : ℕ) : Function.Surjective (Θ i) := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | H z =>
        have hle : N (i + 1) ≤ N i ⊔ (N 1).map (μ i) := by
          rw [Submodule.span_le]
          intro w hw
          obtain ⟨⟨j, m⟩, hjm, rfl⟩ := Finset.mem_image.mp hw
          simp only [Finset.mem_product, Finset.mem_range] at hjm
          rcases Nat.lt_or_ge j (i + 1) with hj | hj
          · apply Submodule.mem_sup_left
            apply Submodule.subset_span
            exact Finset.mem_image.mpr ⟨(j, m), by simp [hjm.2, hj], rfl⟩
          · obtain rfl : j = i + 1 := by omega
            apply Submodule.mem_sup_right
            refine ⟨x • m, Submodule.subset_span (Finset.mem_image.mpr ⟨(1, m), ?_, ?_⟩), ?_⟩
            · simp [hjm.2]
            · simp
            · simp [μ, smul_smul, ← pow_succ']
        obtain ⟨u, hu, _, ⟨y, hy, rfl⟩, hz⟩ := Submodule.mem_sup.mp (hle z.2)
        refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
        erw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq, Submodule.mem_comap]
        have h' : (μ i) y - (z : M) = -u := by rw [← hz]; abel
        simpa [LinearMap.coe_restrict_apply, h'] using (N i).neg_mem hu
    let L (i : ℕ) : Submodule T (Q 0) := LinearMap.ker (Θ i)
    have hL : Monotone L := by
      refine monotone_nat_of_le_succ fun i v hv ↦ ?_
      induction v using Submodule.Quotient.induction_on with
      | H y =>
        change Θ i _ = 0 at hv
        change Θ (i + 1) _ = 0
        erw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at hv ⊢
        rw [Submodule.mem_comap] at hv ⊢
        have := hxN i _ hv
        simpa [μ, pow_succ', mul_smul] using this
    have : IsNoetherian T (Q 0) := inferInstance
    obtain ⟨i₀, hi₀⟩ := monotone_stabilizes_iff_noetherian.mpr this ⟨L, hL⟩
    have hker (i : ℕ) : LinearMap.ker (Θ i) = L (min i i₀) := by
      rcases le_total i i₀ with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h]
        exact (hi₀ i h).symm
    -- Apply the induction hypothesis to `N 0` and to the quotients `Q 0 ⧸ L j`, `j ≤ i₀`.
    obtain ⟨a₀, ha₀, h₀⟩ := ih T ⟨eT⟩ (N 0)
    have hQ (j : ℕ) : ∃ b : R, b ≠ 0 ∧ FlatAway b (Q 0 ⧸ L j) := ih T ⟨eT⟩ _
    choose b hb₀ hb using hQ
    set a := a₀ * ∏ j ∈ Finset.range (i₀ + 1), b j
    have ha : a ≠ 0 := mul_ne_zero ha₀ (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hb₀ j)
    have hQa (i : ℕ) : FlatAway a (Q i) := by
      have hj : min i i₀ ∈ Finset.range (i₀ + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _))
      have h1 : FlatAway a (Q 0 ⧸ L (min i i₀)) :=
        (hb _).of_dvd (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem b hj) _)
      have e₁ : (Q 0 ⧸ L (min i i₀)) ≃ₗ[T] Q i :=
        (Submodule.quotEquivOfEq _ _ (hker i).symm).trans
          ((Θ i).quotKerEquivOfSurjective (hΘ i))
      exact h1.of_linearEquiv (e₁.restrictScalars R)
    have hNa (i : ℕ) : FlatAway a (N i) := by
      induction i with
      | zero => exact h₀.of_dvd (Dvd.intro _ rfl)
      | succ i ih' =>
        have e₂ : ↥(N i) ≃ₗ[T] ↥((N i).comap (N (i + 1)).subtype) :=
          (Submodule.comapSubtypeEquivOfLe (hN (Nat.le_succ i))).symm
        have h1 : FlatAway a ↥((N i).comap (N (i + 1)).subtype) :=
          ih'.of_linearEquiv (e₂.restrictScalars R)
        set K := (N i).comap (N (i + 1)).subtype
        have hex : Function.Exact (K.subtype.restrictScalars R) (K.mkQ.restrictScalars R) :=
          LinearMap.exact_subtype_mkQ K
        have h2 := FlatAway.of_exact (M := ↥(N (i + 1))) (B := Q i)
          (i := K.subtype.restrictScalars R) (p := K.mkQ.restrictScalars R)
          (by rw [LinearMap.coe_restrictScalars]; exact K.injective_subtype)
          (by rw [LinearMap.coe_restrictScalars]; exact K.mkQ_surjective) hex h1 (hQa i)
        rw [← pow_two] at h2
        exact h2.of_pow
    exact ⟨a, ha, FlatAway.of_iSup (fun i ↦ (N i).restrictScalars R)
      (fun i j hij ↦ hN hij) htop hNa⟩

/-- **Generic flatness** (Stacks, Tag 051R). Let `R` be a noetherian domain, `S` a finite type
`R`-algebra and `M` a finite `S`-module. Then there is a nonzero `a ∈ R` such that `M_a` is flat
over `R`. -/
theorem exists_flat_localizedModule_powers [IsNoetherianRing R] [IsDomain R] {S : Type*}
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (M : Type*) [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.Finite S M] :
    ∃ a : R, a ≠ 0 ∧ Flat R (LocalizedModule (Submonoid.powers a) M) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let := Module.compHom M f.toRingHom
  have : IsScalarTower R (MvPolynomial (Fin n) R) M := by
    refine ⟨fun r p m ↦ ?_⟩
    change f (r • p) • m = r • f p • m
    rw [map_smul, smul_assoc]
  have : Module.Finite (MvPolynomial (Fin n) R) M := by
    obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := S) (M := M)
    refine ⟨⟨σ, eq_top_iff.mpr fun m hm' ↦ ?_⟩⟩
    clear hm'
    have hm : m ∈ Submodule.span S (σ : Set M) := hσ ▸ trivial
    induction hm using Submodule.span_induction with
    | mem m hm => exact Submodule.subset_span hm
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul s m _ hm =>
      obtain ⟨p, rfl⟩ := hf s
      exact Submodule.smul_mem _ p hm
  obtain ⟨a, ha, h⟩ := exists_flatAway_of_mvPolynomial n (MvPolynomial (Fin n) R)
    ⟨AlgEquiv.refl⟩ M
  exact ⟨a, ha, (flatAway_iff a).mp h⟩

end GenericFlatness

/-- **Finitely presented flat modules are locally free.** If `M` is a finitely presented flat
`R`-module and `p` is a prime of `R`, then `M_r` is a finite free `R_r`-module for some `r ∉ p`:
the localization `M_p` is free over the local ring `R_p`, and a basis of `M_p` spreads out to a
basis of some `M_r`. -/
theorem exists_free_localizedModule_powers_of_flat {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, Module.Free (Localization.Away r) (LocalizedModule.Away r M) ∧
      Module.Finite (Localization.Away r) (LocalizedModule.Away r M) := by
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  exact ⟨r, hr, hfree, Module.Finite.of_isLocalizedModule (.powers r)
    (LocalizedModule.mkLinearMap (.powers r) M)⟩

end Module
