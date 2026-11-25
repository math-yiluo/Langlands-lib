/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import WeilConjectures.Mathlib.RingTheory.Filtration
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Openness of the flat locus

Let `R` be a noetherian ring, `S` a finite type `R`-algebra and `M` a finite `S`-module. The set
of primes `q` of `S` such that `M_q` is flat over `R` is open (Stacks, Tag 00RC; Matsumura,
Theorem 24.3).

## Main results

- `Module.lTensor_localizedModule_injective_iff`: injectivity of `M_T ⊗ N' → M_T ⊗ N` in terms of
  the kernel of `M ⊗ N' → M ⊗ N`.
- `Module.flat_localizedModule_iff`: flatness of `M_T` in terms of the kernels of `M ⊗ J → M`.
- `Module.exists_notMem_pow_smul_eq_zero`: generic flatness relative to a prime of the base.
- `Module.Flat.exists_notMem_forall_flat_localizedModule`: openness of the flat locus.
- `Module.Flat.of_bijective_smul`: a module over a domain on which nonzero elements act bijectively
  is flat.
- `Algebra.exists_notMem_forall_pow_smul_eq_zero`: the local criterion for regular elements of
  the fibre over a noetherian base, for all base changes.
- `Module.Flat.localization_of_isPushout`: flatness at a point is stable under base change.
- `Module.Flat.localization_of_forall_mem_isClosed`: localizing away from a closed set of
  flat points gives a flat algebra.
- `Module.Flat.localization_tensorProduct_map`: flatness of `R ⊗[R₀] S₀` over `R` at a point is
  preserved by a map of `R₀`-algebras `R → R'`.
- `PrimeSpectrum.isOpen_setOf_flat_localization`: the flat locus of a finite type algebra over a
  noetherian ring is open (Stacks, Tag 00RC).
-/

@[expose] public section

open TensorProduct

namespace Module.Flat

/-- A module over a domain on which every nonzero element acts bijectively is flat: it is a
vector space over the fraction field. -/
theorem of_bijective_smul {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    (h : ∀ r : R, r ≠ 0 → Function.Bijective (fun m : M ↦ r • m)) : Flat R M := by
  let S := nonZeroDivisors R
  have : IsLocalizedModule S (LinearMap.id : M →ₗ[R] M) :=
    { map_units := fun s ↦ (Module.End.isUnit_iff _).mpr (h s (nonZeroDivisors.ne_zero s.2))
      surj := fun y ↦ ⟨(y, 1), by simp⟩
      exists_of_eq := fun {x y} hxy ↦ ⟨1, by simpa using hxy⟩ }
  have : Flat R (LocalizedModule S M) :=
    (Module.flat_iff_of_isLocalization (Localization S) S _).mp inferInstance
  exact Flat.of_linearEquiv (IsLocalizedModule.iso S (LinearMap.id : M →ₗ[R] M)).symm

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Purity for modules over a prime.** If every `r ∉ p` acts bijectively on `M`, then
`M ⊗ N' → M ⊗ N` is injective whenever `N' ≤ N` and `N` is killed by `p`: indeed `M ⧸ p M` is
a vector space over the fraction field of `R ⧸ p`. -/
theorem lTensor_subtype_injective_of_bijective_smul (p : Ideal R) [p.IsPrime]
    (hM : ∀ r ∉ p, Function.Bijective (fun m : M ↦ r • m)) {N : Type*} [AddCommGroup N]
    [Module R N] (hN : ∀ i ∈ p, ∀ n : N, i • n = 0) (N' : Submodule R N) :
    Function.Injective (N'.subtype.lTensor M) := by
  have : Flat (R ⧸ p) (M ⧸ p • (⊤ : Submodule R M)) := by
    refine of_bijective_smul fun r hr ↦ ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hrp : r ∉ p := fun h ↦ hr (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    let e := LinearEquiv.ofBijective (DistribSMul.toLinearMap R M r) (hM r hrp)
    have hsmul (m : M) : (Ideal.Quotient.mk p r) •
        (Submodule.Quotient.mk m : M ⧸ p • (⊤ : Submodule R M)) =
          Submodule.Quotient.mk (r • m) := rfl
    constructor
    · intro x y hxy
      induction x using Submodule.Quotient.induction_on with | H x =>
      induction y using Submodule.Quotient.induction_on with | H y =>
      simp only [hsmul, Submodule.Quotient.eq] at hxy ⊢
      have := Submodule.smul_top_le_comap_smul_top p e.symm.toLinearMap hxy
      rw [Submodule.mem_comap, ← smul_sub] at this
      convert this using 1
      exact (e.symm_apply_apply (x - y)).symm
    · intro x
      induction x using Submodule.Quotient.induction_on with | H x =>
      refine ⟨Submodule.Quotient.mk (e.symm x), ?_⟩
      change _ • _ = _
      rw [hsmul]
      congr 1
      exact e.apply_symm_apply x
  exact lTensor_subtype_injective_of_smul_eq_zero p hN N'

end Module.Flat

namespace Module

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [Module S M] [IsScalarTower R S M]

/-- Let `T` be a multiplicative subset of `S` and `ℓ : M → L` a localization at `T`. Then
`L ⊗ N' → L ⊗ N` is injective if and only if every element of the kernel of `M ⊗ N' → M ⊗ N` is
killed by an element of `T`. -/
lemma lTensor_injective_iff_of_isLocalizedModule (T : Submonoid S) {L : Type*} [AddCommGroup L]
    [Module R L] [Module S L] [IsScalarTower R S L] (ℓ : M →ₗ[S] L) [IsLocalizedModule T ℓ]
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (f : N' →ₗ[R] N) :
    Function.Injective (f.lTensor L) ↔
      ∀ y : M ⊗[R] N', f.lTensor M y = 0 → ∃ t ∈ T, t • y = 0 := by
  let g' := AlgebraTensorModule.rTensor R N' ℓ
  let g := AlgebraTensorModule.rTensor R N ℓ
  have : IsLocalizedModule T g' := IsLocalizedModule.rTensor (A := S) T ℓ
  have : IsLocalizedModule T g := IsLocalizedModule.rTensor (A := S) T ℓ
  let fM := AlgebraTensorModule.lTensor S M f
  let fL := AlgebraTensorModule.lTensor S L f
  have hsq (y : M ⊗[R] N') : fL (g' y) = g (fM y) := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]
    | tmul m n => rfl
  constructor
  · intro h y hy
    have h1 : g' y = 0 := by
      apply h
      rw [map_zero]
      change fL (g' y) = 0
      rw [hsq]
      change g (f.lTensor M y) = 0
      rw [hy, map_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T (f := g')).mp h1
    exact ⟨t, t.2, ht⟩
  · intro h
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨⟨y, s⟩, hs⟩ := IsLocalizedModule.surj T g' w
    simp only at hs
    have h1 : g (fM y) = 0 := by
      rw [← hsq, ← hs, Submonoid.smul_def, map_smul]
      change (s : S) • f.lTensor L w = 0
      rw [hw, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T (f := g)).mp h1
    rw [Submonoid.smul_def, ← map_smul] at ht
    obtain ⟨t', ht', ht'y⟩ := h _ ht
    have h2 : g' y = 0 := by
      rw [IsLocalizedModule.eq_zero_iff T]
      exact ⟨⟨t' * t, mul_mem ht' t.2⟩, by rw [Submonoid.smul_def, mul_smul]; exact ht'y⟩
    rw [h2, Submonoid.smul_def] at hs
    have hu := IsLocalizedModule.map_units g' s
    have : (algebraMap S (Module.End S _) s) w = (algebraMap S (Module.End S _) s) 0 := by
      rw [map_zero, Module.algebraMap_end_apply, hs]
    exact (Module.End.isUnit_iff _).mp hu |>.1 this

/-- Let `T` be a multiplicative subset of `S`. Then `M_T ⊗ N' → M_T ⊗ N` is injective if and only
if every element of the kernel of `M ⊗ N' → M ⊗ N` is killed by an element of `T`. -/
lemma lTensor_localizedModule_injective_iff (T : Submonoid S) {N N' : Type*} [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] (f : N' →ₗ[R] N) :
    Function.Injective (f.lTensor (LocalizedModule T M)) ↔
      ∀ y : M ⊗[R] N', f.lTensor M y = 0 → ∃ t ∈ T, t • y = 0 :=
  lTensor_injective_iff_of_isLocalizedModule T (LocalizedModule.mkLinearMap T M) f

/-- Let `T` be a multiplicative subset of `S`. Then `M_T` is flat over `R` if and only if every
element of the kernel of `M ⊗ J → M`, `J` an ideal of `R`, is killed by an element of `T`. -/
lemma flat_localizedModule_iff (T : Submonoid S) :
    Flat R (LocalizedModule T M) ↔ ∀ (J : Ideal R) (y : M ⊗[R] J),
      J.subtype.lTensor M y = 0 → ∃ t ∈ T, t • y = 0 := by
  rw [Flat.iff_lTensor_injective']
  exact forall_congr' fun J ↦ lTensor_localizedModule_injective_iff T J.subtype

universe v in
/-- **Generic flatness relative to a prime of the base.** Let `R` be noetherian, `p` a prime of
`R`, `S` a finite type `R`-algebra and `M` a finite `S`-module killed by `p`. Then there is
`a ∉ p` such that for every injective map `N' → N` of modules killed by `p`, every element of the
kernel of `M ⊗ N' → M ⊗ N` is killed by a power of `a`. This is generic flatness
(`Module.exists_flat_localizedModule_powers`) over the domain `R ⧸ p`. -/
theorem exists_notMem_pow_smul_eq_zero [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    [Algebra.FiniteType R S] [Module.Finite S M] (hM : ∀ r ∈ p, ∀ m : M, r • m = 0) :
    ∃ a ∉ p, ∀ (N N' : Type v) [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'],
      (∀ r ∈ p, ∀ n : N, r • n = 0) → (∀ r ∈ p, ∀ n : N', r • n = 0) →
      ∀ f : N' →ₗ[R] N, Function.Injective f →
      ∀ y : M ⊗[R] N', f.lTensor M y = 0 → ∃ k : ℕ, a ^ k • y = 0 := by
  have hMt : IsTorsionBySet R M p := fun m r ↦ hM r r.2 m
  have hMS : IsTorsionBySet S M (p.map (algebraMap R S)) := by
    intro m ⟨s, hs⟩
    change s • m = 0
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨r, hr, rfl⟩ := hs
      rw [algebraMap_smul]
      exact hM r hr m
    | zero => exact zero_smul _ _
    | add s t _ _ hs ht => rw [add_smul, hs, ht, add_zero]
    | smul s t _ ht => rw [smul_eq_mul, mul_smul, ht, smul_zero]
  let := hMt.module
  let := hMS.module
  let : Algebra (R ⧸ p) (S ⧸ p.map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower (R ⧸ p) (S ⧸ p.map (algebraMap R S)) M := by
    refine ⟨fun a s m ↦ ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h1 : Ideal.Quotient.mk p a • Ideal.Quotient.mk (p.map (algebraMap R S)) s =
        Ideal.Quotient.mk (p.map (algebraMap R S)) (algebraMap R S a * s) := by
      rw [Algebra.smul_def]
      rfl
    rw [h1]
    erw [Module.IsTorsionBySet.mk_smul]
    change (algebraMap R S a * s) • m = a • (s • m)
    rw [mul_smul, algebraMap_smul]
  have : Algebra.FiniteType R (S ⧸ p.map (algebraMap R S)) :=
    Algebra.FiniteType.trans (S := S) ‹_› inferInstance
  have : IsScalarTower R (R ⧸ p) (S ⧸ p.map (algebraMap R S)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  have : Algebra.FiniteType (R ⧸ p) (S ⧸ p.map (algebraMap R S)) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have : Module.Finite (S ⧸ p.map (algebraMap R S)) M := by
    obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := S) (M := M)
    refine ⟨⟨σ, eq_top_iff.mpr fun m hm' ↦ ?_⟩⟩
    clear hm'
    have hm : m ∈ Submodule.span S (σ : Set M) := hσ ▸ trivial
    induction hm using Submodule.span_induction with
    | mem m hm => exact Submodule.subset_span hm
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul s m _ hm => exact Submodule.smul_mem _ (Ideal.Quotient.mk _ s) hm
  obtain ⟨ā, hā, hflat⟩ := exists_flat_localizedModule_powers (R := R ⧸ p)
    (S := S ⧸ p.map (algebraMap R S)) M
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective ā
  refine ⟨a, fun ha ↦ hā (Ideal.Quotient.eq_zero_iff_mem.mpr ha), ?_⟩
  intro N N' _ _ _ _ hN hN' f hf y hy
  let := (show IsTorsionBySet R N p from fun n r ↦ hN r r.2 n).module
  let := (show IsTorsionBySet R N' p from fun n r ↦ hN' r r.2 n).module
  let f' : N' →ₗ[R ⧸ p] N :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        rintro ⟨r⟩ n
        exact f.map_smul r n }
  have hinj : Function.Injective
      (f'.lTensor (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk p a)) M)) :=
    Flat.lTensor_preserves_injective_linearMap f' hf
  rw [lTensor_localizedModule_injective_iff (R := R ⧸ p) (S := R ⧸ p)] at hinj
  have hsurj : Function.Surjective (algebraMap R (R ⧸ p)) := Ideal.Quotient.mk_surjective
  have : CompatibleSMul R (R ⧸ p) M N := CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  have : CompatibleSMul R (R ⧸ p) M N' := CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  let e' := equivOfCompatibleSMul R (R ⧸ p) R M N'
  let e := equivOfCompatibleSMul R (R ⧸ p) R M N
  have hcomm (z : M ⊗[R ⧸ p] N') : e (f'.lTensor M z) = f.lTensor M (e' z) := by
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
    | tmul m n => rfl
  obtain ⟨_, ⟨k, rfl⟩, ht⟩ := hinj (e'.symm y) (by
    apply e.injective
    rw [hcomm, LinearEquiv.apply_symm_apply, hy, map_zero])
  refine ⟨k, ?_⟩
  have hsmul (z : M ⊗[R ⧸ p] N') : a ^ k • z = (Ideal.Quotient.mk p a) ^ k • z := by
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => rw [smul_add, smul_add, hz, hw]
    | tmul m n =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← map_pow]
      rfl
  apply e'.symm.injective
  rw [map_zero, map_smul, hsmul, ht]

omit [Module R M] [IsScalarTower R S M] in
lemma _root_.Submodule.restrictScalars_map_smul_top [Module R M] [IsScalarTower R S M]
    (I : Ideal R) :
    (I.map (algebraMap R S) • (⊤ : Submodule S M)).restrictScalars R =
      I • (⊤ : Submodule R M) := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    induction hx using Submodule.smul_induction_on' with
    | smul a ha m _ =>
      induction ha using Submodule.span_induction generalizing m with
      | mem a ha =>
        obtain ⟨r, hr, rfl⟩ := ha
        rw [algebraMap_smul]
        exact Submodule.smul_mem_smul hr trivial
      | zero => rw [zero_smul]; exact zero_mem _
      | add a b _ _ ha hb =>
        rw [add_smul]; exact Submodule.add_mem _ (ha m trivial) (hb m trivial)
      | smul s a _ ha => rw [smul_eq_mul, mul_comm, mul_smul]; exact ha _ trivial
    | add x _ y _ hx hy => exact Submodule.add_mem _ hx hy
  · rw [Submodule.smul_le]
    intro r hr m _
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul S r m]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial

/-- **Openness of the flat locus** (Stacks, Tag 00RC; Matsumura, Theorem 24.3). Let `R` be a
noetherian ring, `S` a finite type `R`-algebra and `M` a finite `S`-module. If `M_P` is flat over
`R` for a prime `P` of `S`, then there is `g ∉ P` such that `M_Q` is flat over `R` for every prime
`Q` of `S` not containing `g`. (blueprint: `lem-weil-pbc-noetherian-flat-locus-neighborhood`) -/
theorem Flat.exists_notMem_forall_flat_localizedModule [IsNoetherianRing R]
    [Algebra.FiniteType R S] [Module.Finite S M] (P : Ideal S) [P.IsPrime]
    (hP : Flat R (LocalizedModule P.primeCompl M)) :
    ∃ g ∉ P, ∀ (Q : Ideal S) [Q.IsPrime], g ∉ Q → Flat R (LocalizedModule Q.primeCompl M) := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  suffices H : ∃ g ∉ P, ∀ Q : Ideal S, Q.IsPrime → g ∉ Q →
      ∀ [Q.IsPrime], Flat R (LocalizedModule Q.primeCompl M) by
    obtain ⟨g, hg, H⟩ := H
    exact ⟨g, hg, fun Q _ hgQ ↦ H Q ‹_› hgQ⟩
  refine Ideal.exists_notMem_forall_of_isNoetherianRing
    (fun Q ↦ ∀ [Q.IsPrime], Flat R (LocalizedModule Q.primeCompl M)) ?_ ?_ P (by exact hP)
  · intro Q Q' hQp _ hle hQ _
    have hQ := @hQ hQp
    rw [flat_localizedModule_iff] at hQ ⊢
    intro J y hy
    obtain ⟨t, ht, hty⟩ := hQ J y hy
    exact ⟨t, fun h ↦ ht (hle h), hty⟩
  intro Q₀ hQ₀ hU
  have := hQ₀
  have hU := @hU hQ₀
  set p₀ := Q₀.comap (algebraMap R S)
  -- (1) The kernel of `M ⊗ p₀ → M` is killed by a single `b ∉ Q₀`.
  set K := LinearMap.ker (AlgebraTensorModule.lTensor S M p₀.subtype)
  have : Module.Finite R p₀ := IsNoetherian.finite R p₀
  have : Module.Finite S (M ⊗[R] p₀) :=
    Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange R S S M p₀)
  obtain ⟨σ, hσ⟩ := (IsNoetherian.noetherian K : K.FG)
  have hσK : ∀ y ∈ σ, ∃ t ∉ Q₀, t • y = 0 := by
    intro y hy
    have hyK : y ∈ K := hσ ▸ Submodule.subset_span hy
    obtain ⟨t, ht, hty⟩ := (flat_localizedModule_iff _).mp hU p₀ y hyK
    exact ⟨t, ht, hty⟩
  choose! t ht hty using hσK
  set b := ∏ y ∈ σ, t y
  have hb : b ∉ Q₀ := by
    rw [Ideal.IsPrime.prod_mem_iff]
    push Not
    exact fun y hy ↦ ht y hy
  have hbK : ∀ y ∈ K, b • y = 0 := by
    intro y hy
    rw [← hσ] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      change (∏ y ∈ σ, t y) • y = 0
      rw [← Finset.prod_erase_mul σ t hy, mul_smul, hty y hy, smul_zero]
    | zero => exact smul_zero _
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul s y _ hy => rw [smul_comm, hy, smul_zero]
  -- (2) Generic flatness of `M ⧸ p₀ M` over `R ⧸ p₀`.
  set P₀ := p₀.map (algebraMap R S) • (⊤ : Submodule S M)
  have hkill : ∀ r ∈ p₀, ∀ m : M ⧸ P₀, r • m = 0 := by
    intro r hr m
    induction m using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← algebraMap_smul S r m]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
  obtain ⟨a, ha, hGF⟩ := exists_notMem_pow_smul_eq_zero.{_, _, _, _} (S := S) p₀ (M := M ⧸ P₀) hkill
  have ha' : algebraMap R S a ∉ Q₀ := ha
  refine ⟨b * algebraMap R S a, fun h ↦ (hQ₀.mul_mem_iff_mem_or_mem.mp h).elim hb ha', ?_⟩
  intro Q hQ hle hg _
  have hbQ : b ∉ Q := fun h ↦ hg (Q.mul_mem_right _ h)
  have haQ : algebraMap R S a ∉ Q := fun h ↦ hg (Q.mul_mem_left _ h)
  -- (3) The local criterion at `Q`.
  have hπ : (Submodule.restrictScalars R P₀) = p₀ • (⊤ : Submodule R M) :=
    Submodule.restrictScalars_map_smul_top p₀
  let φ : (M ⧸ p₀ • (⊤ : Submodule R M)) ≃ₗ[R] M ⧸ P₀ :=
    (Submodule.quotEquivOfEq _ _ hπ.symm).trans (Submodule.Quotient.restrictScalarsEquiv R P₀)
  have hbij (N : Type u_1) [AddCommGroup N] [Module R N] (hN : ∀ r ∈ p₀, ∀ n : N, r • n = 0) :
      Function.Bijective ((P₀.mkQ.restrictScalars R).rTensor N) := by
    have : (P₀.mkQ.restrictScalars R).rTensor N =
        φ.toLinearMap.rTensor N ∘ₗ (p₀ • (⊤ : Submodule R M)).mkQ.rTensor N := by
      rw [← LinearMap.rTensor_comp]
      rfl
    rw [this, LinearMap.coe_comp]
    exact (LinearEquiv.bijective (φ.rTensor N)).comp
      (Flat.bijective_rTensor_mkQ_of_smul_eq_zero p₀ hN)
  have hjac : p₀.map (algebraMap R (Localization.AtPrime Q)) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q),
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q]
    exact hle hr
  refine Flat.of_lTensor_injective_of_forall (S := Localization.AtPrime Q) p₀ hjac ?_ ?_
  · intro N _ _ hN N'
    rw [lTensor_localizedModule_injective_iff]
    intro y hy
    have hN' : ∀ r ∈ p₀, ∀ n : N', r • n = 0 := fun r hr n ↦ Subtype.ext (hN r hr n)
    set π := P₀.mkQ.restrictScalars R
    have h1 : N'.subtype.lTensor (M ⧸ P₀) (π.rTensor N' y) = 0 := by
      rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
        LinearMap.comp_apply, hy, map_zero]
    obtain ⟨k, hk⟩ := hGF N N' hN hN' N'.subtype Subtype.val_injective _ h1
    refine ⟨algebraMap R S a ^ k, fun h ↦ haQ (hQ.mem_of_pow_mem k h), ?_⟩
    apply (hbij (↥N') hN').1
    rw [map_zero, ← map_pow, algebraMap_smul, map_smul, hk]
  · rw [lTensor_localizedModule_injective_iff]
    intro y hy
    exact ⟨b, hbQ, hbK y hy⟩

omit [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] in
/-- For a tower `R → A → B` and an ideal `I` of `R`, the `A`-submodule `(I A) • B` is the ideal
`I B` of `B`. -/
lemma _root_.Ideal.mem_map_smul_top_iff {A : Type*} [CommRing A] [Algebra R A] [Algebra A S]
    [IsScalarTower R A S] (I : Ideal R) (y : S) :
    y ∈ (I.map (algebraMap R A) • (⊤ : Submodule A S)) ↔ y ∈ I.map (algebraMap R S) := by
  constructor
  · intro hy
    induction hy using Submodule.smul_induction_on' with
    | smul a ha b _ =>
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have : (I.map (algebraMap R A)).map (algebraMap A S) = I.map (algebraMap R S) := by
        rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      exact this ▸ Ideal.mem_map_of_mem _ ha
    | add x _ y _ hx hy => exact Ideal.add_mem _ hx hy
  · intro hy
    have hmul : ∀ b : S, ∀ z ∈ (I.map (algebraMap R A) • (⊤ : Submodule A S)),
        b * z ∈ (I.map (algebraMap R A) • (⊤ : Submodule A S)) := by
      intro b z hz
      induction hz using Submodule.smul_induction_on' with
      | smul a ha c _ =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem_smul ha trivial
      | add x _ y _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      rw [IsScalarTower.algebraMap_apply R A S, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul b y _ hy => exact hmul b y hy

omit [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] in
/-- **Regular elements of the fibre, noetherian case** (Stacks, Tags 00MF and 00RC). Let `R` be
noetherian, `S` a finite type `R`-algebra, `q` a prime of `S` with `S_q` flat over `R`, and
`f ∈ S` a nonzerodivisor of the fibre `S_q ⧸ p S_q`, `p = q ∩ R`. Then there is `g ∉ q` such that
`f` is a nonzerodivisor on `S_g` and `(S ⧸ f)_g` is flat over `R`. -/
theorem _root_.Algebra.exists_notMem_flat_localizedModule_quotient [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime] [Flat R (Localization.AtPrime q)] (f : S)
    (hfib : ∀ m : Localization.AtPrime q,
      algebraMap S _ f * m ∈ (q.comap (algebraMap R S)).map (algebraMap R _) →
        m ∈ (q.comap (algebraMap R S)).map (algebraMap R (Localization.AtPrime q))) :
    ∃ g ∉ q, (∀ x : S, f * x = 0 → g * x = 0) ∧
      Flat R (LocalizedModule (Submonoid.powers g) (S ⧸ Ideal.span {f})) := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  set p := q.comap (algebraMap R S)
  set Sq := Localization.AtPrime q
  let φR : Localization.AtPrime p →+* Sq := Localization.localRingHom p q (algebraMap R S) rfl
  let : Algebra (Localization.AtPrime p) Sq := φR.toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) Sq := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R S Sq]
    exact (Localization.localRingHom_to_map p q (algebraMap R S) rfl r).symm
  have : IsLocalHom (algebraMap (Localization.AtPrime p) Sq) :=
    Localization.isLocalHom_localRingHom p q (algebraMap R S) rfl
  have : Flat (Localization.AtPrime p) Sq :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl Sq).mpr
      inferInstance
  set s := algebraMap S Sq f
  set mR := IsLocalRing.maximalIdeal (Localization.AtPrime p)
  have hmax : mR.map (algebraMap _ Sq) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h ↦ (IsLocalRing.mem_maximalIdeal _).mp hx (isUnit_of_map_unit _ _ h)
  have hmR : mR = p.map (algebraMap R (Localization.AtPrime p)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hs : ∀ m : Sq, s • m ∈ mR • (⊤ : Submodule (Localization.AtPrime p) Sq) →
      m ∈ mR • (⊤ : Submodule (Localization.AtPrime p) Sq) := by
    intro m
    rw [hmR, Ideal.mem_map_smul_top_iff, Ideal.mem_map_smul_top_iff, smul_eq_mul]
    exact hfib m
  have key :=
    Flat.rTensor_toLinearMap_injective (R := Localization.AtPrime p) (M := Sq) mR hmax s hs
  set φ := DistribSMul.toLinearMap (Localization.AtPrime p) Sq s
  -- `s` is a nonzerodivisor of `S_q`.
  have hreg : ∀ m : Sq, s * m = 0 → m = 0 := by
    intro m hm
    have h := key (Localization.AtPrime p) (a₁ := m ⊗ₜ 1) (a₂ := 0) (by
      rw [map_zero, LinearMap.rTensor_tmul]
      simp [φ, smul_eq_mul, hm])
    simpa using congr(TensorProduct.rid _ Sq $h)
  -- `S_q ⧸ s` is flat.
  have hq : Flat (Localization.AtPrime p) (Sq ⧸ LinearMap.range φ) := by
    refine Flat.quotient_range φ fun J m hm ↦ ?_
    let e := TensorProduct.tensorQuotEquivQuotSMul Sq J
    have he (x : Sq ⊗[Localization.AtPrime p] (Localization.AtPrime p ⧸ J)) :
        e (φ.rTensor _ x) = (J • (⊤ : Submodule (Localization.AtPrime p) Sq)).mapQ (J • ⊤) φ
          (fun y hy ↦ by
            rw [Submodule.mem_comap]
            change s • y ∈ J • (⊤ : Submodule (Localization.AtPrime p) Sq)
            induction hy using Submodule.smul_induction_on' with
            | smul r hr y _ => rw [smul_comm]; exact Submodule.smul_mem_smul hr trivial
            | add y _ z _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz) (e x) := by
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
      | tmul y r =>
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        simp [e, φ, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
    have h0 : φ.rTensor _ (e.symm (Submodule.Quotient.mk m)) = 0 := by
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply, Submodule.mapQ_apply, map_zero,
        Submodule.Quotient.mk_eq_zero]
      exact hm
    have := key (Localization.AtPrime p ⧸ J) (h0.trans (map_zero _).symm)
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hqR : Flat R (Sq ⧸ LinearMap.range φ) := Flat.trans R (Localization.AtPrime p) _
  -- Transfer to the localization of `S ⧸ f`.
  set C := S ⧸ Ideal.span {f}
  let ψ := (Ideal.span {f} : Submodule S S).toLocalizedQuotient' Sq q.primeCompl
    (Algebra.linearMap S Sq)
  let e₁ : LocalizedModule q.primeCompl C ≃ₗ[S] Sq ⧸ (Ideal.span {f} : Submodule S S).localized'
      Sq q.primeCompl (Algebra.linearMap S Sq) := IsLocalizedModule.iso q.primeCompl ψ
  have hloc : (Ideal.span {f} : Submodule S S).localized' Sq q.primeCompl
      (Algebra.linearMap S Sq) = Submodule.span Sq {s} := by
    rw [Submodule.localized'_span, Set.image_singleton]
    rfl
  have hrange : (Submodule.span Sq {s}).restrictScalars (Localization.AtPrime p) =
      LinearMap.range φ := by
    ext x
    rw [Submodule.restrictScalars_mem, ← Ideal.span, Ideal.mem_span_singleton', LinearMap.mem_range]
    exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha, mul_comm]; rfl⟩,
      fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha, mul_comm]; rfl⟩⟩
  let e₂ : (Sq ⧸ Submodule.span Sq {s}) ≃ₗ[Localization.AtPrime p] Sq ⧸ LinearMap.range φ :=
    (Submodule.Quotient.restrictScalarsEquiv _ _).symm.trans (Submodule.quotEquivOfEq _ _ hrange)
  have hflatq : Flat R (LocalizedModule q.primeCompl C) :=
    Flat.of_linearEquiv ((e₁.restrictScalars R).trans
      (((Submodule.quotEquivOfEq _ _ hloc).restrictScalars R).trans (e₂.restrictScalars R)))
  -- Openness of the flat locus.
  obtain ⟨g₁, hg₁, hopen⟩ := Flat.exists_notMem_forall_flat_localizedModule (M := C) q hflatq
  have hC : ∀ (J : Ideal R) (y : C ⊗[R] J), J.subtype.lTensor C y = 0 →
      ∃ n : ℕ, g₁ ^ n • y = 0 := by
    intro J y hy
    have : g₁ ∈ (Submodule.span S {y}).annihilator.radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro Q ⟨haQ, hQ⟩
      by_contra hg
      obtain ⟨t, ht, hty⟩ := (flat_localizedModule_iff _).mp (hopen Q hg) J y hy
      exact ht (haQ ((Submodule.mem_annihilator_span_singleton _ _).mpr hty))
    obtain ⟨n, hn⟩ := this
    exact ⟨n, (Submodule.mem_annihilator_span_singleton _ _).mp hn⟩
  -- `f` is a nonzerodivisor near `q`.
  set K := LinearMap.ker (LinearMap.mulLeft S f)
  obtain ⟨σ, hσ⟩ := (IsNoetherian.noetherian K : K.FG)
  have hσK : ∀ x ∈ σ, ∃ t ∉ q, t * x = 0 := by
    intro x hx
    have hxK : f * x = 0 := LinearMap.mem_ker.mp (hσ ▸ Submodule.subset_span hx)
    have : algebraMap S Sq x = 0 := hreg _ (by rw [← map_mul, hxK, map_zero])
    obtain ⟨⟨t, ht⟩, htx⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl Sq x).mp this
    exact ⟨t, ht, htx⟩
  choose! t ht hty using hσK
  set g₂ := ∏ x ∈ σ, t x
  have hg₂ : g₂ ∉ q := by
    rw [Ideal.IsPrime.prod_mem_iff]
    push Not
    exact fun x hx ↦ ht x hx
  have hg₂K : ∀ x ∈ K, g₂ * x = 0 := by
    intro x hx
    rw [← hσ] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      change (∏ x ∈ σ, t x) * x = 0
      rw [← Finset.prod_erase_mul σ t hx, mul_assoc, hty x hx, mul_zero]
    | zero => exact mul_zero _
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  refine ⟨g₁ * g₂, fun h ↦ (Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹_›).mp h |>.elim hg₁ hg₂,
    fun x hx ↦ ?_, ?_⟩
  · rw [mul_assoc, hg₂K x (LinearMap.mem_ker.mpr hx), mul_zero]
  · rw [flat_localizedModule_iff]
    intro J y hy
    obtain ⟨n, hn⟩ := hC J y hy
    exact ⟨(g₁ * g₂) ^ n, ⟨n, rfl⟩, by rw [mul_pow, mul_comm, mul_smul, hn, smul_zero]⟩

omit [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] in
/-- **Regular elements of the fibre, noetherian case, all base changes.** Let `R` be noetherian,
`S` a finite type `R`-algebra, `q` a prime of `S` with `S_q` flat over `R`, and `f ∈ S` a
nonzerodivisor of the fibre `S_q ⧸ p S_q`. Then there is `g ∉ q` such that for every `R`-module
`N`, every element of `S ⊗ N` killed by `f` is killed by a power of `g`. -/
theorem _root_.Algebra.exists_notMem_forall_pow_smul_eq_zero [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime] [Flat R (Localization.AtPrime q)] (f : S)
    (hfib : ∀ m : Localization.AtPrime q,
      algebraMap S _ f * m ∈ (q.comap (algebraMap R S)).map (algebraMap R _) →
        m ∈ (q.comap (algebraMap R S)).map (algebraMap R (Localization.AtPrime q))) :
    ∃ g ∉ q, ∀ (N : Type*) [AddCommGroup N] [Module R N] (y : S ⊗[R] N), f • y = 0 →
      ∃ n : ℕ, g ^ n • y = 0 := by
  classical
  obtain ⟨g₁, hg₁, hreg, hC⟩ := Algebra.exists_notMem_flat_localizedModule_quotient q f hfib
  have hP : Flat R (LocalizedModule q.primeCompl S) := Flat.of_linearEquiv
    ((IsLocalizedModule.iso q.primeCompl
      (Algebra.linearMap S (Localization.AtPrime q))).restrictScalars R)
  obtain ⟨g₂, hg₂, hopen⟩ := Flat.exists_notMem_forall_flat_localizedModule (M := S) q hP
  have hS : ∀ (J : Ideal R) (y : S ⊗[R] J), J.subtype.lTensor S y = 0 →
      ∃ n : ℕ, g₂ ^ n • y = 0 := by
    intro J y hy
    have : g₂ ∈ (Submodule.span S {y}).annihilator.radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro Q ⟨haQ, hQ⟩
      by_contra hg
      obtain ⟨t, ht, hty⟩ := (flat_localizedModule_iff _).mp (hopen Q hg) J y hy
      exact ht (haQ ((Submodule.mem_annihilator_span_singleton _ _).mpr hty))
    obtain ⟨n, hn⟩ := this
    exact ⟨n, (Submodule.mem_annihilator_span_singleton _ _).mp hn⟩
  set g := g₁ * g₂
  refine ⟨g, fun h ↦ (Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹_›).mp h |>.elim hg₁ hg₂, ?_⟩
  set X := Localization.Away g
  have hX : Flat R X := by
    have : Flat R (LocalizedModule (Submonoid.powers g) S) := by
      rw [flat_localizedModule_iff]
      intro J y hy
      obtain ⟨n, hn⟩ := hS J y hy
      exact ⟨g ^ n, ⟨n, rfl⟩, by rw [mul_pow, mul_smul, hn, smul_zero]⟩
    exact Flat.of_linearEquiv ((IsLocalizedModule.iso (Submonoid.powers g)
      (Algebra.linearMap S X)).restrictScalars R).symm
  set s := algebraMap S X f
  let φ : X →ₗ[R] X := (LinearMap.mulLeft S s).restrictScalars R
  -- `s` is a nonzerodivisor of `X`.
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers g) x
    change s * IsLocalization.mk' X a b = 0 at hx
    rw [show s = IsLocalization.mk' X f (1 : Submonoid.powers g) from
      (IsLocalization.mk'_one X f).symm, ← IsLocalization.mk'_mul, one_mul,
      IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := hx
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨g ^ (m + 1), m + 1, rfl⟩, ?_⟩
    have := hreg (g ^ m * a) (by rw [← hm]; ring)
    change g ^ (m + 1) * a = 0
    rw [pow_succ, show g ^ m * g * a = g₂ * (g₁ * (g ^ m * a)) by ring, this, mul_zero]
  -- `X ⧸ s` is flat.
  have hflat : Flat R (X ⧸ LinearMap.range φ) := by
    have : Flat R (LocalizedModule (Submonoid.powers g) (S ⧸ Ideal.span {f})) := by
      rw [flat_localizedModule_iff] at hC ⊢
      intro J y hy
      obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hC J y hy
      simp only at hn
      exact ⟨g ^ n, ⟨n, rfl⟩, by rw [mul_pow, mul_comm (g₁ ^ n), mul_smul, hn, smul_zero]⟩
    let ψ := (Ideal.span {f} : Submodule S S).toLocalizedQuotient' X (Submonoid.powers g)
      (Algebra.linearMap S X)
    let e₁ : LocalizedModule (Submonoid.powers g) (S ⧸ Ideal.span {f}) ≃ₗ[S]
        X ⧸ (Ideal.span {f} : Submodule S S).localized' X (Submonoid.powers g)
          (Algebra.linearMap S X) := IsLocalizedModule.iso (Submonoid.powers g) ψ
    have hloc : (Ideal.span {f} : Submodule S S).localized' X (Submonoid.powers g)
        (Algebra.linearMap S X) = Submodule.span X {s} := by
      rw [Submodule.localized'_span, Set.image_singleton]
      rfl
    have hrange : (Submodule.span X {s}).restrictScalars R = LinearMap.range φ := by
      ext x
      rw [Submodule.restrictScalars_mem, ← Ideal.span, Ideal.mem_span_singleton',
        LinearMap.mem_range]
      exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha, mul_comm]; rfl⟩,
        fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha, mul_comm]; rfl⟩⟩
    let e₂ : (X ⧸ Submodule.span X {s}) ≃ₗ[R] X ⧸ LinearMap.range φ :=
      (Submodule.Quotient.restrictScalarsEquiv _ _).symm.trans
        (Submodule.quotEquivOfEq _ _ hrange)
    exact Flat.of_linearEquiv (((e₁.restrictScalars R).trans
      ((Submodule.quotEquivOfEq _ _ hloc).restrictScalars R)).trans e₂).symm
  intro N _ _ y hy
  have hinj : Function.Injective (φ.rTensor N) := by
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact LinearMap.lTensor_injective_of_exact_of_flat _ (Submodule.mkQ_surjective _) φ hφ
      (LinearMap.exact_map_mkQ_range φ) N
  let ℓ := AlgebraTensorModule.rTensor R N (Algebra.linearMap S X)
  have : IsLocalizedModule (Submonoid.powers g) ℓ :=
    IsLocalizedModule.rTensor (A := S) _ (Algebra.linearMap S X)
  have hnat (z : S ⊗[R] N) : φ.rTensor N (ℓ z) = ℓ (f • z) := by
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => rw [map_add, map_add, hz, hw, smul_add, map_add]
    | tmul a n => simp [φ, ℓ, s, smul_tmul']
  have h0 : ℓ y = 0 := hinj (by rw [hnat, hy, map_zero, map_zero])
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g) (f := ℓ)).mp h0
  exact ⟨n, hn⟩

end Module

/-- **Flatness at a point is stable under base change.** Let `S' = R' ⊗[R] S` and let `Q` be a
prime of `S'` lying over the prime `Q ∩ S` of `S`. If `S` is flat over `R` at `Q ∩ S`, then `S'` is
flat over `R'` at `Q`. -/
theorem Module.Flat.localization_of_isPushout {R R' S S' : Type*} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] [Algebra R R'] [Algebra R S] [Algebra R' S'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']
    (Q : Ideal S') [Q.IsPrime]
    (h : Module.Flat R (Localization.AtPrime (Q.comap (algebraMap S S')))) :
    Module.Flat R' (Localization.AtPrime Q) := by
  set Q₁ := Q.comap (algebraMap S S')
  set M := Algebra.algebraMapSubmonoid S' Q₁.primeCompl
  have hle : M ≤ Q.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  let : Algebra (Localization M) (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ M Q.primeCompl hle
  have : IsScalarTower S' (Localization M) (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ M Q.primeCompl hle
  have : IsScalarTower R' (Localization M) (Localization.AtPrime Q) :=
    .of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply R' S' (Localization M), ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
  have : IsLocalization (Q.primeCompl.map (algebraMap S' (Localization M)))
      (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ M Q.primeCompl hle
  have : Module.Flat (Localization M) (Localization.AtPrime Q) :=
    IsLocalization.flat _ (Q.primeCompl.map (algebraMap S' (Localization M)))
  have : Algebra.IsPushout S (Localization.AtPrime Q₁) S' (Localization M) :=
    (Algebra.isPushout_of_isLocalization Q₁.primeCompl (Localization.AtPrime Q₁) S'
      (Localization M)).symm
  have : Algebra.IsPushout R S R' S' := Algebra.IsPushout.symm inferInstance
  have : IsScalarTower R (Localization.AtPrime Q₁) (Localization M) :=
    .of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q₁),
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S' (Localization M),
        IsScalarTower.algebraMap_apply R S S', ← IsScalarTower.algebraMap_apply S S']
  have : Algebra.IsPushout R (Localization.AtPrime Q₁) R' (Localization M) :=
    (Algebra.IsPushout.comp_iff R S R' S').mpr inferInstance
  have : Module.Flat R' (Localization M) :=
    Module.Flat.isBaseChange R R' (Localization.AtPrime Q₁) (Localization M)
      (Algebra.IsPushout.symm this).out
  exact Module.Flat.trans R' (Localization M) (Localization.AtPrime Q)

/-- Let `Z` be a closed subset of `Spec C` such that `C` is flat over `R` at every point of `Z`, and
`T` a submonoid of `C` containing every element lying in no prime of `Z`. Then the localization
`C_T` is flat over `R`. -/
theorem Module.Flat.localization_of_forall_mem_isClosed {R C : Type*} [CommRing R] [CommRing C]
    [Algebra R C] {Z : Set (PrimeSpectrum C)} (hZ : IsClosed Z)
    (hflat : ∀ q ∈ Z, Module.Flat R (Localization.AtPrime q.asIdeal)) (T : Submonoid C)
    (hT : ∀ c : C, (∀ q ∈ Z, c ∉ q.asIdeal) → c ∈ T) :
    Module.Flat R (Localization T) := by
  refine Module.Flat.iff_lTensor_injective'.2 fun J ↦ ?_
  rw [Module.lTensor_injective_iff_of_isLocalizedModule T (Algebra.linearMap C (Localization T))]
  intro y hy
  have hI : LinearMap.ker (LinearMap.toSpanSingleton C _ y) ⊔
      PrimeSpectrum.vanishingIdeal Z = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    have hmZ : (⟨m, hm.isPrime⟩ : PrimeSpectrum C) ∈ Z := by
      rw [← hZ.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact le_sup_right.trans hle
    have := hflat _ hmZ
    obtain ⟨t, ht, hty⟩ := (Module.lTensor_injective_iff_of_isLocalizedModule m.primeCompl
      (Algebra.linearMap C (Localization.AtPrime m)) J.subtype).1
      (Module.Flat.iff_lTensor_injective'.1 this J) y hy
    exact ht (le_sup_left.trans hle (LinearMap.mem_ker.2 hty))
  obtain ⟨t, ht, j, hj, htj⟩ := Submodule.mem_sup.1 (hI ▸ Submodule.mem_top (x := (1 : C)))
  refine ⟨t, hT t fun q hq htq ↦ q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_), ht⟩
  rw [← htj]
  exact add_mem htq ((PrimeSpectrum.mem_vanishingIdeal Z j).1 hj q hq)

/-- **Flatness at a point along an enlargement of the base.** Let `f : R → R'` be a map of
`R₀`-algebras and `Q` a prime of `R' ⊗[R₀] S₀`. If `R ⊗[R₀] S₀` is flat over `R` at the prime
below `Q`, then `R' ⊗[R₀] S₀` is flat over `R'` at `Q`. -/
theorem Module.Flat.localization_tensorProduct_map {R₀ R R' S₀ : Type*} [CommRing R₀]
    [CommRing R] [CommRing R'] [CommRing S₀] [Algebra R₀ R] [Algebra R₀ R'] [Algebra R₀ S₀]
    (f : R →ₐ[R₀] R') (Q : Ideal (R' ⊗[R₀] S₀)) [Q.IsPrime] (P : Ideal (R ⊗[R₀] S₀)) [P.IsPrime]
    (hPQ : Q.comap (Algebra.TensorProduct.map f (AlgHom.id R₀ S₀)).toRingHom = P)
    (h : Module.Flat R (Localization.AtPrime P)) :
    Module.Flat R' (Localization.AtPrime Q) := by
  subst hPQ
  let : Algebra R R' := f.toRingHom.toAlgebra
  have : IsScalarTower R₀ R R' := .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  let : Algebra (R ⊗[R₀] S₀) (R' ⊗[R₀] S₀) :=
    (Algebra.TensorProduct.map f (AlgHom.id R₀ S₀)).toRingHom.toAlgebra
  have : IsScalarTower R (R ⊗[R₀] S₀) (R' ⊗[R₀] S₀) := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have : Algebra.IsPushout R R' (R ⊗[R₀] S₀) (R' ⊗[R₀] S₀) :=
    Algebra.IsPushout.tensorProduct_tensorProduct R₀ S₀ R R' (by
      ext x
      simp [RingHom.algebraMap_toAlgebra])
  exact Module.Flat.localization_of_isPushout Q h

namespace PrimeSpectrum

/-- **Openness of the flat locus** (Stacks `00RC`). For a finite type algebra `S` over a
noetherian ring `R`, the set of primes `q` of `S` such that `S_q` is flat over `R` is open. -/
theorem isOpen_setOf_flat_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (Localization.AtPrime q.asIdeal)} := by
  rw [isOpen_iff_forall_mem_open]
  intro q (hq : Module.Flat R _)
  have hP : Module.Flat R (LocalizedModule q.asIdeal.primeCompl S) := Module.Flat.of_linearEquiv
    ((IsLocalizedModule.iso q.asIdeal.primeCompl
      (Algebra.linearMap S (Localization.AtPrime q.asIdeal))).restrictScalars R)
  obtain ⟨g, hg, hopen⟩ :=
    Module.Flat.exists_notMem_forall_flat_localizedModule (M := S) q.asIdeal hP
  refine ⟨basicOpen g, fun Q hQ ↦ ?_, isOpen_basicOpen, hg⟩
  have := hopen Q.asIdeal hQ
  exact Module.Flat.of_linearEquiv
    ((IsLocalizedModule.iso Q.asIdeal.primeCompl
      (Algebra.linearMap S (Localization.AtPrime Q.asIdeal))).restrictScalars R).symm

end PrimeSpectrum
