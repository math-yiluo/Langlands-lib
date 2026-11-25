/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Module.TransferInstance
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimesExactSequence
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated

/-!
# Associated primes under flat base change

Source: Stacks Project, Algebra, Lemma Tag 0312 (Bourbaki)
(blueprint: lem-weil-pbc-associated-primes-flat-base-change).
-/

@[expose] public section

universe r s m n

open scoped TensorProduct Pointwise

namespace RingTheory

private theorem associated_flat_tensor_finite
    {R : Type r} [CommRing R] [IsNoetherianRing R]
    (M : Type m) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type n) [AddCommGroup N] [Module R N] [Module.Flat R N]
    {p : Ideal R} (hp : p ∈ associatedPrimes R (M ⊗[R] N)) :
    p ∈ associatedPrimes R M := by
  let : p.IsPrime := hp.isPrime
  let A := Localization.AtPrime p
  let L := LocalizedModule.AtPrime p M
  let f : M →ₗ[R] L := LocalizedModule.mkLinearMap p.primeCompl M
  let g : M ⊗[R] N →ₗ[R] L ⊗[R] N :=
    TensorProduct.AlgebraTensorModule.rTensor R N f
  have hloc : IsLocalRing.maximalIdeal A ∈ associatedPrimes A (L ⊗[R] N) := by
    apply (open Module.associatedPrimes in
      mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule p.primeCompl g)
    simpa only [A, Localization.AtPrime.under_maximalIdeal] using hp
  have hL : IsLocalRing.maximalIdeal A ∈ associatedPrimes A L := by
    by_contra h
    obtain ⟨x, hx, hreg⟩ := exists_mem_maximalIdeal_smul_injective A L h
    have hinj : Function.Injective (fun z : L ⊗[R] N ↦ x • z) := by
      change Function.Injective ((Algebra.lsmul R R L x).rTensor N)
      exact Module.Flat.rTensor_preserves_injective_linearMap _ hreg
    obtain ⟨hprime, w, hw⟩ := isAssociatedPrime_iff.mp hloc
    have hw0 : w ≠ 0 := by
      intro h
      exact hprime.ne_top (by simpa [h, Submodule.colon_singleton_zero] using hw)
    have hxw : x • w = 0 := by
      have := hw ▸ hx
      simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using this
    exact hw0 (hinj (by simpa only [smul_zero] using hxw))
  have hdesc := open Module.associatedPrimes in
    comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      p.primeCompl f (IsLocalRing.maximalIdeal A) hL
      (Ideal.fg_of_isNoetherianRing _)
  simpa only [A, Localization.AtPrime.under_maximalIdeal] using hdesc

private theorem associated_flat_tensor
    {R : Type r} [CommRing R] [IsNoetherianRing R]
    (M : Type m) [AddCommGroup M] [Module R M]
    (N : Type n) [AddCommGroup N] [Module R N] [Module.Flat R N]
    {p : Ideal R} (hp : p ∈ associatedPrimes R (M ⊗[R] N)) :
    p ∈ associatedPrimes R M := by
  -- An annihilator witness comes from a finite submodule; flatness preserves it.
  obtain ⟨hp, z, hz⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨L, hL, y, hy⟩ := Submodule.exists_fg_le_eq_rTensor_subtype z
  let : Module.Finite R L := Module.Finite.of_fg hL
  let f := L.subtype.rTensor N
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap L.subtype Subtype.val_injective
  have hpL : p ∈ associatedPrimes R (L ⊗[R] N) := by
    apply isAssociatedPrime_iff.mpr
    refine ⟨hp, y, ?_⟩
    rw [hz, hy]
    ext a
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change a • f y = 0 ↔ a • y = 0
    rw [← f.map_smul, ← f.map_zero, hf.eq_iff]
  exact (associated_flat_tensor_finite L N hpL).map_of_injective L.subtype
    Subtype.val_injective

/-- The contraction claim in Stacks 0312. We restrict the annihilator witness to R,
commute tensor factors, and apply `associated_flat_tensor`. The latter localizes only
at p over R: no localization of N over S or comparison of two localizations is needed.
Source: Stacks Project, Algebra, Lemma Tag 0312, third proof paragraph;
the equivalent argument with localization over R is written here by U1. -/
private theorem annihilatorAssociatedPrimes_tensor_contraction
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type m) [AddCommGroup M] [Module R M]
    (N : Type n) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [IsNoetherianRing R] [Module.Flat R N]
    {q : Ideal S} (hq : q ∈ annihilatorAssociatedPrimes S (N ⊗[R] M)) :
    q.comap (algebraMap R S) ∈ annihilatorAssociatedPrimes R M := by
  obtain ⟨hqprime, z, hz⟩ := hq
  have hqR : q.comap (algebraMap R S) ∈ associatedPrimes R (N ⊗[R] M) := by
    apply isAssociatedPrime_iff.mpr
    refine ⟨hqprime.under R, z, ?_⟩
    ext a
    simp only [Ideal.mem_comap, hz, Submodule.mem_colon_singleton, Submodule.mem_bot,
      algebraMap_smul]
  have hqR' := hqR.map_of_injective (TensorProduct.comm R N M).toLinearMap
    (TensorProduct.comm R N M).injective
  exact isAssociatedPrime_iff.mp (associated_flat_tensor M N hqR')


private theorem associated_of_injective
    {S : Type s} [CommRing S] {A : Type*} {B : Type*}
    [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    (f : A →ₗ[S] B) (hf : Function.Injective f) :
    annihilatorAssociatedPrimes S A ⊆ annihilatorAssociatedPrimes S B := by
  rintro q ⟨hq, z, rfl⟩
  refine ⟨hq, f z, ?_⟩
  ext a
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  rw [← f.map_smul, ← f.map_zero, hf.eq_iff]

private theorem smul_top_restrict
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] [Algebra R S]
    {N : Type n} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (p : Ideal R) :
    (((p : Set R) • (⊤ : Submodule S N)).restrictScalars R) =
      p • (⊤ : Submodule R N) := by
  ext x
  constructor
  · intro hx
    change x ∈ (p : Set R) • (⊤ : Submodule S N) at hx
    induction x, hx using Submodule.set_smul_inductionOn with
    | smul₀ hr hn => exact Submodule.smul_mem_smul hr Submodule.mem_top
    | smul₁ a hx ih =>
      refine Submodule.smul_induction_on ih ?_ ?_
      · intro b hb y hy
        rw [smul_comm a b y]
        exact Submodule.smul_mem_smul hb Submodule.mem_top
      · intro y z hy hz
        simpa only [smul_add] using Submodule.add_mem _ hy hz
    | add hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
    | zero => exact Submodule.zero_mem _
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y hy
      exact Submodule.mem_set_smul_of_mem_mem ha Submodule.mem_top
    · intro y z hy hz
      exact Submodule.add_mem _ hy hz

private noncomputable def quotientTensorEquiv
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] [Algebra R S]
    {N : Type n} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (p : Ideal R) :
    (N ⧸ ((p : Set R) • (⊤ : Submodule S N))) ≃ₗ[S] N ⊗[R] (R ⧸ p) := by
  let e := (Submodule.Quotient.restrictScalarsEquiv R
    ((p : Set R) • (⊤ : Submodule S N))).symm.trans
      ((Submodule.quotEquivOfEq _ _ (smul_top_restrict (N := N) p)).trans
        (TensorProduct.tensorQuotEquivQuotSMul N p).symm)
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (a • x) ⊗ₜ[R] (1 : R ⧸ p) = a • (x ⊗ₜ[R] (1 : R ⧸ p))
    exact TensorProduct.smul_tmul' a x 1

private theorem associated_quotient_subset_tensor
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type m} [AddCommGroup M] [Module R M]
    {N : Type n} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R N]
    {p : Ideal R} (hp : p ∈ annihilatorAssociatedPrimes R M) :
    annihilatorAssociatedPrimes S (N ⧸ ((p : Set R) • (⊤ : Submodule S N))) ⊆
      annihilatorAssociatedPrimes S (N ⊗[R] M) := by
  obtain ⟨_, z, hz⟩ := hp
  let f := LinearMap.toSpanSingleton R M z
  have hker : p = LinearMap.ker f := by
    rw [hz]
    ext a
    simp [f, Submodule.mem_colon_singleton, LinearMap.toSpanSingleton_apply]
  let j : (R ⧸ p) →ₗ[R] M := p.liftQ f hker.le
  have hj : Function.Injective j := by
    apply LinearMap.ker_eq_bot.mp
    exact p.ker_liftQ_eq_bot' f hker
  let t : N ⊗[R] (R ⧸ p) →ₗ[S] N ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.lTensor S N j
  have ht : Function.Injective t :=
    Module.Flat.lTensor_preserves_injective_linearMap j hj
  exact associated_of_injective (t.comp (quotientTensorEquiv (N := N) p).toLinearMap)
    (ht.comp (quotientTensorEquiv (N := N) p).injective)

private theorem associated_tensor_prime_quotient_finite
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type m} [AddCommGroup M] [Module R M]
    {N : Type n} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [IsNoetherianRing R] [Module.Flat R N] [Module.Finite R M]
    {q : Ideal S} (hq : q ∈ annihilatorAssociatedPrimes S (N ⊗[R] M)) :
    ∃ p : Ideal R, p.IsPrime ∧
      q ∈ annihilatorAssociatedPrimes S (N ⊗[R] (R ⧸ p)) := by
  -- This induction principle is the prime filtration of Stacks 00L0.
  induction ‹Module.Finite R M› using
    IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton L =>
    obtain ⟨hq, z, hz⟩ := hq
    have hz0 : z = 0 := Subsingleton.elim _ _
    exact (hq.ne_top (by simpa [hz0, Submodule.colon_singleton_zero] using hz)).elim
  | quotient L p e =>
    let f : N ⊗[R] L →ₗ[S] N ⊗[R] (R ⧸ p.asIdeal) :=
      TensorProduct.AlgebraTensorModule.lTensor S N e.toLinearMap
    exact ⟨p.asIdeal, p.isPrime, associated_of_injective f
      (Module.Flat.lTensor_preserves_injective_linearMap e.toLinearMap e.injective) hq⟩
  | exact L₁ L₂ L₃ f g hf hg hfg h₁ h₃ =>
    let f' := TensorProduct.AlgebraTensorModule.lTensor S N f
    let g' := TensorProduct.AlgebraTensorModule.lTensor S N g
    have hf' : Function.Injective f' :=
      Module.Flat.lTensor_preserves_injective_linearMap f hf
    have hg' : Function.Surjective g' := LinearMap.lTensor_surjective N hg
    have hfg' : Function.Exact f' g' := Module.Flat.lTensor_exact N hfg
    have h := (annihilatorAssociatedPrimes_of_shortExact f' g' hf' hfg' hg').2.2 hq
    rcases h with h | h
    · exact h₁ h
    · exact h₃ h

private theorem associated_tensor_prime_quotient
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type m} [AddCommGroup M] [Module R M]
    {N : Type n} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [IsNoetherianRing R] [Module.Flat R N]
    {q : Ideal S} (hq : q ∈ annihilatorAssociatedPrimes S (N ⊗[R] M)) :
    ∃ p : Ideal R, p.IsPrime ∧
      q ∈ annihilatorAssociatedPrimes S (N ⊗[R] (R ⧸ p)) := by
  obtain ⟨hq, z, hz⟩ := hq
  obtain ⟨L, hL, y, hy⟩ := Submodule.exists_fg_le_eq_rTensor_subtype
    ((TensorProduct.comm R N M) z)
  let : Module.Finite R L := Module.Finite.of_fg hL
  let f := TensorProduct.AlgebraTensorModule.lTensor S N L.subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap L.subtype Subtype.val_injective
  have hy' : z = f ((TensorProduct.comm R L N) y) := by
    apply (TensorProduct.comm R N M).injective
    change (TensorProduct.comm R N M) z = (TensorProduct.comm R N M)
      (L.subtype.lTensor N ((TensorProduct.comm R L N) y))
    rw [← LinearMap.rTensor_comm]
    simpa only [TensorProduct.comm_comm] using hy
  have hqL : q ∈ annihilatorAssociatedPrimes S (N ⊗[R] L) := by
    refine ⟨hq, (TensorProduct.comm R L N) y, ?_⟩
    rw [hz, hy']
    ext a
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [← f.map_smul, ← f.map_zero, hf.eq_iff]
  exact associated_tensor_prime_quotient_finite hqL

private theorem associated_quotient_eq
    {R : Type r} [CommRing R] {p q : Ideal R} (hp : p.IsPrime)
    (hq : q ∈ annihilatorAssociatedPrimes R (R ⧸ p)) : q = p := by
  obtain ⟨hq, z, hz⟩ := hq
  have hz0 : z ≠ 0 := by
    intro h
    exact hq.ne_top (by simpa [h, Submodule.colon_singleton_zero] using hz)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hx : x ∉ p := by
    intro hx
    exact hz0 ((Ideal.Quotient.eq_zero_iff_mem).mpr hx)
  rw [hz]
  ext a
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h ↦ (hp.mem_or_mem h).resolve_right hx, fun h ↦ p.mul_mem_right x h⟩

/-- Bourbaki's associated-prime formula for a flat module.
Source: Stacks Project, Algebra, Lemma Tag 0312
(blueprint: lem-weil-pbc-associated-primes-flat-base-change).
The `S`-action on `M ⊗[R] N` is transported along tensor commutation from the action on
`N ⊗[R] M`: thus `s • (m ⊗ n) = m ⊗ (s • n)`. The submodule `pN` is the
pointwise set scalar product `(p : Set R) • ⊤` in `Submodule S N`.

Proof, following the node's nine steps:
1. For `p = Ann(z)`, inject `R/p` into `M` by `r ↦ r z`. Flatness
   (def-weil-pbc-flat-ring-map, lem-weil-pbc-flat-tensor-exact) preserves this injection.
   Identify `(R/p) ⊗ N` with `N/pN` (lem-weil-pbc-tensor-over-quotient-ring).
   An injection preserves associated primes (lem-weil-pbc-associated-primes-exact-sequence).
2. Associated primes of a directed union of submodules are the union of their associated
   primes: each witnessing element already lies in one submodule, with the same annihilator.
3. Write `M` as the directed union of its finite submodules (def-weil-finitely-generated-module).
   Flatness embeds their tensors into `M ⊗ N`, with union the whole tensor. Step 2 reduces
   equality over Noetherian `R` (def-weil-pbc-noetherian-ring) to finite `M`.
4. For `q` associated to `M ⊗ N`, localize at `q` to obtain a nonzero element annihilated by
   `q S_q` (lem-weil-pbc-associated-prime-localize-at-prime). Set `p` to its contraction.
5. Identify `(M ⊗ N)_q` with `M_p ⊗ N_q`, compatibly with `R`-scalars, using
   lem-weil-pbc-localization-tensor-over-base and
   lem-weil-pbc-localization-module-over-localization (and the module-localization definition).
6. `N_q` remains flat over `R`: localize the injections induced by tensoring with `N`, using
   lem-weil-pbc-localization-module-exact and the naturality of the tensor identification.
7. If `p R_p` were not associated to `M_p`, choose a nonzerodivisor in it using
   lem-weil-pbc-nonzerodivisor-if-maximal-not-associated. Noetherian localization uses
   lem-weil-pbc-localization-noetherian. Flatness makes its action injective on `M_p ⊗ N_q`,
   contradicting Step 4. Descend association by
   lem-weil-pbc-noetherian-associated-prime-from-localization. Thus `p` is associated to `M`.
8. Choose a prime filtration of finite `M` (lem-weil-pbc-noetherian-module-prime-filtration).
   Tensor it with `N`, using flat tensor exactness and lem-weil-pbc-tensor-right-exact.
   Its quotients are `N/p_iN`. The exact-sequence associated-prime inclusion puts each
   associated `q` in the associated primes of one such quotient.
9. Step 7 applied to `R/p_i` shows that the contraction of this `q` is associated to `R/p_i`.
   Primality gives `Ass(R/p_i) = {p_i}`. Hence that `p_i` is the contraction `p` already
   associated to `M`, proving the reverse inclusion. All maps are `S`-linear. -/
theorem annihilatorAssociatedPrimes_flat_base_change
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type m) [AddCommGroup M] [Module R M]
    (N : Type n) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R N] :
    letI : Module S (M ⊗[R] N) := (TensorProduct.comm R M N).toAddEquiv.module S
    let rhs : Set (Ideal S) := ⋃ p ∈ annihilatorAssociatedPrimes R M,
      annihilatorAssociatedPrimes S (N ⧸ ((p : Set R) • (⊤ : Submodule S N)))
    rhs ⊆ annihilatorAssociatedPrimes S (M ⊗[R] N) ∧
      (IsNoetherianRing R → annihilatorAssociatedPrimes S (M ⊗[R] N) = rhs) := by
  -- The contraction proof uses localization over R instead of the docstring
  -- plan's localization over S. The filtration and both inclusions are unchanged.
  let : Module S (M ⊗[R] N) := (TensorProduct.comm R M N).toAddEquiv.module S
  dsimp only
  let e : (M ⊗[R] N) ≃ₗ[S] (N ⊗[R] M) :=
    (TensorProduct.comm R M N).toAddEquiv.linearEquiv S
  have hsubset : (⋃ p ∈ annihilatorAssociatedPrimes R M,
      annihilatorAssociatedPrimes S (N ⧸ ((p : Set R) • (⊤ : Submodule S N)))) ⊆
      annihilatorAssociatedPrimes S (M ⊗[R] N) := by
    intro q hq
    obtain ⟨p, hp, hq⟩ := Set.mem_iUnion₂.mp hq
    exact associated_of_injective e.symm.toLinearMap e.symm.injective
      (associated_quotient_subset_tensor hp hq)
  refine ⟨hsubset, ?_⟩
  intro hR
  let : IsNoetherianRing R := hR
  apply Set.Subset.antisymm ?_ hsubset
  intro q hq
  have hqt := associated_of_injective e.toLinearMap e.injective hq
  have hcon := annihilatorAssociatedPrimes_tensor_contraction M N hqt
  obtain ⟨p, hp, hqp⟩ := associated_tensor_prime_quotient hqt
  have hconp := annihilatorAssociatedPrimes_tensor_contraction (R ⧸ p) N hqp
  have heq : q.comap (algebraMap R S) = p := associated_quotient_eq hp hconp
  apply Set.mem_iUnion₂.mpr
  refine ⟨p, heq ▸ hcon, ?_⟩
  exact associated_of_injective (quotientTensorEquiv (N := N) p).symm.toLinearMap
    (quotientTensorEquiv (N := N) p).symm.injective hqp

end RingTheory
