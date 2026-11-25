/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.RingTheory.CoverModuleExact
import WeilConjectures.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Exactness of the formal glueing complex

Source: Stacks Project, More on Algebra, Lemma 05EK and equation `glueing-complex`
(blueprint: lem-weil-pbc-formal-glueing-complex-exact).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace RingTheory

private theorem mem_primaryComponent_iff_localizations_zero
    {R : Type u} [CommRing R] {P : Type w} [AddCommGroup P] [Module R P]
    (t : ℕ) (f : Fin t → R) (x : P) :
    x ∈ Ideal.primaryComponent P (Ideal.span (Set.range f)) ↔
      ∀ i, LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P x = 0 := by
  let I := Ideal.span (Set.range f)
  let J := (Submodule.span R ({x} : Set P)).annihilator
  constructor
  · intro hx i
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem P I x).mp hx
    apply (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P)).mpr
    refine ⟨⟨(f i) ^ n, ⟨n, rfl⟩⟩, ?_⟩
    have hn' := (Submodule.mem_torsionBySet_iff (↑(I ^ n) : Set R) x).mp hn
    have hfi : f i ∈ I := Ideal.subset_span ⟨i, rfl⟩
    exact hn' ⟨(f i) ^ n, Ideal.pow_mem_pow hfi n⟩
  · intro hx
    have hIJ : I ≤ J.radical := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P)).mp (hx i)
      obtain ⟨n, hn⟩ := a.2
      change ∃ n : ℕ, (f i) ^ n ∈ J
      refine ⟨n, (Submodule.mem_annihilator_span_singleton x _).mpr ?_⟩
      simpa only [← hn, Submonoid.smul_def] using ha
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ
      (Submodule.fg_span (Set.finite_range f))
    apply (Ideal.primaryComponent_mem P I x).mpr
    refine ⟨n, (Submodule.mem_torsionBySet_iff (↑(I ^ n) : Set R) x).mpr ?_⟩
    intro a
    exact (Submodule.mem_annihilator_span_singleton x (a : R)).mp (hn a.2)

private theorem formalGlueing_normalize
    {R : Type u} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]
    {P : Type v} [AddCommGroup P] [Module R P]
    (η : M →ₗ[R] P) (t : ℕ) (f : Fin t → R)
    (y : P) (s : ∀ i, LocalizedModule.Away (f i) M)
    (hb : ∀ i, LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P y =
      IsLocalizedModule.map (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P) η (s i))
    (hs : ∀ i j,
      IsLocalizedModule.lift (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j)) M)
        (localizationAway_map_units_of_dvd (M := M) _ _ (dvd_mul_right _ _)) (s i) =
      IsLocalizedModule.lift (Submonoid.powers (f j))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j)) M)
        (localizationAway_map_units_of_dvd (M := M) _ _ (dvd_mul_left _ _)) (s j)) :
    ∃ n : ℕ, ∃ x : Fin t → M,
      (∀ i, (f i) ^ n • s i =
        LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M (x i)) ∧
      (∀ i j, (f j) ^ n • x i = (f i) ^ n • x j) ∧
      (∀ i, η (x i) = (f i) ^ n • y) := by
  classical
  let loc (a : R) := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  let locP (a : R) := LocalizedModule.mkLinearMap (Submonoid.powers a) P
  let ρ := fun (a h : R) (ha : a ∣ h) ↦
    IsLocalizedModule.lift (Submonoid.powers a) (loc a) (loc h)
      (localizationAway_map_units_of_dvd (M := M) a h ha)
  have hrep (i : Fin t) : ∃ e : ℕ, ∃ m : M, (f i) ^ e • s i = loc (f i) m := by
    obtain ⟨⟨m, a⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (loc (f i)) (s i)
    obtain ⟨e, he⟩ := a.2
    exact ⟨e, m, by simpa only [← he, Submonoid.smul_def] using ha⟩
  choose e x hx using hrep
  let N := Finset.univ.sup e
  let m (i : Fin t) := (f i) ^ (N - e i) • x i
  have hm (i : Fin t) : (f i) ^ N • s i = loc (f i) (m i) := by
    dsimp only [m]
    rw [map_smul, ← hx, smul_smul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ i))]
  have heq (i j : Fin t) : ∃ k : ℕ,
      (f i * f j) ^ k • ((f j) ^ N • m i) =
        (f i * f j) ^ k • ((f i) ^ N • m j) := by
    have hloc : loc (f i * f j) ((f j) ^ N • m i) =
        loc (f i * f j) ((f i) ^ N • m j) := by
      rw [(loc (f i * f j)).map_smul ((f j) ^ N) (m i),
        (loc (f i * f j)).map_smul ((f i) ^ N) (m j)]
      rw [← IsLocalizedModule.lift_apply (Submonoid.powers (f i)) (loc (f i))
        (loc (f i * f j)) (localizationAway_map_units_of_dvd (M := M) _ _
          (dvd_mul_right (f i) (f j))) (m i)]
      rw [← IsLocalizedModule.lift_apply (Submonoid.powers (f j)) (loc (f j))
        (loc (f i * f j)) (localizationAway_map_units_of_dvd (M := M) _ _
          (dvd_mul_left (f j) (f i))) (m j)]
      change (f j) ^ N • ρ (f i) (f i * f j) (dvd_mul_right _ _) (loc (f i) (m i)) =
        (f i) ^ N • ρ (f j) (f i * f j) (dvd_mul_left _ _) (loc (f j) (m j))
      rw [← hm, ← hm, map_smul, map_smul, hs, smul_comm]
    obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (f i * f j))
      (loc (f i * f j))).mp hloc
    obtain ⟨k, hk⟩ := a.2
    exact ⟨k, by simpa only [← hk, Submonoid.smul_def] using ha⟩
  have heqP (i : Fin t) : ∃ c : ℕ,
      (f i) ^ c • ((f i) ^ N • y) = (f i) ^ c • η (m i) := by
    have hloc : locP (f i) ((f i) ^ N • y) = locP (f i) (η (m i)) := by
      rw [map_smul, hb]
      rw [← IsLocalizedModule.map_apply (Submonoid.powers (f i)) (loc (f i))
        (locP (f i)) η (m i), ← hm, map_smul]
    obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (f i))
      (locP (f i))).mp hloc
    obtain ⟨c, hc⟩ := a.2
    exact ⟨c, by simpa only [← hc, Submonoid.smul_def] using ha⟩
  choose k hk using heq
  choose c hc using heqP
  let K := (Finset.univ.sup fun p : Fin t × Fin t ↦ k p.1 p.2) ⊔ Finset.univ.sup c
  have hK (i j : Fin t) :
      (f i * f j) ^ K • ((f j) ^ N • m i) =
        (f i * f j) ^ K • ((f i) ^ N • m j) := by
    have hle : k i j ≤ K := le_sup_of_le_left (Finset.le_sup
      (f := fun p : Fin t × Fin t ↦ k p.1 p.2) (Finset.mem_univ (i, j)))
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, mul_smul, hk]
  have hKP (i : Fin t) : (f i) ^ K • ((f i) ^ N • y) = (f i) ^ K • η (m i) := by
    have hle : c i ≤ K := le_sup_of_le_right (Finset.le_sup (Finset.mem_univ i))
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, mul_smul, hc]
  refine ⟨K + N, fun i ↦ (f i) ^ K • m i, ?_, ?_, ?_⟩
  · intro i
    change (f i) ^ (K + N) • s i = loc (f i) ((f i) ^ K • m i)
    rw [pow_add, mul_smul, hm, (loc (f i)).map_smul ((f i) ^ K) (m i)]
  · intro i j
    have h := hK i j
    simp only [smul_smul] at h ⊢
    calc
      _ = ((f i * f j) ^ K * (f j) ^ N) • m i := by congr 1; rw [mul_pow, pow_add]; ring
      _ = ((f i * f j) ^ K * (f i) ^ N) • m j := h
      _ = _ := by congr 1; rw [mul_pow, pow_add]; ring
  · intro i
    rw [map_smul, ← hKP, pow_add, mul_smul]

/-- A compatible family of multiples by powers of the generators is a boundary if
it becomes a boundary after the specified flat base change.

Source: Stacks Project, More on Algebra, Lemma 05EK, second computational proof,
the argument using the class in `H_1(M, (f_1^n, ..., f_t^n))`.
(blueprint: lem-weil-pbc-formal-glueing-complex-exact).

Proof: let `δ : M → M^t` send `m` to `(f_i^n m)_i`, and take the class `ξ`
of `x` in `Q = M^t / range δ`. Compatibility gives `f_k^n x = δ(x_k)`,
so every `f_k^n` annihilates `ξ`. The finitely generated ideal `I = (f_i)`
lies in the radical of the annihilator of `ξ`, hence a power of `I` kills `ξ`.
The finite product tensor comparison identifies `1 ⊗ x` with `δ.lTensor S y`
by the boundary hypothesis. Applying the tensor extension of the quotient map
gives `1 ⊗ ξ = 0`. Injectivity of the torsion-submodule base-change map
(05EC(1)) now gives `ξ = 0`, hence `x = δ(m)` for some `m`.
This uses the ambient cokernel instead of the Koszul subquotient of the source;
only the class of the compatible family must be torsion. For an empty family,
the ambient product is zero and the same argument applies. -/
private theorem formalGlueing_powerFamily_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (hflat : RingHom.Flat (algebraMap R S))
    (t : ℕ) (f : Fin t → R)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M]
    (n : ℕ) (x : Fin t → M) (y : S ⊗[R] M)
    (hcompat : ∀ i j, (f j) ^ n • x i = (f i) ^ n • x j)
    (hboundary : ∀ i, TensorProduct.mk R S M 1 (x i) = (f i) ^ n • y) :
    ∃ m : M, ∀ i, x i = (f i) ^ n • m := by
  classical
  let I := Ideal.span (Set.range f)
  let δ : M →ₗ[R] (Fin t → M) := LinearMap.pi fun i ↦
    (f i) ^ n • (LinearMap.id : M →ₗ[R] M)
  let Q := (Fin t → M) ⧸ LinearMap.range δ
  let π : (Fin t → M) →ₗ[R] Q := (LinearMap.range δ).mkQ
  let ξ : Q := π x
  let J := (Submodule.span R ({ξ} : Set Q)).annihilator
  have hkill (k : Fin t) : (f k) ^ n • ξ = 0 := by
    change (f k) ^ n • π x = 0
    rw [← map_smul]
    have heq : (f k) ^ n • x = δ (x k) := by
      funext i
      exact hcompat i k
    rw [heq]
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range δ)).mpr ⟨x k, rfl⟩
  have hIJ : I ≤ J.radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ∃ e : ℕ, (f i) ^ e ∈ J
    exact ⟨n, (Submodule.mem_annihilator_span_singleton ξ _).mpr (hkill i)⟩
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ
    (Submodule.fg_span (Set.finite_range f))
  have hξ : ξ ∈ Ideal.primaryComponent Q I := by
    apply (Ideal.primaryComponent_mem Q I ξ).mpr
    refine ⟨e, (Submodule.mem_torsionBySet_iff (↑(I ^ e) : Set R) ξ).mpr ?_⟩
    intro a
    exact (Submodule.mem_annihilator_span_singleton ξ (a : R)).mp (he a.2)
  let E := TensorProduct.piRight R R S (fun _ : Fin t ↦ M)
  have hδ (z : S ⊗[R] M) (i : Fin t) : E (δ.lTensor S z) i = (f i) ^ n • z := by
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
      simp [E, δ, TensorProduct.piRightHom_tmul, TensorProduct.tmul_smul]
    | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂, smul_add]
  have hboundary' : (1 : S) ⊗ₜ[R] x = δ.lTensor S y := by
    apply E.injective
    funext i
    rw [hδ]
    exact hboundary i
  have hπδ : π.comp δ = 0 := by
    ext m
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range δ)).mpr ⟨m, rfl⟩
  have hzero : (1 : S) ⊗ₜ[R] ξ = 0 := by
    change (1 : S) ⊗ₜ[R] π x = 0
    rw [← LinearMap.lTensor_tmul, hboundary', ← LinearMap.lTensor_comp_apply,
      hπδ, LinearMap.lTensor_zero, LinearMap.zero_apply]
  have hinj := (Ideal.primaryComponent_baseChange_bijective I
    (Submodule.fg_span (Set.finite_range f)) hflat hquot Q).1
  have hclass : (⟨ξ, hξ⟩ : Ideal.primaryComponent Q I) = 0 := by
    apply hinj
    apply Subtype.ext
    change (1 : S) ⊗ₜ[R] ξ = (1 : S) ⊗ₜ[R] (0 : Q)
    simpa only [TensorProduct.tmul_zero] using hzero
  have hξzero : ξ = 0 := congrArg Subtype.val hclass
  obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range δ)).mp hξzero
  exact ⟨m, fun i ↦ (congrFun hm i).symm⟩


/-- The formal glueing complex is exact for a flat map inducing an isomorphism modulo
`I = (f₁, …, fₜ)`. Scalar extension is written `S ⊗[R] M`, as in the recorded dependency
`def-weil-module-base-change`; tensor commutativity identifies it with `M ⊗[R] S`.
The map `η` is `m ↦ 1 ⊗ m`. Its localized map renders `mᵢ ⊗ 1` in `(M ⊗ S)_fᵢ`.
The canonical overlap maps `ρ` are the universal lifts of `m ↦ m/1`.
Source: Stacks Project, More on Algebra, Lemma 05EK and equation `glueing-complex`
(blueprint: lem-weil-pbc-formal-glueing-complex-exact).

Proof (following the second computational proof of 05EK):
1. Vanishing in all localizations is equivalent to ideal-power torsion: individual
   annihilating powers place I in the radical of the element's annihilator, and
   finite generation gives a power of I contained in that annihilator.
2. The localized map of eta sends m/1 to eta(m)/1. The universal overlap lifts
   also send m/1 to m/1, so beta(alpha(m)) = 0.
3. If alpha(m) = 0, then m is I-power torsion and eta(m) = 0. Injectivity of
   `Ideal.primaryComponent_baseChange_bijective` gives m = 0.
4. For a kernel element (y, (s_i)), clear denominators and the finitely many
   localized equalities. Obtain a common n and x_i in M satisfying
   f_i^n s_i = x_i/1, f_j^n x_i = f_i^n x_j, and eta(x_i) = f_i^n y.
5. Let delta(m) = (f_i^n m)_i, Q = M^t/range(delta), and xi be the class of x.
   Compatibility gives f_k^n x = delta(x_k), hence xi is I-power torsion.
   `TensorProduct.piRight` identifies 1 tensor x with delta.lTensor(S)(y).
   Applying the tensor extension of the quotient map gives 1 tensor xi = 0.
   Torsion comparison injectivity applied to Q gives xi = 0, so x_i = f_i^n m.
6. Scalar multiplication by f_i^n is injective in M localized at f_i, giving
   m/1 = s_i. The remainder y - eta(m) is I-power torsion. Surjectivity of
   the torsion comparison lifts it to a torsion element z of M, whose
   localizations vanish. Thus the kernel element is alpha(m + z).
The proof uses only the torsion class in the ambient cokernel, without forming
Koszul homology. Empty families and exponent zero are included throughout. -/
theorem formalGlueingComplexExact {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (hflat : φ.Flat)
    (t : ℕ) (f : Fin t → R)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M] :
    letI : Algebra R S := φ.toAlgebra
    let η : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
    let ρ := fun (a h : R) (ha : a ∣ h) ↦
      IsLocalizedModule.lift (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
        (localizationAway_map_units_of_dvd (M := M) a h ha)
    let α : M → (S ⊗[R] M) × (∀ i : Fin t, LocalizedModule.Away (f i) M) :=
      fun m ↦ (η m, fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m)
    let β : (S ⊗[R] M) × (∀ i : Fin t, LocalizedModule.Away (f i) M) →
        (∀ i : Fin t, LocalizedModule.Away (f i) (S ⊗[R] M)) ×
          (∀ i j : Fin t, LocalizedModule.Away (f i * f j) M) :=
      fun p ↦
        (fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] M) p.1 -
          IsLocalizedModule.map (Submonoid.powers (f i))
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] M)) η (p.2 i),
         fun i j ↦ ρ (f i) (f i * f j) (dvd_mul_right (f i) (f j)) (p.2 i) -
          ρ (f j) (f i * f j) (dvd_mul_left (f j) (f i)) (p.2 j))
    Function.Injective α ∧ Function.Exact α β := by
  classical
  let : Algebra R S := φ.toAlgebra
  let η : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
  let loc (a : R) := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  let locS (a : R) := LocalizedModule.mkLinearMap (Submonoid.powers a) (S ⊗[R] M)
  let I := Ideal.span (Set.range f)
  have htors := Ideal.primaryComponent_baseChange_bijective I
    (Submodule.fg_span (Set.finite_range f)) hflat hquot M
  dsimp only
  constructor
  · intro m₁ m₂ heq
    have hη : η (m₁ - m₂) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Prod.fst heq
    have hloc : ∀ i, loc (f i) (m₁ - m₂) = 0 := by
      intro i
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun p ↦ p.2 i) heq
    have hmem := (mem_primaryComponent_iff_localizations_zero t f (m₁ - m₂)).mpr hloc
    have hz : (⟨m₁ - m₂, hmem⟩ : Ideal.primaryComponent M I) = 0 := by
      apply htors.1
      apply Subtype.ext
      change η (m₁ - m₂) = η 0
      rw [map_zero]
      exact hη
    exact sub_eq_zero.mp (congrArg Subtype.val hz)
  · intro p
    constructor
    · intro hp
      have hb : ∀ i, locS (f i) p.1 =
          IsLocalizedModule.map (Submonoid.powers (f i)) (loc (f i)) (locS (f i)) η
            (p.2 i) := by
        intro i
        exact sub_eq_zero.mp (congrArg (fun q ↦ q.1 i) hp)
      have hs : ∀ i j,
          IsLocalizedModule.lift (Submonoid.powers (f i)) (loc (f i)) (loc (f i * f j))
            (localizationAway_map_units_of_dvd (M := M) _ _ (dvd_mul_right _ _)) (p.2 i) =
          IsLocalizedModule.lift (Submonoid.powers (f j)) (loc (f j)) (loc (f i * f j))
            (localizationAway_map_units_of_dvd (M := M) _ _ (dvd_mul_left _ _)) (p.2 j) := by
        intro i j
        exact sub_eq_zero.mp (congrArg (fun q ↦ q.2 i j) hp)
      obtain ⟨n, x, hx, hcompat, hη⟩ := formalGlueing_normalize η t f p.1 p.2 hb hs
      obtain ⟨m, hm⟩ := formalGlueing_powerFamily_descent hflat t f hquot M n x p.1
        hcompat hη
      have hmloc : ∀ i, loc (f i) m = p.2 i := by
        intro i
        apply IsLocalizedModule.smul_injective (loc (f i))
          (⟨(f i) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (f i))
        change (f i) ^ n • loc (f i) m = (f i) ^ n • p.2 i
        rw [hx, hm, map_smul]
      have hrem : p.1 - η m ∈ Ideal.primaryComponent (S ⊗[R] M) I := by
        apply (mem_primaryComponent_iff_localizations_zero t f _).mpr
        intro i
        apply (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i)) (locS (f i))).mpr
        refine ⟨⟨(f i) ^ n, ⟨n, rfl⟩⟩, ?_⟩
        change (f i) ^ n • (p.1 - η m) = 0
        rw [smul_sub, sub_eq_zero, ← hη, hm, map_smul]
      obtain ⟨z, hz⟩ := htors.2 ⟨p.1 - η m, hrem⟩
      have hzη : η (z : M) = p.1 - η m := congrArg Subtype.val hz
      have hzloc : ∀ i, loc (f i) (z : M) = 0 :=
        (mem_primaryComponent_iff_localizations_zero t f (z : M)).mp z.2
      refine ⟨m + (z : M), ?_⟩
      apply Prod.ext
      · change η (m + (z : M)) = p.1
        rw [map_add, hzη, add_sub_cancel]
      · funext i
        change loc (f i) (m + (z : M)) = p.2 i
        rw [map_add, hzloc, add_zero, hmloc]
    · rintro ⟨m, rfl⟩
      apply Prod.ext
      · funext i
        simp only [IsLocalizedModule.map_apply, sub_self, Pi.zero_apply, Prod.fst_zero]
      · funext i j
        simp only [IsLocalizedModule.lift_apply, sub_self, Pi.zero_apply, Prod.snd_zero]

end RingTheory
