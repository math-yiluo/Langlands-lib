/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.Mathlib.Algebra.Algebra.Hom
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Étale algebras over a normal domain with separably closed fraction field

Let `A` be an integrally closed domain whose fraction field `K` is separably closed, and let `B`
be an étale `A`-algebra. Then every point of `Spec B` lies on a section of `Spec B → Spec A`
defined over a basic open of `Spec A`: for every prime `q` of `B` there are `a : A` and an
`A`-algebra map `ψ : B →ₐ[A] A[1/a]` such that `q` is the pullback along `ψ` of a prime of
`A[1/a]`.

The proof combines Zariski's main theorem with the structure of étale algebras over the
separably closed field `K`. By Zariski's main theorem
(`Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`) there is a
module-finite subalgebra `S'` of `B` and `r ∈ S'`, `r ∉ q`, with `S'[1/r] = B[1/r]`. Since `B`
is flat over `A`, it embeds into `K ⊗[A] B`, which is a finite product of copies of `K`; so the
`A`-algebra maps `φ : B →ₐ[A] K` are jointly injective, and as `q` is prime and there are
finitely many of them, `q` contains the kernel of one of them. This `φ` maps the integral
`A`-algebra `S'` into the integral closure `A` of `A` in `K`, hence `B` into `A[1/φ(r)]`.

Specialising to a local ring gives that an integrally closed local domain with separably
closed fraction field is strictly henselian.

## Main results

- `Algebra.Etale.exists_algHom_localizationAway_comap_eq`: the section statement above.
- `Algebra.Etale.exists_algHom_comap_maximalIdeal_eq`: over an integrally closed local domain
  with separably closed fraction field, every prime of an étale algebra over the closed point
  is the pullback of the maximal ideal along an `A`-algebra map `B →ₐ[A] A`.
- `HenselianLocalRing.of_isSepClosed_fractionRing`,
  `IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing`: such a local ring is
  henselian with separably closed residue field, i.e. it is strictly henselian.
-/

@[expose] public section

open Polynomial

open scoped TensorProduct

namespace Algebra.Etale

variable {A B : Type*} [CommRing A] [IsIntegrallyClosed A] [CommRing B]
  [Algebra A B] [Algebra.Etale A B]

omit [IsIntegrallyClosed A] in
/-- If `B` is étale over a domain `A` whose fraction field `K` is separably closed, then every
prime `q` of `B` contains the kernel of some `A`-algebra map `B →ₐ[A] K`. Indeed, these maps
are the factors of the injection `B → K ⊗[A] B ≃ K ^ n`, so a product of elements outside `q`
would vanish. -/
lemma exists_algHom_ker_le (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] [IsSepClosed K] (q : Ideal B) [q.IsPrime] :
    ∃ φ : B →ₐ[A] K, RingHom.ker φ ≤ q := by
  classical
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[A] B)
  have := Algebra.FormallyUnramified.finite_of_free K (K ⊗[A] B)
  have : IsArtinianRing (K ⊗[A] B) := isArtinian_of_tower K inferInstance
  have := Fintype.ofFinite (PrimeSpectrum (K ⊗[A] B))
  let φ (i : PrimeSpectrum (K ⊗[A] B)) : B →ₐ[A] K :=
    ((Pi.evalAlgHom K _ i).comp e.toAlgHom).restrictScalars A |>.comp
      Algebra.TensorProduct.includeRight
  have hinj : Function.Injective
      (e.toAlgHom.restrictScalars A |>.comp (Algebra.TensorProduct.includeRight (R := A) (A := K)
        (B := B))) :=
    e.injective.comp (Algebra.TensorProduct.includeRight_injective
      (IsFractionRing.injective A K))
  by_contra! h
  choose x hx hxq using fun i ↦ Set.not_subset.mp (h (φ i))
  have hprod : ∏ i, x i ∈ q := by
    rw [(hinj.eq_iff' (a := ∏ i, x i) (map_zero _)).mp ?_]
    · exact q.zero_mem
    funext i
    have := map_prod (φ i) x Finset.univ
    rw [Finset.prod_eq_zero (f := fun j ↦ φ i (x j)) (Finset.mem_univ i)
      (RingHom.mem_ker.mp (hx i))] at this
    exact this
  obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
  exact hxq i hi

set_option backward.isDefEq.respectTransparency false in
/-- **Points of an étale algebra over a normal domain with separably closed fraction field lie
on sections.** Let `A` be an integrally closed domain with separably closed fraction field `K`
and `B` an étale `A`-algebra. Then for every prime `q` of `B` there are `a : A` and an
`A`-algebra map `ψ : B →ₐ[A] A[1/a]` such that `q` is the preimage of a prime of `A[1/a]`
under `ψ`. This is the algebraic heart of Stacks Project, Lemma 59.80.4 (Tag 09Z9). -/
theorem exists_algHom_localizationAway_comap_eq (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] [IsSepClosed K] (q : Ideal B) [q.IsPrime] :
    ∃ (a : A) (ψ : B →ₐ[A] Localization.Away a) (P : Ideal (Localization.Away a)),
      P.IsPrime ∧ P.comap ψ = q := by
  obtain ⟨S', hS', r, hrq, hr⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := A) q
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_le (A := A) K q
  have : Module.Finite A S' := Module.Finite.iff_fg.mpr hS'
  obtain ⟨θ, hθ⟩ := AlgHom.exists_algebraMap_comp_eq_of_forall_mem_range
    (IsFractionRing.injective A K) (φ.comp S'.val) fun s ↦ IsIntegrallyClosed.isIntegral_iff.mp
      ((Algebra.IsIntegral.isIntegral s).map (φ.comp S'.val))
  have hθker : RingHom.ker θ ≤ q.comap S'.val := fun s hs ↦ hφ <| by
    rw [RingHom.mem_ker] at hs ⊢
    simpa [hs] using (hθ s).symm
  have hθsurj : Function.Surjective θ := fun x ↦ ⟨algebraMap A S' x, θ.commutes x⟩
  let e : Localization.Away r ≃ₐ[A] Localization.Away r.1 :=
    AlgEquiv.ofBijective (Localization.awayMapₐ S'.val r) hr
  have he (s : S') : e (algebraMap S' _ s) = algebraMap B (Localization.Away r.1) s := by
    simp [e, Localization.awayMapₐ, IsLocalization.Away.map, Subalgebra.val]
  set ψ : B →ₐ[A] Localization.Away (θ r) := (Localization.awayMapₐ θ r).comp
    (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom A B (Localization.Away r.1)))
  have hψ (s : S') : ψ s = algebraMap A _ (θ s) := by
    simp only [ψ, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_toAlgHom]
    rw [← he, e.symm_apply_apply]
    simp [Localization.awayMapₐ, IsLocalization.Away.map]
  have hmem (b : B) : ∃ m, r.1 ^ m * b ∈ S' := by
    obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj r (e.symm (algebraMap B _ b))
    have := congrArg e hx
    rw [map_mul, map_pow, he, he, e.apply_symm_apply, ← map_pow, ← map_mul] at this
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq r.1 this
    refine ⟨k + n, ?_⟩
    rw [pow_add, mul_assoc, mul_comm _ b, hk]
    exact S'.mul_mem (S'.pow_mem r.2 _) x.2
  set P0 := (q.comap S'.val).map θ with hP0_def
  have hP0 : P0.IsPrime := Ideal.map_isPrime_of_surjective hθsurj hθker
  have hθP0 (s : S') : θ s ∈ P0 ↔ s.1 ∈ q := by
    rw [← Ideal.mem_comap, hP0_def, Ideal.comap_map_of_surjective _ hθsurj,
      sup_eq_left.mpr (by rwa [← RingHom.ker_eq_comap_bot]), Ideal.mem_comap]
    rfl
  have hdisj : Disjoint (Submonoid.powers (θ r) : Set A) P0 := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨n, rfl⟩ h
    exact hrq ((hθP0 r).mp (hP0.mem_of_pow_mem n h))
  have hPprime := IsLocalization.isPrime_of_isPrime_disjoint (.powers (θ r))
    (Localization.Away (θ r)) P0 hP0 hdisj
  have hPcomap := IsLocalization.under_map_of_isPrime_disjoint (.powers (θ r))
    (Localization.Away (θ r)) hP0 hdisj
  set P := P0.map (algebraMap A (Localization.Away (θ r)))
  have hψP (s : S') : ψ s ∈ P ↔ s.1 ∈ q := by
    rw [hψ, ← Ideal.mem_comap, ← Ideal.under_def, hPcomap, hθP0]
  have hrP : ψ r.1 ∉ P := (hψP r).not.mpr hrq
  refine ⟨θ r, ψ, P, hPprime, Ideal.ext fun b ↦ ?_⟩
  obtain ⟨m, hm⟩ := hmem b
  have := hψP ⟨_, hm⟩
  rw [map_mul, map_pow, Ideal.IsPrime.mul_mem_left_iff (mt (hPprime.mem_of_pow_mem m) hrP)] at this
  rw [Ideal.mem_comap, this]
  exact Ideal.IsPrime.mul_mem_left_iff (mt (Ideal.IsPrime.mem_of_pow_mem inferInstance m) hrq)

/-- Over an integrally closed local domain `A` with separably closed fraction field, every prime
`q` of an étale `A`-algebra `B` lying over the maximal ideal is the preimage of the maximal ideal
under an `A`-algebra map `B →ₐ[A] A`. -/
theorem exists_algHom_comap_maximalIdeal_eq [IsLocalRing A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] [IsSepClosed K] (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    ∃ ψ : B →ₐ[A] A, (IsLocalRing.maximalIdeal A).comap ψ = q := by
  obtain ⟨a, ψ, P, hP, hPq⟩ := exists_algHom_localizationAway_comap_eq (A := A) K q
  have hPA : P.comap (algebraMap A (Localization.Away a)) = IsLocalRing.maximalIdeal A := by
    rw [← hq, ← hPq]
    ext x
    simp
  have ha : IsUnit a := by
    by_contra h
    have : algebraMap A _ a ∈ P := by
      rw [← Ideal.mem_comap, hPA]
      exact (IsLocalRing.mem_maximalIdeal _).mpr h
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ this (IsLocalization.Away.algebraMap_isUnit a))
  let e := IsLocalization.atUnits A (Submonoid.powers a) (S := Localization.Away a)
    (by
      rintro _ ⟨n, rfl⟩
      exact ha.pow n)
  refine ⟨e.symm.toAlgHom.comp ψ, Ideal.ext fun b ↦ ?_⟩
  rw [← hPq, Ideal.mem_comap, Ideal.mem_comap, ← hPA, Ideal.mem_comap, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, ← e.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    e.apply_symm_apply]

end Algebra.Etale

variable {A : Type*} [CommRing A] [IsIntegrallyClosed A] [IsLocalRing A]

/-- An integrally closed local domain with separably closed fraction field is henselian. -/
theorem HenselianLocalRing.of_isSepClosed_fractionRing (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] [IsSepClosed K] : HenselianLocalRing A :=
  .of_exists_algHom_comap_maximalIdeal_eq fun _ _ _ _ q _ hq ↦
    Algebra.Etale.exists_algHom_comap_maximalIdeal_eq K q hq

/-- An integrally closed local domain with separably closed fraction field has separably closed
residue field. -/
theorem IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing (K : Type*) [Field K]
    [Algebra A K] [IsFractionRing A K] [IsSepClosed K] :
    IsSepClosed (IsLocalRing.ResidueField A) :=
  isSepClosed_residueField_of_exists_algHom_comap_maximalIdeal_eq fun _ _ _ _ q _ hq ↦
    Algebra.Etale.exists_algHom_comap_maximalIdeal_eq K q hq
