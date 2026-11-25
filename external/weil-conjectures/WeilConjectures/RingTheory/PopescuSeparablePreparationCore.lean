/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.RingTheory.ImprovePresentation
import WeilConjectures.RingTheory.PopescuPolynomialQuotientSmooth
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.RingTheory.CommonStrictlyStandardPower

@[expose] public section

universe u v w

namespace Algebra

/-- The polynomial construction, before choosing parameters in the receiving ring.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FE, first two paragraphs
(blueprint: lem-weil-pbc-popescu-separable-preparation-core).

Proof: choose finite generators a_j of H_{A/k}, since A is Noetherian. Set
R = k[X_i] and B = A[X_i,Z_ij]/(X_i^n - sum_j Z_ij a_j). This is finitely
presented over R. After inverting a_j, eliminate Z_ij for every i; the resulting
polynomial ring over A_(a_j)[X_i] is smooth over R by smooth base change.
After inverting X_i the a_j generate the unit ideal, so smoothness on that principal
cover proves B_(X_i) smooth (if the generator set is empty the localization is zero).
Apply the improve-presentation lemma to B, obtaining a finite-type B-algebra C with
retraction rho : C -> B whose indicated smooth localizations have free differentials.
Since R is Noetherian, C is finitely presented over R. The strict-standard-power lemma
and finiteness of Fin d give a common positive exponent c. The composite A -> B -> C
is beta. All these objects depend only on A, d, n, not on the receiving ring.
For any alpha and phi satisfying the displayed power membership, write
phi(X_i)^n = sum_j lambda_ij alpha(a_j). Evaluation X_i -> phi(X_i),
Z_ij -> lambda_ij defines B -> Lambda, as it kills the relations. Compose with rho
for gamma. Its composite with beta is alpha and it is an R-algebra map.
Smoothness of C_(beta(a_j)) places beta(a_j) in H_{C/R}. Consequently the extension
of H_{A/k} to C lies in H_{C/R}; mapping to Lambda and taking radicals gives the
Popescu-ideal inequality. The quotient and symmetric-algebra constructions use only
carriers in universe max(u,v), so C has the specified universe. -/
theorem exists_popescu_separable_preparation_core
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [FinitePresentation k A] (d n : ℕ) (hn : 1 ≤ n) :
    ∃ (c : ℕ) (C : Type (max u v)) (_ : CommRing C) (_ : Algebra k C)
      (_ : Algebra (MvPolynomial (Fin d) k) C)
      (_ : IsScalarTower k (MvPolynomial (Fin d) k) C)
      (_ : FinitePresentation (MvPolynomial (Fin d) k) C) (β : A →ₐ[k] C),
      1 ≤ c ∧
      (∀ i : Fin d, IsStrictlyStandardElement (R := MvPolynomial (Fin d) k)
        (algebraMap (MvPolynomial (Fin d) k) C (MvPolynomial.X i ^ c))) ∧
      ∀ {Λ : Type w} [CommRing Λ] [Algebra k Λ]
        (α : A →ₐ[k] Λ) (φ : MvPolynomial (Fin d) k →ₐ[k] Λ),
        letI := φ.toRingHom.toAlgebra
        (∀ i : Fin d, φ (MvPolynomial.X i) ^ n ∈
          Ideal.map α.toRingHom (singularIdeal k A)) →
        ∃ γ : C →ₐ[MvPolynomial (Fin d) k] Λ,
          (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ := by
  classical
  let R := MvPolynomial (Fin d) k
  have : IsNoetherianRing A := FiniteType.isNoetherianRing k A
  obtain ⟨m, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    ((inferInstance : IsNoetherianRing A).noetherian (singularIdeal k A))
  change Ideal.span (Set.range a) = singularIdeal k A at ha
  let B := PopescuPolynomialQuotient d n a
  let f : R →ₐ[k] B := popescuPolynomialBaseMap d n a
  let : Algebra R B := f.toRingHom.toAlgebra
  have : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  obtain ⟨hfpB, hsa, hsx⟩ := popescuPolynomialQuotient_smooth d n hn a ha
  let : FinitePresentation R B := hfpB
  obtain ⟨C, instC, instBC, hft, ρ, hρ, hlocal⟩ :=
    exists_finiteType_retract_smooth_free_differentials R B
  let : CommRing C := instC
  let : Algebra B C := instBC
  let : Algebra R C := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  let : Algebra k C := ((algebraMap B C).comp (algebraMap k B)).toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k B C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k R C := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change algebraMap B C (algebraMap k B x) =
      algebraMap B C (algebraMap R B (algebraMap k R x))
    rw [IsScalarTower.algebraMap_apply k R B]
  let : FiniteType B C := hft
  have : FiniteType R C := FiniteType.trans (inferInstance : FiniteType R B) hft
  have : FinitePresentation R C := FinitePresentation.of_finiteType.mp inferInstance
  let β : A →ₐ[k] C := (IsScalarTower.toAlgHom k B C).comp
    (IsScalarTower.toAlgHom k A B)
  obtain ⟨c, hc, hstrict⟩ := exists_common_strictlyStandard_power R C
    (fun i : Fin d ↦ algebraMap R C (MvPolynomial.X i)) (fun i ↦ by
      have hh := hlocal (algebraMap R B (MvPolynomial.X i)) (hsx i)
      have hx : algebraMap B C (algebraMap R B (MvPolynomial.X i)) =
          algebraMap R C (MvPolynomial.X i) := rfl
      rw [hx] at hh
      exact hh)
  simp only [← map_pow] at hstrict
  refine ⟨c, C, instC, inferInstance, inferInstance, inferInstance, inferInstance,
    β, hc, hstrict, ?_⟩
  intro Λ instΛ instkΛ α φ
  let := φ.toRingHom.toAlgebra
  intro hpow
  have hspan (i : Fin d) : φ (MvPolynomial.X i) ^ n ∈
      Ideal.span (Set.range (fun j ↦ α (a j))) := by
    have hh := hpow i
    rw [← ha, Ideal.map_span] at hh
    have heq : α.toRingHom '' Set.range a = Set.range (fun j ↦ α (a j)) := by
      ext x
      constructor
      · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨a j, ⟨j, rfl⟩, rfl⟩
    rwa [heq] at hh
  choose coeff hcoeff using fun i ↦
    (Submodule.mem_span_range_iff_exists_fun Λ).mp (hspan i)
  let ev : MvPolynomial (Fin d ⊕ (Fin d × Fin m)) A →ₐ[k] Λ :=
    { MvPolynomial.eval₂Hom α.toRingHom
        (Sum.elim (fun i ↦ φ (MvPolynomial.X i)) (fun ij ↦ coeff ij.1 ij.2)) with
      commutes' := fun x ↦ by simp [AlgHom.commutes] }
  let I := Ideal.span (Set.range (popescuPolynomialRelations d n a))
  have hev : ∀ p ∈ I, ev p = 0 := by
    change I ≤ RingHom.ker ev.toRingHom
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change ev (popescuPolynomialRelations d n a i) = 0
    simp only [popescuPolynomialRelations, map_sub, map_pow, map_sum, map_mul]
    simpa [ev, smul_eq_mul] using
      sub_eq_zero.mpr (hcoeff i).symm
  let gk : B →ₐ[k] Λ := Ideal.Quotient.liftₐ I ev hev
  have hg : gk.comp f = φ := by
    ext i
    change gk (f (MvPolynomial.X i)) = φ (MvPolynomial.X i)
    have hx : f (MvPolynomial.X i) = Ideal.Quotient.mk I (MvPolynomial.X (Sum.inl i)) :=
      MvPolynomial.aeval_X _ _
    rw [hx]
    change ev (MvPolynomial.X (Sum.inl i)) = φ (MvPolynomial.X i)
    simp [ev]
  let g : B →ₐ[R] Λ :=
    { gk with
      commutes' := fun r ↦ by
        change gk (f r) = φ r
        exact DFunLike.congr_fun hg r }
  let ρR : C →ₐ[R] B :=
    { ρ.toRingHom with
      commutes' := fun r ↦ by
        change ρ (algebraMap B C (algebraMap R B r)) = algebraMap R B r
        exact ρ.commutes _ }
  let γ : C →ₐ[R] Λ := g.comp ρR
  have hcomp : (γ.restrictScalars k).comp β = α := by
    ext x
    change gk (ρ (algebraMap B C (algebraMap A B x))) = α x
    rw [ρ.commutes]
    change ev (MvPolynomial.C x) = α x
    simp [ev]
  refine ⟨γ, hcomp, ?_⟩
  have hsing : Ideal.map β.toRingHom (singularIdeal k A) ≤ singularIdeal R C := by
    rw [← ha, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro x ⟨y, ⟨j, rfl⟩, rfl⟩
    apply Ideal.le_radical
    apply Ideal.subset_span
    change Smooth R (Localization.Away (β (a j)))
    exact (hlocal (algebraMap A B (a j)) (hsa j)).1
  apply Ideal.radical_mono
  have hh := Ideal.map_mono (f := γ.toRingHom) hsing
  rw [Ideal.map_map] at hh
  have hm : γ.toRingHom.comp β.toRingHom = α.toRingHom :=
    congrArg AlgHom.toRingHom hcomp
  rw [hm] at hh
  exact hh

end Algebra
