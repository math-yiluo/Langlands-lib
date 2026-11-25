/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.EtaleSectionIdempotentSplitting
import WeilConjectures.RingTheory.EtaleSectionLiftingOfGabberRoots
import WeilConjectures.RingTheory.IdempotentsDeterminedModuloRadical

/-!
# Unique maps from étale henselization stages

Source: Stacks Project, Tag 0A02, final paragraph, with Tags 09XI and 09XF
(blueprint: lem-weil-pbc-henselization-stage-map).
-/

@[expose] public section

universe u

namespace RingTheory

open Polynomial in
open scoped BigOperators in
/-- For a Gabber polynomial, `1` is a simple root modulo `I`; use the root-lifting
field of `HenselianRing` directly. This avoids the factorization criterion. -/
private theorem gabber_roots_of_henselian
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    (n : ℕ) (_hn : 1 ≤ n) (a : Fin (n + 1) → A) (ha : ∀ j, a j ∈ I)
    (f : A[X]) (hf : f.Monic)
    (heq : f = X ^ n * (X - 1) + ∑ j : Fin (n + 1), C (a j) * X ^ (j : ℕ)) :
    ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α := by
  have hmap : f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) := by
    rw [heq]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_sum,
      Polynomial.map_C]
    have hz : ∀ j, Ideal.Quotient.mk I (a j) = 0 := fun j ↦
      Ideal.Quotient.eq_zero_iff_mem.mpr (ha j)
    simp [hz]
  have hval : f.eval 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← Polynomial.eval_map_apply]
    simp [hmap]
  have hder : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hmap]
    simp [Polynomial.derivative_mul]
  obtain ⟨α, hα, hαI⟩ := HenselianRing.is_henselian f hf 1 hval hder
  exact ⟨α, hαI, hα⟩

open scoped TensorProduct in
/-- Split the diagonal multiplication section by an idempotent. A pair of sections
agreeing modulo `I` sends that idempotent to `1`, so kills the diagonal kernel. -/
private theorem etale_sections_eq_of_mod
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (D : Type u) [CommRing D] [Algebra A D] [Algebra.Etale A D]
    (s t : D →ₐ[A] A)
    (hst : (Ideal.Quotient.mkₐ A I).comp s = (Ideal.Quotient.mkₐ A I).comp t) :
    s = t := by
  let μ : D ⊗[A] D →ₐ[D] D := Algebra.TensorProduct.lmul'' A
  obtain ⟨e, he, hμe, hker, _⟩ :=
    Algebra.Etale.exists_idempotent_splitting_of_algHom μ
  let p : D ⊗[A] D →ₐ[A] A := Algebra.TensorProduct.productMap s t
  have hpmod : (Ideal.Quotient.mkₐ A I).comp p =
      ((Ideal.Quotient.mkₐ A I).comp s).comp (Algebra.TensorProduct.lmul' A) := by
    apply Algebra.TensorProduct.ext
    · ext x
      simp [p]
    · ext x
      simpa [p] using (AlgHom.congr_fun hst x).symm
  have hpe : p e = 1 := by
    apply IsIdempotentElem.eq_of_sub_mem_of_le_jacobson I hI (he.map p) IsIdempotentElem.one
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, sub_eq_zero]
    have := AlgHom.congr_fun hpmod e
    change (Algebra.TensorProduct.lmul' A) e = 1 at hμe
    simpa [hμe] using this
  have hkill : RingHom.ker μ.toRingHom ≤ RingHom.ker p.toRingHom := by
    rw [hker]
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change p (1 - e) = 0
    simp [hpe]
  apply AlgHom.ext
  intro x
  have hx : x ⊗ₜ[A] (1 : D) - (1 : D) ⊗ₜ[A] x ∈ RingHom.ker μ.toRingHom := by
    change μ _ = 0
    simp [μ, Algebra.TensorProduct.lmul'']
  have hp := hkill hx
  change p (x ⊗ₜ[A] (1 : D) - (1 : D) ⊗ₜ[A] x) = 0 at hp
  simpa [p, sub_eq_zero] using hp

/-- A single étale algebra trivial modulo J admits exactly one map to a henselian pair
extending a morphism of pairs.
Source: Stacks Project, Tag 0A02, final paragraph, using Tags 09XI, 02FL, and 09XF.
(blueprint: lem-weil-pbc-henselization-stage-map)

Proof: Give A its B-algebra structure through φ and C its structure through f. The
isomorphism B/J ≃ C/JC and the induced map B/J → A/I give a B-algebra map C → A/I.
Tensor-product universality extends this to a section modulo I of D = A ⊗[B] C,
which is étale over A. For each Gabber polynomial, its reduction is X^n(X-1), whose
value at 1 is zero and whose derivative at 1 is 1. Apply the root-lifting property of
HenselianRing directly. Together with its Jacobson-radical field, this supplies the
hypotheses of section lifting, giving an A-algebra section D → A. Restrict to C.
For uniqueness, every extension induces an A-algebra section of D. Its reduction
factors through C/JC and must equal the constructed reduced map, since B/J → C/JC
is surjective. Split the multiplication section D ⊗[A] D → D by an idempotent e.
The section-pair map sends e to an idempotent congruent to 1 modulo I; idempotents
are determined modulo I, so its value is 1. The pair map kills the multiplication
kernel, generated by 1-e, including x ⊗ 1 - 1 ⊗ x. Hence the sections, and their
restrictions to C, agree. All constructions also apply to zero rings. -/
theorem existsUnique_henselization_stage_map
    (B : Type u) [CommRing B] (J : Ideal B)
    (C : Type u) [CommRing C] (f : B →+* C)
    (hf : AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)))
    (hquot : Function.Bijective
      (Ideal.quotientMap (J.map f) f (Ideal.le_comap_map)))
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    (φ : B →+* A) (hφ : J.map φ ≤ I) :
    ∃! τ : C →+* A, τ.comp f = φ := by
  classical
  let : Algebra B C := f.toAlgebra
  let : Algebra B A := φ.toAlgebra
  have hf' : RingHom.Etale f :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)
      (φ := CommRingCat.ofHom f)).mp hf
  let : Algebra.Etale B C := (RingHom.etale_algebraMap).mp hf'
  let q : B ⧸ J →+* C ⧸ J.map f :=
    Ideal.quotientMap (J.map f) f Ideal.le_comap_map
  let e : B ⧸ J ≃+* C ⧸ J.map f := RingEquiv.ofBijective q hquot
  have hφJ : J ≤ RingHom.ker ((Ideal.Quotient.mk I).comp φ) := by
    intro x hx
    change Ideal.Quotient.mk I (φ x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hφ (Ideal.mem_map_of_mem φ hx))
  let ψ : B ⧸ J →+* A ⧸ I := Ideal.Quotient.lift J
    ((Ideal.Quotient.mk I).comp φ) hφJ
  let σring : C →+* A ⧸ I :=
    (ψ.comp e.symm.toRingHom).comp (Ideal.Quotient.mk (J.map f))
  have hσ : σring.comp f = (Ideal.Quotient.mk I).comp φ := by
    ext x
    change ψ (e.symm (q (Ideal.Quotient.mk J x))) = _
    rw [show q (Ideal.Quotient.mk J x) = e (Ideal.Quotient.mk J x) from rfl,
      e.symm_apply_apply]
    rfl
  let σ : C →ₐ[B] A ⧸ I :=
    { σring with commutes' := fun x ↦ RingHom.congr_fun hσ x }
  let D := TensorProduct B A C
  let σD : D →ₐ[A] A ⧸ I := AlgHom.liftEquiv B A C (A ⧸ I) σ
  obtain ⟨s, hs⟩ := Algebra.exists_etale_section_lift_of_gabber_roots
    A I HenselianRing.jac (gabber_roots_of_henselian A I) D σD
  let τalg : C →ₐ[B] A := (AlgHom.liftEquiv B A C A).symm s
  refine ⟨τalg.toRingHom, ?_, ?_⟩
  · ext x
    exact τalg.commutes x
  · intro τ hτ
    have hτapply : ∀ x, τ (f x) = φ x := fun x ↦ RingHom.congr_fun hτ x
    let talg : C →ₐ[B] A := { τ with commutes' := fun x ↦ RingHom.congr_fun hτ x }
    let t : D →ₐ[A] A := AlgHom.liftEquiv B A C A talg
    have hτJ : J.map f ≤ RingHom.ker ((Ideal.Quotient.mk I).comp τ) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change Ideal.Quotient.mk I (τ (f x)) = 0
      rw [hτapply x]
      exact hφJ hx
    let τquot : C ⧸ J.map f →+* A ⧸ I := Ideal.Quotient.lift (J.map f)
      ((Ideal.Quotient.mk I).comp τ) hτJ
    have hτq : τquot.comp q = ψ := by
      apply RingHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk I (τ (f x)) = Ideal.Quotient.mk I (φ x)
      rw [hτapply x]
    have hτquot : τquot = ψ.comp e.symm.toRingHom := by
      apply RingHom.ext
      intro x
      obtain ⟨y, rfl⟩ := hquot.2 x
      change τquot (q y) = ψ (e.symm (e y))
      rw [e.symm_apply_apply]
      exact RingHom.congr_fun hτq y
    have hτmod : (Ideal.Quotient.mk I).comp τ = σring := by
      change (Ideal.Quotient.mk I).comp τ =
        (ψ.comp e.symm.toRingHom).comp (Ideal.Quotient.mk (J.map f))
      rw [← hτquot]
      rfl
    have ht : (Ideal.Quotient.mkₐ A I).comp t = σD := by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · ext x
        simpa [t, σD, τalg, talg, σ] using RingHom.congr_fun hτmod x
    have hts : t = s := etale_sections_eq_of_mod A I HenselianRing.jac D t s
      (ht.trans hs.symm)
    have htal : talg = τalg := (AlgHom.liftEquiv B A C A).injective (by
      simpa [t, τalg] using hts)
    exact congrArg AlgHom.toRingHom htal

end RingTheory
