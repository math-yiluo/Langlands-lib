/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.IdempotentsDeterminedModuloRadical
import WeilConjectures.RingTheory.LiftIdempotentUpstairs
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Henselian pairs from lifting sections of étale algebras

Source: Stacks Project, More on Algebra, Lemma Tag 09XI, (2) ⇒ (4) ⇒ (3)
(blueprint: lem-weil-pbc-etale-section-lifting-henselian-pair).
-/

@[expose] public section

universe u v

/-! Proof plan is recorded on the blueprint node. -/

private theorem lift_small_etale_section
    (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      (σ : A' →ₐ[A] A ⧸ I), ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.Etale A C]
    (σ : C →ₐ[A] A ⧸ I) : ∃ τ : C →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ := by
  let E : ULift.{v} C ≃ₐ[A] C := ULift.algEquiv
  let : Algebra.Etale A (ULift.{v} C) := Algebra.Etale.of_equiv E.symm
  obtain ⟨τ, hτ⟩ := h (ULift.{v} C) (σ.comp E.toAlgHom)
  refine ⟨τ.comp E.symm.toAlgHom, ?_⟩
  ext x
  have hx := DFunLike.congr_fun hτ (E.symm x)
  simpa using hx

/-- The radical and root-lifting part of Stacks Tag 09XI.
Source: Stacks Project, More on Algebra, Lemma Tag 09XI, (2) ⇒ (4) ⇒ (3)
(blueprint: lem-weil-pbc-etale-section-lifting-radical-and-henselian).

Proof: apply the open-localization argument for the Jacobson radical, then the
finite-algebra idempotent descent through the étale neighbourhood and the section
supplied by the hypothesis; uniqueness follows from congruence modulo the radical. -/
theorem etale_section_lifting_radical_and_henselian (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      (σ : A' →ₐ[A] A ⧸ I), ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ) :
    I ≤ Ideal.jacobson ⊥ ∧ HenselianRing A I := by
  have hJ : I ≤ Ideal.jacobson ⊥ := by
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    let f := x * y + 1
    have hf : IsUnit ((Ideal.Quotient.mkₐ A I) f) := by
      simp [f, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    let σ : Localization.Away f →ₐ[A] A ⧸ I :=
      IsLocalization.Away.liftAlgHom f hf
    obtain ⟨τ, -⟩ := lift_small_etale_section A I h (Localization.Away f) σ
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).map τ
  refine ⟨hJ, ⟨hJ, ?_⟩⟩
  -- Simple roots give maps out of the standard étale algebra A[X, 1/f']/f.
  intro f hf a₀ ha₀ hder
  let P : StandardEtalePair A :=
    ⟨f, hf, f.derivative, 1, 0, 1, by simp⟩
  have hm : P.HasMap (Ideal.Quotient.mk I a₀) := by
    constructor
    · simpa [P, Polynomial.aeval_def, ← Polynomial.eval₂_at_apply] using
        Ideal.Quotient.eq_zero_iff_mem.mpr ha₀
    · simpa [P, Polynomial.aeval_def, ← Polynomial.eval₂_at_apply] using hder
  obtain ⟨τ, hτ⟩ := lift_small_etale_section A I h P.Ring (P.lift _ hm)
  refine ⟨τ P.X, ?_, ?_⟩
  · have hr := P.hasMap_X.map τ
    simpa [P, Polynomial.aeval_def] using hr.1
  · apply Ideal.Quotient.eq.mp
    have he := DFunLike.congr_fun hτ P.X
    simpa using he

/-- The finite-algebra idempotent-lifting part
(blueprint: lem-weil-pbc-etale-section-lifting-idempotents) of Stacks Tag 09XI.
Source: Stacks Project, More on Algebra, Lemma Tag 09XI, (4) ⇒ (3).

Proof: apply the étale idempotent lifting construction and descend along the
section supplied by the hypothesis; uniqueness follows from congruence modulo
the radical. -/
theorem etale_section_lifting_idempotents (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      (σ : A' →ₐ[A] A ⧸ I), ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ) :
    ∀ (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
      (e₀ : B ⧸ I.map (algebraMap A B)), IsIdempotentElem e₀ → ∃! e : B,
        IsIdempotentElem e ∧ Ideal.Quotient.mk (I.map (algebraMap A B)) e = e₀ := by
  intro B _ _ _ e₀ he₀
  have hJ := (etale_section_lifting_radical_and_henselian A I h).1
  have hJB : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.jacobson, le_sInf_iff]
    rintro M ⟨-, hM⟩
    let : M.IsMaximal := hM
    have hcom : (M.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) M
    apply Ideal.map_le_iff_le_comap.mpr
    exact hJ.trans (sInf_le ⟨bot_le, hcom⟩)
  obtain ⟨C, g, hg⟩ := AlgebraicGeometry.exists_etale_lift_isIdempotentElem I e₀ he₀
  let : Algebra A C := g.hom.toAlgebra
  obtain ⟨hEt, α, hα, e', he', β, hβ, hemod⟩ := hg
  have : Algebra.Etale A C := RingHom.etale_algebraMap.mp
    ((AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale)).mp hEt)
  let αA : (A ⧸ I) ≃ₐ[A] (C ⧸ I.map (algebraMap A C)) :=
    { α with commutes' := hα }
  let σ := αA.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A (I.map (algebraMap A C)))
  obtain ⟨τ, -⟩ := lift_small_etale_section A I h C σ
  let φ : TensorProduct A B C →ₐ[A] B :=
    Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp τ)
      (fun _ _ ↦ Commute.all _ _)
  have hφ : I.map (algebraMap A (TensorProduct A B C)) ≤
      (I.map (algebraMap A B)).comap φ.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change φ (algebraMap A (TensorProduct A B C) a) ∈ I.map (algebraMap A B)
    rw [φ.commutes]
    exact Ideal.mem_map_of_mem _ ha
  let δ := Ideal.quotientMap (I.map (algebraMap A B)) φ.toRingHom hφ
  have hδβ : ∀ z, δ (β z) = z := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hβ]
    change Ideal.Quotient.mk _ (φ (b ⊗ₜ[A] (1 : C))) = _
    simp [φ, Algebra.TensorProduct.lift_tmul]
  have hlift : Ideal.Quotient.mk (I.map (algebraMap A B)) (φ e') = e₀ := by
    have heq := congrArg δ hemod
    change δ (β e₀) = Ideal.Quotient.mk _ (φ e') at heq
    rw [hδβ] at heq
    exact heq.symm
  refine ⟨φ e', ⟨he'.map φ, hlift⟩, ?_⟩
  intro e he
  apply IsIdempotentElem.eq_of_sub_mem_of_le_jacobson
    (I.map (algebraMap A B)) hJB he.1 (he'.map φ)
  exact Ideal.Quotient.eq.mp (he.2.trans hlift.symm)

/-- (blueprint: lem-weil-pbc-etale-section-lifting-henselian-pair) -/
theorem henselianRing_of_etale_section_lifting (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      (σ : A' →ₐ[A] A ⧸ I), ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ) :
    I ≤ Ideal.jacobson ⊥ ∧ HenselianRing A I ∧
      ∀ (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
        (e₀ : B ⧸ I.map (algebraMap A B)), IsIdempotentElem e₀ →
          ∃! e : B, IsIdempotentElem e ∧
    Ideal.Quotient.mk (I.map (algebraMap A B)) e = e₀ := by
  obtain ⟨hJ, hH⟩ := etale_section_lifting_radical_and_henselian A I h
  obtain hE := etale_section_lifting_idempotents A I h
  exact ⟨hJ, hH, hE⟩

